//go:build windows

package main

import (
	"context"
	crand "crypto/rand"
	_ "embed"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math/rand/v2"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
	"unicode/utf16"
	"unicode/utf8"
	"unsafe"
)

const (
	appName = "MacroLoom"
	version = "0.9.0"
	port    = 47811
)

//go:embed ui.html
var uiHTML string

var (
	u32  = syscall.NewLazyDLL("user32.dll")
	k32  = syscall.NewLazyDLL("kernel32.dll")
	sh32 = syscall.NewLazyDLL("shell32.dll")

	pSetWindowsHookEx    = u32.NewProc("SetWindowsHookExW")
	pCallNextHookEx      = u32.NewProc("CallNextHookEx")
	pGetMessage          = u32.NewProc("GetMessageW")
	pTranslateMessage    = u32.NewProc("TranslateMessage")
	pDispatchMessage     = u32.NewProc("DispatchMessageW")
	pSendInput           = u32.NewProc("SendInput")
	pMapVirtualKey       = u32.NewProc("MapVirtualKeyW")
	pGetForegroundWindow = u32.NewProc("GetForegroundWindow")
	pGetWindowText       = u32.NewProc("GetWindowTextW")
	pGetWindowThreadPID  = u32.NewProc("GetWindowThreadProcessId")
	pGetAsyncKeyState    = u32.NewProc("GetAsyncKeyState")
	pGetCursorPos        = u32.NewProc("GetCursorPos")
	pSetCursorPos        = u32.NewProc("SetCursorPos")
	pClientToScreen      = u32.NewProc("ClientToScreen")
	pScreenToClient      = u32.NewProc("ScreenToClient")
	pRegisterClassEx     = u32.NewProc("RegisterClassExW")
	pCreateWindowEx      = u32.NewProc("CreateWindowExW")
	pDefWindowProc       = u32.NewProc("DefWindowProcW")
	pLoadIcon            = u32.NewProc("LoadIconW")
	pCreatePopupMenu     = u32.NewProc("CreatePopupMenu")
	pAppendMenu          = u32.NewProc("AppendMenuW")
	pTrackPopupMenu      = u32.NewProc("TrackPopupMenu")
	pDestroyMenu         = u32.NewProc("DestroyMenu")
	pSetForegroundWindow = u32.NewProc("SetForegroundWindow")
	pMessageBox          = u32.NewProc("MessageBoxW")
	pSetDpiCtx           = u32.NewProc("SetProcessDpiAwarenessContext")

	pPostMessage     = u32.NewProc("PostMessageW")
	pVkKeyScan       = u32.NewProc("VkKeyScanW")
	pGetDC           = u32.NewProc("GetDC")
	pReleaseDC       = u32.NewProc("ReleaseDC")
	pGetPixel        = syscall.NewLazyDLL("gdi32.dll").NewProc("GetPixel")
	pMultiByteToWide = k32.NewProc("MultiByteToWideChar")
	pGetModuleHandle = k32.NewProc("GetModuleHandleW")
	pOpenProcess     = k32.NewProc("OpenProcess")
	pCloseHandle     = k32.NewProc("CloseHandle")
	pQueryImageName  = k32.NewProc("QueryFullProcessImageNameW")
	pShellNotifyIcon = sh32.NewProc("Shell_NotifyIconW")
	pShellExecute    = sh32.NewProc("ShellExecuteW")
)

// ---------- shared state ----------

var (
	cfgMu   sync.RWMutex
	cfg     *Config
	cfgPath string
	token   string

	active   atomic.Pointer[activeSet]
	paused   atomic.Bool
	physMods atomic.Uint32 // bit per modifier key, see modKeys
	pauseID  atomic.Uint32

	fgMu      sync.Mutex
	fgHwnd    uintptr
	fgExe     string
	fgTitle   string
	activeIDs []string

	eng  = &engine{running: map[string]*runState{}, fired: map[string]int64{}}
	held = map[uint32]*Macro{} // hook thread only

	trayHwnd uintptr
)

// physical modifier keys, index = bit in physMods
var modKeys = []keyDef{
	{vk: 0xA2, scan: 0x1D},            // LCtrl
	{vk: 0xA3, scan: 0x1D, ext: true}, // RCtrl
	{vk: 0xA0, scan: 0x2A},            // LShift
	{vk: 0xA1, scan: 0x36},            // RShift
	{vk: 0xA4, scan: 0x38},            // LAlt
	{vk: 0xA5, scan: 0x38, ext: true}, // RAlt
}

func modIndex(vk uint32) int {
	switch vk {
	case 0xA2, 0x11:
		return 0
	case 0xA3:
		return 1
	case 0xA0, 0x10:
		return 2
	case 0xA1:
		return 3
	case 0xA4, 0x12:
		return 4
	case 0xA5:
		return 5
	}
	return -1
}

func trigMods(bits uint32) uint32 {
	var m uint32
	if bits&0x03 != 0 {
		m |= modCtrl
	}
	if bits&0x0C != 0 {
		m |= modShift
	}
	if bits&0x30 != 0 {
		m |= modAlt
	}
	return m
}

// ---------- input injection ----------

type keyInput struct {
	typ   uint32
	_     uint32
	vk    uint16
	scan  uint16
	flags uint32
	time  uint32
	_     uint32
	extra uintptr
	_     [8]byte
}

type mouseInput struct {
	typ       uint32
	_         uint32
	dx, dy    int32
	mouseData uint32
	flags     uint32
	time      uint32
	_         uint32
	extra     uintptr
}

func sendKey(d keyDef, up bool) {
	// vk + scan together (what AutoHotkey does); scan-only if the vk is unknown
	in := keyInput{typ: 1, vk: d.vk, scan: d.scan}
	if d.vk == 0 {
		in.flags = 0x0008 // KEYEVENTF_SCANCODE
	}
	if d.ext {
		in.flags |= 0x0001
	}
	if up {
		in.flags |= 0x0002
	}
	countSend(pSendInput.Call(1, uintptr(unsafe.Pointer(&in)), unsafe.Sizeof(in)))
}

// postKey delivers a key straight to the foreground window's message queue.
func postKey(d keyDef, up bool) {
	hwnd, _, _ := pGetForegroundWindow.Call()
	msg, lp := uintptr(0x100), uintptr(1)|uintptr(d.scan)<<16
	if d.ext {
		lp |= 1 << 24
	}
	if up {
		msg, lp = 0x101, lp|0xC0000000
	}
	countSend(pPostMessage.Call(hwnd, msg, uintptr(d.vk), lp))
}

func keyOut(mode string, d keyDef, up bool) {
	if mode == "post" {
		postKey(d, up)
		if !up && d.vk == 0x0D {
			hwnd, _, _ := pGetForegroundWindow.Call()
			countSend(pPostMessage.Call(hwnd, 0x102, 13, 1))
		}
		return
	}
	sendKey(d, up)
}

// typeUnit types one UTF-16 unit using the profile's send mode.
func typeUnit(mode string, u uint16) {
	switch mode {
	case "post":
		hwnd, _, _ := pGetForegroundWindow.Call()
		countSend(pPostMessage.Call(hwnd, 0x102, uintptr(u), 1)) // WM_CHAR
		return
	case "unicode":
		sendUnicode(u)
		return
	}
	r, _, _ := pVkKeyScan.Call(uintptr(u))
	v := uint16(r)
	if v == 0xFFFF || (v>>8)&^7 != 0 || v&0xFF == 0 {
		sendUnicode(u) // not on the keyboard layout
		return
	}
	sc, _, _ := pMapVirtualKey.Call(uintptr(v&0xFF), 0)
	d := keyDef{vk: v & 0xFF, scan: uint16(sc)}
	var mods uint32
	if v>>8&1 != 0 {
		mods |= modShift
	}
	if v>>8&2 != 0 {
		mods |= modCtrl
	}
	if v>>8&4 != 0 {
		mods |= modAlt
	}
	for _, md := range modDefs {
		if mods&md.bit != 0 {
			sendKey(md.def, false)
		}
	}
	sendKey(d, false)
	time.Sleep(22 * time.Millisecond)
	sendKey(d, true)
	for i := len(modDefs) - 1; i >= 0; i-- {
		if mods&modDefs[i].bit != 0 {
			sendKey(modDefs[i].def, true)
		}
	}
	time.Sleep(10 * time.Millisecond)
}

func sendUnicode(u uint16) {
	for _, f := range []uint32{0x0004, 0x0004 | 0x0002} {
		in := keyInput{typ: 1, scan: u, flags: f}
		countSend(pSendInput.Call(1, uintptr(unsafe.Pointer(&in)), unsafe.Sizeof(in)))
	}
}

func sendMouse(flags uint32) {
	in := mouseInput{typ: 0, flags: flags}
	countSend(pSendInput.Call(1, uintptr(unsafe.Pointer(&in)), unsafe.Sizeof(in)))
}

var modDefs = []struct {
	bit uint32
	def keyDef
}{{modCtrl, modKeys[0]}, {modShift, modKeys[2]}, {modAlt, modKeys[4]}}

// ---------- diagnostics ----------

var (
	sendOK, sendFail atomic.Int64
	lastKey          atomic.Uint32
	lastKeyAt        atomic.Int64
	lastKeyHit       atomic.Bool
	codeNames        = map[uint32]string{}
)

// lastSendErr is the Win32 error of the most recent failed send (5 = access
// denied: the target window belongs to a process running as administrator).
var lastSendErr atomic.Uint32

var elevated = func() bool {
	r, _, _ := sh32.NewProc("IsUserAnAdmin").Call()
	return r != 0
}()

func countSend(r, _ uintptr, err error) {
	if r == 0 {
		sendFail.Add(1)
		if en, ok := err.(syscall.Errno); ok {
			lastSendErr.Store(uint32(en))
		}
	} else {
		sendOK.Add(1)
	}
}

func triggerName(id uint32) string {
	s := ""
	if id>>16&modCtrl != 0 {
		s += "Ctrl+"
	}
	if id>>16&modShift != 0 {
		s += "Shift+"
	}
	if id>>16&modAlt != 0 {
		s += "Alt+"
	}
	if n, ok := codeNames[id&0xFFFF]; ok {
		return s + n
	}
	return fmt.Sprintf("%s(コード 0x%X)", s, id&0xFFFF)
}

func resolveKeys() {
	defer func() {
		for n, d := range keyTable {
			codeNames[d.code()] = n
		}
		for n, c := range mouseCodes {
			codeNames[c] = n
		}
	}()
	for _, d := range keyTable {
		if d.scan != 0 && d.vk == 0 {
			vk, _, _ := pMapVirtualKey.Call(uintptr(d.scan), 1) // VSC -> VK
			d.vk = uint16(vk)
		} else if d.scan == 0 {
			sc, _, _ := pMapVirtualKey.Call(uintptr(d.vk), 0) // VK -> VSC
			d.scan = uint16(sc)
		}
	}
}

// ---------- macro engine ----------

type runState struct{ cancel context.CancelFunc }

type engine struct {
	mu      sync.Mutex
	running map[string]*runState
	fired   map[string]int64 // macro id -> unix ms of last start
}

func (e *engine) onDown(m *Macro, momentary bool) {
	loop := m.Mode == "toggle" || (m.Mode == "hold" && !momentary)
	e.mu.Lock()
	if rs, ok := e.running[m.ID]; ok {
		if m.Mode == "toggle" {
			rs.cancel()
		}
		e.mu.Unlock()
		return
	}
	e.mu.Unlock()
	e.start(m, loop, true)
}

func (e *engine) onUp(m *Macro) {
	if m.Mode != "hold" {
		return
	}
	e.mu.Lock()
	if rs, ok := e.running[m.ID]; ok {
		rs.cancel()
	}
	e.mu.Unlock()
}

func (e *engine) start(m *Macro, loop, relMods bool) {
	ctx, cancel := context.WithCancel(context.Background())
	rs := &runState{cancel: cancel}
	e.mu.Lock()
	if _, ok := e.running[m.ID]; ok {
		e.mu.Unlock()
		cancel()
		return
	}
	e.running[m.ID] = rs
	e.fired[m.ID] = time.Now().UnixMilli()
	e.mu.Unlock()
	go func() {
		defer func() {
			cancel()
			e.mu.Lock()
			if e.running[m.ID] == rs {
				delete(e.running, m.ID)
			}
			e.mu.Unlock()
		}()
		runMacro(ctx, m, loop, relMods)
	}()
}

func (e *engine) stopAll() {
	e.mu.Lock()
	for _, rs := range e.running {
		rs.cancel()
	}
	e.mu.Unlock()
}

func (e *engine) runningIDs() []string {
	e.mu.Lock()
	defer e.mu.Unlock()
	ids := make([]string, 0, len(e.running))
	for id := range e.running {
		ids = append(ids, id)
	}
	return ids
}

func sleepCtx(ctx context.Context, d time.Duration) error {
	if d <= 0 {
		return ctx.Err()
	}
	t := time.NewTimer(d)
	defer t.Stop()
	select {
	case <-ctx.Done():
		return ctx.Err()
	case <-t.C:
		return nil
	}
}

func runMacro(ctx context.Context, m *Macro, loop, relMods bool) {
	// Lift modifiers the user is physically holding (from the trigger combo)
	// so they don't leak into the keys we send; restore them afterwards.
	var lifted uint32
	if relMods {
		lifted = physMods.Load()
		for i, d := range modKeys {
			if lifted&(1<<i) != 0 {
				sendKey(d, true)
			}
		}
	}
	downKeys := map[string]keyDef{}
	defer func() {
		for _, d := range downKeys {
			keyOut(m.sendMode, d, true)
		}
		still := physMods.Load()
		for i, d := range modKeys {
			if lifted&still&(1<<i) != 0 {
				sendKey(d, false)
			}
		}
	}()
	for {
		gap := 20 * time.Millisecond
		for _, s := range m.Steps {
			err := doStep(ctx, m, s, downKeys)
			if err == errSkip {
				gap = 150 * time.Millisecond
				break
			}
			if err != nil {
				return
			}
		}
		if !loop {
			return
		}
		if sleepCtx(ctx, gap) != nil {
			return
		}
	}
}

// errSkip ends the current pass of a macro (condition not met / timed out).
var errSkip = errors.New("skip")

func stepPoint(s Step) point {
	pt := point{int32(s.X), int32(s.Y)}
	if s.Pos != "screen" {
		hwnd, _, _ := pGetForegroundWindow.Call()
		pClientToScreen.Call(hwnd, uintptr(unsafe.Pointer(&pt)))
	}
	return pt
}

func screenPixel(pt point) (r, g, b int, ok bool) {
	hdc, _, _ := pGetDC.Call(0)
	if hdc == 0 {
		return
	}
	c, _, _ := pGetPixel.Call(hdc, uintptr(pt.x), uintptr(pt.y))
	pReleaseDC.Call(0, hdc)
	if uint32(c) == 0xFFFFFFFF {
		return
	}
	return int(c & 0xFF), int(c >> 8 & 0xFF), int(c >> 16 & 0xFF), true
}

func pixelCond(s Step) bool {
	wr, wg, wb, err := parseColor(s.Color)
	if err != nil {
		return false
	}
	r, g, b, ok := screenPixel(stepPoint(s))
	if !ok {
		return false
	}
	near := func(a, b int) bool { d := a - b; return d <= s.Tol && -d <= s.Tol }
	return (near(r, wr) && near(g, wg) && near(b, wb)) != s.Not
}

func deadline(ctx context.Context, ms int) (context.Context, context.CancelFunc) {
	if ms > 0 {
		return context.WithTimeout(ctx, time.Duration(ms)*time.Millisecond)
	}
	return context.WithCancel(ctx)
}

func doStep(ctx context.Context, m *Macro, s Step, downKeys map[string]keyDef) error {
	if err := ctx.Err(); err != nil {
		return err
	}
	switch s.Type {
	case "key":
		if s.Keys == "" {
			return nil
		}
		mods, d, err := parseKeys(s.Keys)
		if err != nil {
			return nil
		}
		for _, md := range modDefs {
			if mods&md.bit != 0 {
				keyOut(m.sendMode, md.def, false)
			}
		}
		if mods != 0 {
			time.Sleep(15 * time.Millisecond)
		}
		keyOut(m.sendMode, d, false)
		time.Sleep(50 * time.Millisecond)
		keyOut(m.sendMode, d, true)
		for i := len(modDefs) - 1; i >= 0; i-- {
			if mods&modDefs[i].bit != 0 {
				keyOut(m.sendMode, modDefs[i].def, true)
			}
		}
		return sleepCtx(ctx, 10*time.Millisecond)
	case "down", "up":
		if s.Keys == "" {
			return nil
		}
		_, d, err := parseKeys(s.Keys)
		if err != nil {
			return nil
		}
		if s.Type == "down" {
			keyOut(m.sendMode, d, false)
			downKeys[s.Keys] = d
		} else {
			keyOut(m.sendMode, d, true)
			delete(downKeys, s.Keys)
		}
		return sleepCtx(ctx, 10*time.Millisecond)
	case "text":
		for _, u := range utf16.Encode([]rune(s.Text)) {
			if err := ctx.Err(); err != nil {
				return err
			}
			typeUnit(m.sendMode, u)
			time.Sleep(6 * time.Millisecond)
		}
		if s.Enter {
			time.Sleep(30 * time.Millisecond)
			d := *keyTable["Enter"]
			keyOut(m.sendMode, d, false)
			time.Sleep(35 * time.Millisecond)
			keyOut(m.sendMode, d, true)
		}
		return sleepCtx(ctx, 10*time.Millisecond)
	case "wait":
		ms := s.Ms
		if s.Jitter > 0 {
			ms += rand.IntN(s.Jitter + 1)
		}
		return sleepCtx(ctx, time.Duration(ms)*time.Millisecond)
	case "click":
		doClick(s)
		return sleepCtx(ctx, 10*time.Millisecond)
	case "ifpixel":
		if !pixelCond(s) {
			return errSkip
		}
	case "waitpixel":
		wctx, cancel := deadline(ctx, s.Timeout)
		defer cancel()
		for !pixelCond(s) {
			if sleepCtx(wctx, 50*time.Millisecond) != nil {
				if ctx.Err() != nil {
					return ctx.Err()
				}
				return errSkip
			}
		}
	case "waitlog":
		want := strings.ToLower(strings.TrimSpace(s.Text))
		if m.logPath == "" || want == "" {
			return errSkip
		}
		ch, unsub := hub.subscribe(m.logPath)
		defer unsub()
		wctx, cancel := deadline(ctx, s.Timeout)
		defer cancel()
		for {
			select {
			case line := <-ch:
				if strings.Contains(strings.ToLower(line), want) {
					return nil
				}
			case <-wctx.Done():
				if ctx.Err() != nil {
					return ctx.Err()
				}
				return errSkip
			}
		}
	}
	return nil
}

// ---------- log file watching ----------

type logStatus struct {
	Found bool   `json:"found"`
	Last  string `json:"last"`
}

type logHub struct {
	mu     sync.Mutex
	tails  map[string]context.CancelFunc
	subs   map[string]map[chan string]struct{}
	status map[string]*logStatus
}

var hub = &logHub{tails: map[string]context.CancelFunc{}, subs: map[string]map[chan string]struct{}{}, status: map[string]*logStatus{}}

func (h *logHub) sync(paths []string) {
	h.mu.Lock()
	defer h.mu.Unlock()
	for p, cancel := range h.tails {
		if !slices.Contains(paths, p) {
			cancel()
			delete(h.tails, p)
			delete(h.status, p)
		}
	}
	for _, p := range paths {
		if _, ok := h.tails[p]; !ok && p != "" {
			ctx, cancel := context.WithCancel(context.Background())
			h.tails[p] = cancel
			h.status[p] = &logStatus{}
			go tailFile(ctx, p)
		}
	}
}

func (h *logHub) subscribe(path string) (chan string, func()) {
	ch := make(chan string, 256)
	h.mu.Lock()
	if h.subs[path] == nil {
		h.subs[path] = map[chan string]struct{}{}
	}
	h.subs[path][ch] = struct{}{}
	h.mu.Unlock()
	return ch, func() {
		h.mu.Lock()
		delete(h.subs[path], ch)
		h.mu.Unlock()
	}
}

func (h *logHub) setFound(path string, found bool) {
	h.mu.Lock()
	if st := h.status[path]; st != nil {
		st.Found = found
	}
	h.mu.Unlock()
}

func (h *logHub) emit(path, line string) {
	line = strings.TrimRight(line, "\r\n \t")
	if line == "" {
		return
	}
	h.mu.Lock()
	if st := h.status[path]; st != nil {
		st.Last = line
	}
	for ch := range h.subs[path] {
		select {
		case ch <- line:
		default:
		}
	}
	h.mu.Unlock()
	if paused.Load() {
		return
	}
	as := active.Load()
	if as == nil {
		return
	}
	low := strings.ToLower(line)
	for _, lm := range as.logs {
		if lm.path == path && strings.Contains(low, lm.text) {
			eng.start(lm.m, false, false)
		}
	}
}

func decodeBytes(b []byte, wide bool) string {
	if wide {
		u := make([]uint16, len(b)/2)
		for i := range u {
			u[i] = uint16(b[2*i]) | uint16(b[2*i+1])<<8
		}
		return string(utf16.Decode(u))
	}
	if len(b) == 0 || utf8.Valid(b) {
		return string(b)
	}
	// system ANSI code page (Shift-JIS on Japanese Windows)
	out := make([]uint16, len(b))
	n, _, _ := pMultiByteToWide.Call(0, 0, uintptr(unsafe.Pointer(&b[0])), uintptr(len(b)), uintptr(unsafe.Pointer(&out[0])), uintptr(len(out)))
	return string(utf16.Decode(out[:n]))
}

func looksWide(b []byte) bool {
	if len(b) >= 2 && b[0] == 0xFF && b[1] == 0xFE {
		return true
	}
	zeros := 0
	n := min(len(b), 64) &^ 1
	for i := 1; i < n; i += 2 {
		if b[i] == 0 {
			zeros++
		}
	}
	return n >= 4 && zeros*4 >= n
}

func tailFile(ctx context.Context, path string) {
	var off int64 = -1
	var rem []byte
	wide := false
	for sleepCtx(ctx, 200*time.Millisecond) == nil {
		fi, err := os.Stat(path)
		if err != nil || fi.IsDir() {
			hub.setFound(path, false)
			off, rem = -1, nil
			continue
		}
		hub.setFound(path, true)
		size := fi.Size()
		f, err := os.Open(path)
		if err != nil {
			continue
		}
		if off < 0 { // first sight: start at the end, only new lines matter
			head := make([]byte, 64)
			n, _ := f.ReadAt(head, 0)
			wide = looksWide(head[:n])
			off = size
			if wide {
				off &^= 1
			}
		} else if size < off { // truncated / recreated
			off, rem = 0, nil
		}
		if size > off {
			buf := make([]byte, min(size-off, 1<<20))
			n, _ := f.ReadAt(buf, off)
			buf = buf[:n]
			if off == 0 {
				wide = looksWide(buf)
				if wide && len(buf) >= 2 && buf[0] == 0xFF && buf[1] == 0xFE {
					buf = buf[2:]
				}
			}
			off += int64(n)
			rem = append(rem, buf...)
			for {
				i, w := -1, 1
				if wide {
					w = 2
					for j := 0; j+1 < len(rem); j += 2 {
						if rem[j] == '\n' && rem[j+1] == 0 {
							i = j
							break
						}
					}
				} else {
					i = slices.Index(rem, '\n')
				}
				if i < 0 {
					break
				}
				hub.emit(path, decodeBytes(rem[:i], wide))
				rem = rem[i+w:]
			}
			if len(rem) > 1<<16 {
				rem = nil
			}
		}
		f.Close()
	}
}

type point struct{ x, y int32 }

func doClick(s Step) {
	switch s.Pos {
	case "window":
		hwnd, _, _ := pGetForegroundWindow.Call()
		pt := point{int32(s.X), int32(s.Y)}
		pClientToScreen.Call(hwnd, uintptr(unsafe.Pointer(&pt)))
		pSetCursorPos.Call(uintptr(pt.x), uintptr(pt.y))
		time.Sleep(30 * time.Millisecond)
	case "screen":
		pSetCursorPos.Call(uintptr(int32(s.X)), uintptr(int32(s.Y)))
		time.Sleep(30 * time.Millisecond)
	}
	var down, up uint32
	switch s.Button {
	case "right":
		down, up = 0x0008, 0x0010
	case "middle":
		down, up = 0x0020, 0x0040
	case "none":
		return
	default:
		down, up = 0x0002, 0x0004
	}
	n := 1
	if s.Double {
		n = 2
	}
	for i := 0; i < n; i++ {
		sendMouse(down)
		time.Sleep(25 * time.Millisecond)
		sendMouse(up)
		if i+1 < n {
			time.Sleep(70 * time.Millisecond)
		}
	}
}

// ---------- hooks ----------

type kbdll struct {
	vk, scan, flags, time uint32
	extra                 uintptr
}

type msll struct {
	pt        point
	mouseData uint32
	flags     uint32
	time      uint32
	extra     uintptr
}

// handleInput runs on the hook thread; returns true to swallow the event.
func handleInput(code uint32, down, momentary bool) bool {
	if !down {
		m, ok := held[code]
		if !ok {
			return false
		}
		delete(held, code)
		if m != nil {
			go eng.onUp(m)
		}
		return true
	}
	if _, ok := held[code]; ok {
		return true // auto-repeat of a trigger that is already down
	}
	id := trigMods(physMods.Load())<<16 | code
	lastKey.Store(id)
	lastKeyAt.Store(time.Now().UnixMilli())
	lastKeyHit.Store(false)
	if pid := pauseID.Load(); pid != 0 && id == pid {
		if !momentary {
			held[code] = nil
		}
		go setPaused(!paused.Load())
		return true
	}
	if paused.Load() {
		return false
	}
	as := active.Load()
	if as == nil {
		return false
	}
	m := as.m[id]
	if m == nil {
		return false
	}
	lastKeyHit.Store(true)
	if !momentary {
		held[code] = m
	}
	go eng.onDown(m, momentary)
	return true
}

func kbProc(nCode, wParam, lParam uintptr) uintptr {
	if int32(nCode) >= 0 {
		k := (*kbdll)(unsafe.Pointer(lParam))
		if k.flags&0x10 == 0 { // not injected
			down := wParam == 0x100 || wParam == 0x104
			if i := modIndex(k.vk); i >= 0 {
				for {
					old := physMods.Load()
					nv := old &^ (1 << i)
					if down {
						nv = old | (1 << i)
					}
					if physMods.CompareAndSwap(old, nv) {
						break
					}
				}
			} else if handleInput(hookCode(k.vk, k.flags&1 != 0), down, false) {
				return 1
			}
		}
	}
	r, _, _ := pCallNextHookEx.Call(0, nCode, wParam, lParam)
	return r
}

func msProc(nCode, wParam, lParam uintptr) uintptr {
	if int32(nCode) >= 0 && wParam != 0x200 { // ignore plain moves fast
		k := (*msll)(unsafe.Pointer(lParam))
		if k.flags&1 == 0 {
			swallow := false
			switch wParam {
			case 0x207:
				swallow = handleInput(0x04, true, false)
			case 0x208:
				swallow = handleInput(0x04, false, false)
			case 0x20B, 0x20C:
				code := uint32(0x05)
				if k.mouseData>>16 == 2 {
					code = 0x06
				}
				swallow = handleInput(code, wParam == 0x20B, false)
			case 0x20A:
				code := uint32(0x201)
				if int16(k.mouseData>>16) < 0 {
					code = 0x202
				}
				swallow = handleInput(code, true, true)
			}
			if swallow {
				return 1
			}
		}
	}
	r, _, _ := pCallNextHookEx.Call(0, nCode, wParam, lParam)
	return r
}

// ---------- foreground tracking ----------

func foregroundInfo() (hwnd uintptr, exe, title string) {
	hwnd, _, _ = pGetForegroundWindow.Call()
	if hwnd == 0 {
		return
	}
	buf := make([]uint16, 512)
	n, _, _ := pGetWindowText.Call(hwnd, uintptr(unsafe.Pointer(&buf[0])), uintptr(len(buf)))
	title = syscall.UTF16ToString(buf[:n])
	var pid uint32
	pGetWindowThreadPID.Call(hwnd, uintptr(unsafe.Pointer(&pid)))
	h, _, _ := pOpenProcess.Call(0x1000, 0, uintptr(pid)) // QUERY_LIMITED_INFORMATION
	if h != 0 {
		pb := make([]uint16, 1024)
		sz := uint32(len(pb))
		r, _, _ := pQueryImageName.Call(h, 0, uintptr(unsafe.Pointer(&pb[0])), uintptr(unsafe.Pointer(&sz)))
		if r != 0 {
			exe = filepath.Base(syscall.UTF16ToString(pb[:sz]))
		}
		pCloseHandle.Call(h)
	}
	return
}

func refreshActive(force bool) {
	hwnd, exe, title := foregroundInfo()
	cfgMu.RLock()
	as, ids := buildActive(cfg, exe, title)
	var logPaths []string
	if force {
		for _, p := range cfg.Profiles {
			if k := logKey(p.LogPath); p.Enabled && k != "" && !slices.Contains(logPaths, k) {
				logPaths = append(logPaths, k)
			}
		}
	}
	pid := uint32(0)
	if cfg.PauseKey != "" {
		pid, _ = parseTrigger(cfg.PauseKey)
	}
	cfgMu.RUnlock()
	pauseID.Store(pid)

	fgMu.Lock()
	changed := force || !slices.Equal(ids, activeIDs)
	fgHwnd, fgExe, fgTitle, activeIDs = hwnd, exe, title, ids
	fgMu.Unlock()
	if changed {
		eng.stopAll()
	}
	active.Store(as)
	if force {
		hub.sync(logPaths)
	}
}

func watchForeground() {
	for {
		refreshActive(false)
		// Resync modifier state in case the hook missed a key-up (lock screen, UAC).
		if len(eng.runningIDs()) == 0 {
			var bits uint32
			for i, d := range modKeys {
				r, _, _ := pGetAsyncKeyState.Call(uintptr(d.vk))
				if r&0x8000 != 0 {
					bits |= 1 << i
				}
			}
			physMods.Store(bits)
		}
		time.Sleep(250 * time.Millisecond)
	}
}

func setPaused(p bool) {
	paused.Store(p)
	if p {
		eng.stopAll()
	}
}

// ---------- tray icon ----------

type wndClassEx struct {
	size       uint32
	style      uint32
	wndProc    uintptr
	clsExtra   int32
	wndExtra   int32
	instance   uintptr
	icon       uintptr
	cursor     uintptr
	background uintptr
	menuName   *uint16
	className  *uint16
	iconSm     uintptr
}

type notifyIconData struct {
	size            uint32
	hwnd            uintptr
	id              uint32
	flags           uint32
	callbackMessage uint32
	icon            uintptr
	tip             [128]uint16
	state           uint32
	stateMask       uint32
	info            [256]uint16
	version         uint32
	infoTitle       [64]uint16
	infoFlags       uint32
	guid            [16]byte
	balloonIcon     uintptr
}

type winMsg struct {
	hwnd    uintptr
	message uint32
	wParam  uintptr
	lParam  uintptr
	time    uint32
	pt      point
	private uint32
}

const trayMsg = 0x8000 + 1

func u16(s string) *uint16 { p, _ := syscall.UTF16PtrFromString(s); return p }

func uiURL() string { return fmt.Sprintf("http://127.0.0.1:%d/", port) }

func openUI() {
	pShellExecute.Call(0, uintptr(unsafe.Pointer(u16("open"))), uintptr(unsafe.Pointer(u16(uiURL()))), 0, 0, 1)
}

func trayData() *notifyIconData {
	nid := &notifyIconData{hwnd: trayHwnd, id: 1}
	nid.size = uint32(unsafe.Sizeof(*nid))
	return nid
}

func quit() {
	eng.stopAll()
	time.Sleep(80 * time.Millisecond)
	if trayHwnd != 0 {
		pShellNotifyIcon.Call(2, uintptr(unsafe.Pointer(trayData())))
	}
	os.Exit(0)
}

func trayProc(hwnd, msg, wParam, lParam uintptr) uintptr {
	if msg == trayMsg {
		switch lParam {
		case 0x202, 0x203: // left click
			openUI()
		case 0x205: // right click
			menu, _, _ := pCreatePopupMenu.Call()
			pauseLabel := "一時停止"
			if paused.Load() {
				pauseLabel = "再開"
			}
			pAppendMenu.Call(menu, 0, 1, uintptr(unsafe.Pointer(u16("設定を開く"))))
			pAppendMenu.Call(menu, 0, 2, uintptr(unsafe.Pointer(u16(pauseLabel))))
			pAppendMenu.Call(menu, 0x800, 0, 0)
			pAppendMenu.Call(menu, 0, 3, uintptr(unsafe.Pointer(u16("終了"))))
			var pt point
			pGetCursorPos.Call(uintptr(unsafe.Pointer(&pt)))
			pSetForegroundWindow.Call(hwnd)
			cmd, _, _ := pTrackPopupMenu.Call(menu, 0x0100|0x0020, uintptr(pt.x), uintptr(pt.y), 0, hwnd, 0)
			pDestroyMenu.Call(menu)
			switch cmd {
			case 1:
				openUI()
			case 2:
				setPaused(!paused.Load())
			case 3:
				quit()
			}
		}
		return 0
	}
	r, _, _ := pDefWindowProc.Call(hwnd, msg, wParam, lParam)
	return r
}

func createTray(hinst uintptr) {
	cls := u16("MacroLoomTray")
	wc := wndClassEx{wndProc: syscall.NewCallback(trayProc), instance: hinst, className: cls}
	wc.size = uint32(unsafe.Sizeof(wc))
	pRegisterClassEx.Call(uintptr(unsafe.Pointer(&wc)))
	trayHwnd, _, _ = pCreateWindowEx.Call(0, uintptr(unsafe.Pointer(cls)), uintptr(unsafe.Pointer(u16(appName))), 0, 0, 0, 0, 0, 0, 0, hinst, 0)
	if trayHwnd == 0 {
		return
	}
	nid := trayData()
	nid.flags = 0x1 | 0x2 | 0x4 // message, icon, tip
	nid.callbackMessage = trayMsg
	nid.icon, _, _ = pLoadIcon.Call(0, 32512)
	copy(nid.tip[:], syscall.StringToUTF16(appName+" - マクロ常駐中"))
	pShellNotifyIcon.Call(0, uintptr(unsafe.Pointer(nid)))
}

// ---------- config persistence ----------

func loadConfig() {
	dir, err := os.UserConfigDir()
	if err != nil {
		dir = "."
	}
	dir = filepath.Join(dir, appName)
	os.MkdirAll(dir, 0o755)
	cfgPath = filepath.Join(dir, "config.json")
	cfg = defaultConfig()
	if b, err := os.ReadFile(cfgPath); err == nil {
		var c Config
		if json.Unmarshal(b, &c) == nil && validate(&c) == nil {
			cfg = &c
		} else {
			os.WriteFile(cfgPath+".broken", b, 0o644)
		}
	}
}

func saveConfig(c *Config) error {
	b, err := json.MarshalIndent(c, "", "  ")
	if err != nil {
		return err
	}
	tmp := cfgPath + ".tmp"
	if err := os.WriteFile(tmp, b, 0o644); err != nil {
		return err
	}
	return os.Rename(tmp, cfgPath)
}

// ---------- HTTP UI ----------

func diagInfo() map[string]any {
	now := time.Now().UnixMilli()
	d := map[string]any{"sendOK": sendOK.Load(), "sendFail": sendFail.Load(), "sendErr": lastSendErr.Load(), "elevated": elevated}
	if at := lastKeyAt.Load(); at != 0 {
		d["key"] = triggerName(lastKey.Load())
		d["keyAgo"] = now - at
		d["keyHit"] = lastKeyHit.Load()
	}
	fired := map[string]int64{}
	eng.mu.Lock()
	for id, at := range eng.fired {
		fired[id] = now - at
	}
	eng.mu.Unlock()
	d["fired"] = fired
	return d
}

func writeJSON(w http.ResponseWriter, v any) {
	w.Header().Set("Content-Type", "application/json; charset=utf-8")
	json.NewEncoder(w).Encode(v)
}

func guard(next http.Handler) http.Handler {
	hosts := []string{fmt.Sprintf("127.0.0.1:%d", port), fmt.Sprintf("localhost:%d", port)}
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if !slices.Contains(hosts, r.Host) {
			http.Error(w, "forbidden", http.StatusForbidden)
			return
		}
		if strings.HasPrefix(r.URL.Path, "/api/") && r.URL.Path != "/api/version" && r.Header.Get("X-Token") != token {
			http.Error(w, "forbidden", http.StatusForbidden)
			return
		}
		next.ServeHTTP(w, r)
	})
}

func pickInfo() map[string]any {
	hwnd, exe, title := foregroundInfo()
	var pt point
	pGetCursorPos.Call(uintptr(unsafe.Pointer(&pt)))
	rel := pt
	if hwnd != 0 {
		pScreenToClient.Call(hwnd, uintptr(unsafe.Pointer(&rel)))
	}
	color := ""
	if r, g, b, ok := screenPixel(pt); ok {
		color = fmt.Sprintf("#%02x%02x%02x", r, g, b)
	}
	return map[string]any{"x": pt.x, "y": pt.y, "wx": rel.x, "wy": rel.y, "exe": exe, "title": title, "color": color}
}

func serve(ln net.Listener) {
	mux := http.NewServeMux()
	mux.HandleFunc("GET /{$}", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		w.Header().Set("Cache-Control", "no-store")
		fmt.Fprint(w, strings.Replace(uiHTML, "__TOKEN__", token, 1))
	})
	mux.HandleFunc("GET /api/version", func(w http.ResponseWriter, r *http.Request) {
		writeJSON(w, map[string]any{"app": appName, "version": version, "elevated": elevated})
	})
	mux.HandleFunc("GET /api/state", func(w http.ResponseWriter, r *http.Request) {
		fgMu.Lock()
		exe, title, ids := fgExe, fgTitle, slices.Clone(activeIDs)
		fgMu.Unlock()
		logs := map[string]logStatus{}
		hub.mu.Lock()
		for p, s := range hub.status {
			logs[p] = *s
		}
		hub.mu.Unlock()
		cfgMu.RLock()
		defer cfgMu.RUnlock()
		writeJSON(w, map[string]any{
			"version": version,
			"logs":    logs,
			"diag":    diagInfo(),
			"config":  cfg, "paused": paused.Load(), "exe": exe, "title": title,
			"active": ids, "running": eng.runningIDs(),
		})
	})
	mux.HandleFunc("PUT /api/config", func(w http.ResponseWriter, r *http.Request) {
		var c Config
		if err := json.NewDecoder(http.MaxBytesReader(w, r.Body, 2<<20)).Decode(&c); err != nil {
			http.Error(w, "設定を読み取れません: "+err.Error(), http.StatusBadRequest)
			return
		}
		if err := validate(&c); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		if err := saveConfig(&c); err != nil {
			http.Error(w, "保存に失敗しました: "+err.Error(), http.StatusInternalServerError)
			return
		}
		cfgMu.Lock()
		cfg = &c
		cfgMu.Unlock()
		refreshActive(true)
		writeJSON(w, map[string]any{"ok": true})
	})
	mux.HandleFunc("POST /api/pause", func(w http.ResponseWriter, r *http.Request) {
		var b struct{ Paused bool }
		json.NewDecoder(r.Body).Decode(&b)
		setPaused(b.Paused)
		writeJSON(w, map[string]any{"paused": b.Paused})
	})
	mux.HandleFunc("POST /api/pick", func(w http.ResponseWriter, r *http.Request) {
		time.Sleep(3 * time.Second)
		writeJSON(w, pickInfo())
	})
	mux.HandleFunc("POST /api/test", func(w http.ResponseWriter, r *http.Request) {
		var b struct{ ID string }
		json.NewDecoder(r.Body).Decode(&b)
		var found *Macro
		cfgMu.RLock()
		for _, p := range cfg.Profiles {
			for _, m := range p.Macros {
				if m.ID == b.ID {
					found = m
				}
			}
		}
		cfgMu.RUnlock()
		if found == nil {
			http.Error(w, "マクロが見つかりません", http.StatusNotFound)
			return
		}
		time.Sleep(3 * time.Second)
		eng.start(found, false, false)
		writeJSON(w, map[string]any{"ok": true})
	})
	mux.HandleFunc("POST /api/elevate", func(w http.ResponseWriter, r *http.Request) {
		exe, err := os.Executable()
		if err != nil {
			http.Error(w, "実行ファイルの場所が分かりません", http.StatusInternalServerError)
			return
		}
		// "runas" shows the Windows UAC prompt; the new instance replaces this one
		rc, _, _ := pShellExecute.Call(0, uintptr(unsafe.Pointer(u16("runas"))), uintptr(unsafe.Pointer(u16(exe))), 0, 0, 1)
		if rc <= 32 {
			http.Error(w, "管理者として起動できませんでした（確認画面でキャンセルされた可能性があります）", http.StatusConflict)
			return
		}
		writeJSON(w, map[string]any{"ok": true})
	})
	mux.HandleFunc("POST /api/quit", func(w http.ResponseWriter, r *http.Request) {
		writeJSON(w, map[string]any{"ok": true})
		go func() { time.Sleep(200 * time.Millisecond); quit() }()
	})
	http.Serve(ln, guard(mux))
}

// ---------- main ----------

func fatal(msg string) {
	pMessageBox.Call(0, uintptr(unsafe.Pointer(u16(msg))), uintptr(unsafe.Pointer(u16(appName))), 0x10)
	os.Exit(1)
}

// takeOver handles "the port is busy". If the same version is already
// running it returns false (just show its UI). If an older MacroLoom holds the
// port it asks that one to quit and returns true so we can start in its place.
func takeOver() (bool, error) {
	c := &http.Client{Timeout: 2 * time.Second}
	if resp, err := c.Get(uiURL() + "api/version"); err == nil {
		var v struct {
			App, Version string
			Elevated     bool
		}
		json.NewDecoder(resp.Body).Decode(&v)
		resp.Body.Close()
		// same version: keep the running one, unless we are the administrator
		// instance replacing a non-administrator one
		if resp.StatusCode == 200 && v.App == appName && v.Version == version && (v.Elevated || !elevated) {
			return false, nil
		}
	}
	resp, err := c.Get(uiURL())
	if err != nil {
		return false, err
	}
	body, _ := io.ReadAll(io.LimitReader(resp.Body, 1<<20))
	resp.Body.Close()
	m := regexp.MustCompile(`const TOKEN = "([0-9a-f]{32})"`).FindSubmatch(body)
	if m == nil || !strings.Contains(string(body), "<title>"+appName+"</title>") {
		return false, fmt.Errorf("ポート %d を別のアプリが使用しています", port)
	}
	req, _ := http.NewRequest("POST", uiURL()+"api/quit", nil)
	req.Header.Set("X-Token", string(m[1]))
	resp, err = c.Do(req)
	if err != nil {
		return false, err
	}
	resp.Body.Close()
	return true, nil
}

// compile-time checks of the Win32 struct layouts (64-bit)
var (
	_ [40 - unsafe.Sizeof(keyInput{})]byte
	_ [unsafe.Sizeof(keyInput{}) - 40]byte
	_ [40 - unsafe.Sizeof(mouseInput{})]byte
	_ [unsafe.Sizeof(mouseInput{}) - 40]byte
	_ [976 - unsafe.Sizeof(notifyIconData{})]byte
	_ [unsafe.Sizeof(notifyIconData{}) - 976]byte
	_ [80 - unsafe.Sizeof(wndClassEx{})]byte
	_ [unsafe.Sizeof(wndClassEx{}) - 80]byte
	_ [48 - unsafe.Sizeof(winMsg{})]byte
	_ [unsafe.Sizeof(winMsg{}) - 48]byte
	_ [24 - unsafe.Sizeof(kbdll{})]byte
	_ [unsafe.Sizeof(kbdll{}) - 24]byte
	_ [32 - unsafe.Sizeof(msll{})]byte
	_ [unsafe.Sizeof(msll{}) - 32]byte
)

func main() {
	runtime.LockOSThread()

	addr := fmt.Sprintf("127.0.0.1:%d", port)
	ln, err := net.Listen("tcp", addr)
	if err != nil {
		replaced, terr := takeOver()
		if terr != nil {
			fatal("起動できませんでした: " + terr.Error())
		}
		if !replaced {
			openUI() // same version already running
			return
		}
		for i := 0; i < 50 && err != nil; i++ {
			time.Sleep(100 * time.Millisecond)
			ln, err = net.Listen("tcp", addr)
		}
		if err != nil {
			fatal("古いバージョンの MacroLoom を終了できませんでした。タスクトレイのアイコンを右クリックして終了してから、もう一度起動してください。")
		}
	}
	if pSetDpiCtx.Find() == nil {
		pSetDpiCtx.Call(^uintptr(3)) // PER_MONITOR_AWARE_V2 (-4)
	}
	tb := make([]byte, 16)
	crand.Read(tb)
	token = hex.EncodeToString(tb)

	resolveKeys()
	loadConfig()
	refreshActive(true)
	go watchForeground()
	go serve(ln)

	hinst, _, _ := pGetModuleHandle.Call(0)
	kb, _, _ := pSetWindowsHookEx.Call(13, syscall.NewCallback(kbProc), hinst, 0)
	ms, _, _ := pSetWindowsHookEx.Call(14, syscall.NewCallback(msProc), hinst, 0)
	if kb == 0 || ms == 0 {
		fatal("キーボード/マウスフックを設定できませんでした。")
	}
	createTray(hinst)
	openUI()

	var msg winMsg
	for {
		r, _, _ := pGetMessage.Call(uintptr(unsafe.Pointer(&msg)), 0, 0, 0)
		if int32(r) <= 0 {
			break
		}
		pTranslateMessage.Call(uintptr(unsafe.Pointer(&msg)))
		pDispatchMessage.Call(uintptr(unsafe.Pointer(&msg)))
	}
}
