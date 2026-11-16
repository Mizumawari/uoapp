package main

import (
	"fmt"
	"strings"
)

type keyDef struct {
	vk   uint16
	scan uint16
	ext  bool
}

// code is the identifier the keyboard hook reports for this key.
func (d keyDef) code() uint32 { return hookCode(uint32(d.vk), d.ext) }

func hookCode(vk uint32, ext bool) uint32 {
	if vk == 0x0D && ext {
		return 0x10D // NumpadEnter
	}
	return vk
}

const (
	modCtrl  = 1
	modShift = 2
	modAlt   = 4
)

var keyTable = map[string]*keyDef{}

// keys defined by physical position (scan code); vk is resolved at startup.
var scanKeys = map[string]uint16{
	"Minus": 0x0C, "Equal": 0x0D, "BracketLeft": 0x1A, "BracketRight": 0x1B,
	"Backslash": 0x2B, "Semicolon": 0x27, "Quote": 0x28, "Backquote": 0x29,
	"Comma": 0x33, "Period": 0x34, "Slash": 0x35, "IntlRo": 0x73, "IntlYen": 0x7D,
}

var mouseCodes = map[string]uint32{
	"MButton": 0x04, "XButton1": 0x05, "XButton2": 0x06, "WheelUp": 0x201, "WheelDown": 0x202,
}

func init() {
	add := func(n string, vk uint16, ext bool) { keyTable[n] = &keyDef{vk: vk, ext: ext} }
	for c := 'A'; c <= 'Z'; c++ {
		add(string(c), uint16(c), false)
	}
	for c := '0'; c <= '9'; c++ {
		add(string(c), uint16(c), false)
		add(fmt.Sprintf("Numpad%c", c), uint16(0x60+c-'0'), false)
	}
	for i := 1; i <= 24; i++ {
		add(fmt.Sprintf("F%d", i), uint16(0x70+i-1), false)
	}
	add("Enter", 0x0D, false)
	add("NumpadEnter", 0x0D, true)
	add("Escape", 0x1B, false)
	add("Space", 0x20, false)
	add("Tab", 0x09, false)
	add("Backspace", 0x08, false)
	add("Insert", 0x2D, true)
	add("Delete", 0x2E, true)
	add("Home", 0x24, true)
	add("End", 0x23, true)
	add("PageUp", 0x21, true)
	add("PageDown", 0x22, true)
	add("Up", 0x26, true)
	add("Down", 0x28, true)
	add("Left", 0x25, true)
	add("Right", 0x27, true)
	add("NumpadMultiply", 0x6A, false)
	add("NumpadAdd", 0x6B, false)
	add("NumpadSubtract", 0x6D, false)
	add("NumpadDecimal", 0x6E, false)
	add("NumpadDivide", 0x6F, true)
	add("Pause", 0x13, false)
	add("ScrollLock", 0x91, false)
	add("CapsLock", 0x14, false)
	add("PrintScreen", 0x2C, false)
	for n, sc := range scanKeys {
		keyTable[n] = &keyDef{scan: sc}
	}
}

func splitCombo(s string) (mods uint32, key string, err error) {
	parts := strings.Split(s, "+")
	for i, p := range parts {
		p = strings.TrimSpace(p)
		if i == len(parts)-1 {
			key = p
			break
		}
		switch strings.ToLower(p) {
		case "ctrl":
			mods |= modCtrl
		case "shift":
			mods |= modShift
		case "alt":
			mods |= modAlt
		default:
			return 0, "", fmt.Errorf("不明な修飾キー %q", p)
		}
	}
	if key == "" {
		return 0, "", fmt.Errorf("キーが指定されていません")
	}
	return mods, key, nil
}

// parseKeys parses a keyboard combo used in a step, e.g. "Ctrl+Q".
func parseKeys(s string) (uint32, keyDef, error) {
	mods, key, err := splitCombo(s)
	if err != nil {
		return 0, keyDef{}, err
	}
	d, ok := keyTable[key]
	if !ok {
		return 0, keyDef{}, fmt.Errorf("不明なキー %q", key)
	}
	return mods, *d, nil
}

// parseTrigger parses a trigger (keyboard or mouse) into a lookup id.
func parseTrigger(s string) (uint32, error) {
	mods, key, err := splitCombo(s)
	if err != nil {
		return 0, err
	}
	if c, ok := mouseCodes[key]; ok {
		return mods<<16 | c, nil
	}
	d, ok := keyTable[key]
	if !ok {
		return 0, fmt.Errorf("不明なキー %q", key)
	}
	return mods<<16 | d.code(), nil
}
