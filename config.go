package main

import (
	"fmt"
	"path/filepath"
	"strings"
)

type Step struct {
	Type   string `json:"type"` // key, down, up, text, wait, click
	Keys   string `json:"keys,omitempty"`
	Text   string `json:"text,omitempty"`
	Enter  bool   `json:"enter,omitempty"`
	Ms     int    `json:"ms,omitempty"`
	Jitter int    `json:"jitter,omitempty"`
	Button string `json:"button,omitempty"` // left, right, middle, none
	Double bool   `json:"double,omitempty"`
	Pos    string `json:"pos,omitempty"` // cursor, window, screen
	X      int    `json:"x"`
	Y      int    `json:"y"`
	// ifpixel / waitpixel / waitlog
	Color   string `json:"color,omitempty"` // #RRGGBB
	Tol     int    `json:"tol,omitempty"`
	Not     bool   `json:"not,omitempty"`
	Timeout int    `json:"timeout,omitempty"` // ms, 0 = no limit
}

type Macro struct {
	ID      string `json:"id"`
	Name    string `json:"name"`
	Trigger string `json:"trigger"`
	Mode    string `json:"mode"` // once, hold, toggle
	Enabled bool   `json:"enabled"`
	Steps   []Step `json:"steps"`
	// LogTrigger: run once when a new log line contains this text.
	LogTrigger string `json:"logTrigger,omitempty"`

	logPath  string // copied from the owning profile by validate
	sendMode string // likewise
}

type Profile struct {
	ID      string   `json:"id"`
	Name    string   `json:"name"`
	Match   string   `json:"match"` // substring of exe name or window title; empty = everywhere
	Enabled bool     `json:"enabled"`
	Macros  []*Macro `json:"macros"`
	LogPath string   `json:"logPath,omitempty"` // game log / journal file to watch
	// SendMode: "" / "keys" (key presses), "unicode" (unicode text), "post" (messages posted to the window)
	SendMode string `json:"sendMode,omitempty"`
	// Kit: id of the UI kit this profile was created from (display only)
	Kit string `json:"kit,omitempty"`
}

type logMacro struct {
	path string
	text string
	m    *Macro
}

type activeSet struct {
	m    map[uint32]*Macro
	logs []logMacro
}

func logKey(p string) string { return strings.ToLower(strings.TrimSpace(p)) }

func parseColor(s string) (r, g, b int, err error) {
	if len(s) != 7 || s[0] != '#' {
		return 0, 0, 0, fmt.Errorf("色は #RRGGBB 形式で指定してください")
	}
	if _, err = fmt.Sscanf(s[1:], "%02x%02x%02x", &r, &g, &b); err != nil {
		return 0, 0, 0, fmt.Errorf("色は #RRGGBB 形式で指定してください")
	}
	return
}

type Config struct {
	PauseKey string     `json:"pauseKey"`
	Profiles []*Profile `json:"profiles"`
}

func defaultConfig() *Config {
	return &Config{
		PauseKey: "Pause",
		Profiles: []*Profile{{
			ID: "p-uo", Name: "Ultima Online", Match: "client.exe", Enabled: true, SendMode: "post",
			Macros: []*Macro{
				{ID: "m-ex1", Name: "例: bank と発言", Trigger: "F9", Mode: "once", Enabled: false,
					Steps: []Step{{Type: "text", Text: "bank", Enter: true}}},
				{ID: "m-ex2", Name: "例: 押している間 F1 → 待ち を繰り返す", Trigger: "XButton1", Mode: "hold", Enabled: false,
					Steps: []Step{{Type: "key", Keys: "F1"}, {Type: "wait", Ms: 800, Jitter: 200}}},
			},
		}},
	}
}

func validate(c *Config) error {
	if c.PauseKey != "" {
		if _, err := parseTrigger(c.PauseKey); err != nil {
			return fmt.Errorf("一時停止キー: %v", err)
		}
	}
	for _, p := range c.Profiles {
		if p == nil || p.ID == "" {
			return fmt.Errorf("プロファイルIDがありません")
		}
		switch p.SendMode {
		case "", "keys", "unicode", "post":
		default:
			return fmt.Errorf("「%s」: 不明な送信方式 %q", p.Name, p.SendMode)
		}
		for _, m := range p.Macros {
			if m == nil || m.ID == "" {
				return fmt.Errorf("マクロIDがありません")
			}
			m.logPath = logKey(p.LogPath)
			m.sendMode = p.SendMode
			where := fmt.Sprintf("「%s / %s」", p.Name, m.Name)
			switch m.Mode {
			case "once", "hold", "toggle":
			default:
				return fmt.Errorf("%s: 不明な動作モード %q", where, m.Mode)
			}
			if m.Trigger != "" {
				if _, err := parseTrigger(m.Trigger); err != nil {
					return fmt.Errorf("%s 起動キー: %v", where, err)
				}
			}
			for i, s := range m.Steps {
				switch s.Type {
				case "key", "down", "up":
					if s.Keys == "" {
						continue
					}
					if _, _, err := parseKeys(s.Keys); err != nil {
						return fmt.Errorf("%s 手順%d: %v", where, i+1, err)
					}
				case "text", "wait", "click", "waitlog":
				case "ifpixel", "waitpixel":
					if _, _, _, err := parseColor(s.Color); err != nil {
						return fmt.Errorf("%s 手順%d: %v", where, i+1, err)
					}
				default:
					return fmt.Errorf("%s 手順%d: 不明な種類 %q", where, i+1, s.Type)
				}
			}
		}
	}
	return nil
}

// buildActive returns the trigger table for the given foreground app.
func buildActive(c *Config, exe, title string) (*activeSet, []string) {
	as := &activeSet{m: map[uint32]*Macro{}}
	out := as.m
	var ids []string
	base := strings.ToLower(filepath.Base(strings.ReplaceAll(exe, `\`, "/")))
	lt := strings.ToLower(title)
	for _, p := range c.Profiles {
		if !p.Enabled {
			continue
		}
		if m := strings.ToLower(strings.TrimSpace(p.Match)); m != "" {
			if !strings.Contains(base, m) && !strings.Contains(lt, m) {
				continue
			}
		}
		ids = append(ids, p.ID)
		for _, m := range p.Macros {
			if !m.Enabled || len(m.Steps) == 0 {
				continue
			}
			if t := strings.ToLower(strings.TrimSpace(m.LogTrigger)); t != "" && m.logPath != "" {
				as.logs = append(as.logs, logMacro{m.logPath, t, m})
			}
			if m.Trigger == "" {
				continue
			}
			id, err := parseTrigger(m.Trigger)
			if err != nil {
				continue
			}
			if _, dup := out[id]; !dup {
				out[id] = m
			}
		}
	}
	return as, ids
}
