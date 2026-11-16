package main

import "testing"

func TestConfig(t *testing.T) {
	c := defaultConfig()
	if err := validate(c); err != nil {
		t.Fatal(err)
	}
	for _, m := range c.Profiles[0].Macros {
		m.Enabled = true
	}
	a, ids := buildActive(c, `C:\UO\Client.EXE`, "Ultima Online")
	if len(ids) != 1 || len(a.m) != 2 {
		t.Fatalf("active %v %v", ids, a)
	}
	if _, ids := buildActive(c, "chrome.exe", "x"); len(ids) != 0 {
		t.Fatal("should not match")
	}
	id, err := parseTrigger("Ctrl+Shift+F1")
	if err != nil || id != (3<<16|0x70) {
		t.Fatalf("%x %v", id, err)
	}
	if a.m[uint32(0x05)] == nil || a.m[uint32(0x78)] == nil {
		t.Fatal("trigger ids")
	}
	if _, err := parseTrigger("Ctrl+"); err == nil {
		t.Fatal("want error")
	}
	if _, _, err := parseKeys("XButton1"); err == nil {
		t.Fatal("mouse not allowed in steps")
	}
	c.Profiles[0].LogPath = ` C:\UO\Journal.txt `
	c.Profiles[0].Macros[0].LogTrigger = "Poison"
	c.Profiles[0].Macros[0].Trigger = ""
	c.Profiles[0].Macros[0].Steps = append(c.Profiles[0].Macros[0].Steps, Step{Type: "ifpixel", Color: "#ff0080"})
	if err := validate(c); err != nil {
		t.Fatal(err)
	}
	a, _ = buildActive(c, "client.exe", "")
	if len(a.logs) != 1 || a.logs[0].text != "poison" || a.logs[0].path != `c:\uo\journal.txt` || len(a.m) != 1 {
		t.Fatalf("logs %+v", a.logs)
	}
	if r, g, b, err := parseColor("#ff0080"); err != nil || r != 255 || g != 0 || b != 128 {
		t.Fatal("color")
	}
	c.Profiles[0].Macros[0].Steps[1].Color = "red"
	if validate(c) == nil {
		t.Fatal("want color error")
	}
	c.Profiles[0].Macros[0].Steps[0].Type = "bogus"
	if validate(c) == nil {
		t.Fatal("want error")
	}
}
