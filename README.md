# Batocera x86-64-v3 Migration

Moves a Batocera PC from the **x86_64** image (Xorg) to the **x86-64-v3** image (Wayland/LabWC) and keeps custom setups working.

**scan → backup → update → integrate**

Since Batocera 43, x86-64-v3 is the preferred PC image for AMD and Intel graphics, and Batocera 44 can switch to it from the updates menu. The switch replaces only the system partition, so `/userdata` is kept. Custom setups can still break, because things in `/userdata` assumed Xorg: game hooks, launchers, services, Wine/Lutris ports and the old system overlay. This tool finds those things, backs them up, and puts them back on v3 with full functionality.

## Install

**From Batocera Unofficial Add-ons (BUA):** System Utilities → **x86-64-v3 Migration**. Run it once before the update and once after. It asks before doing anything.

**Over SSH:**

```
curl -fsSL https://github.com/klova5/batocera-wayland-v3-migrate/releases/latest/download/batocera_v3_migrate.py -o /userdata/system/batocera_v3_migrate.py
python3 /userdata/system/batocera_v3_migrate.py
```

With no arguments, it runs whichever step comes next.

## Ports menu (controller)

```
python3 /userdata/system/batocera_v3_migrate.py launcher install
```

This adds **V3 Migration** to ES's **Ports** list, so every step can be run from the couch. It works with stock ES and with custom frontends such as GCM, because it is an ordinary Ports entry. It opens a full-screen menu showing the board, the current step and the next one, with the next step already selected:

- **Before the update:** Scan, Back up (pick a drive under `/media`, or internal), Prepare for the update, then Update now or Undo prepare.
- **After the update, on v3:** Integrate (safe to repeat).
- **Any time:** Status and Last result.

Each step asks Yes/No first, shows its output live, then shows the result in a scrollable view. A step keeps running even if the window is closed; opening the menu again follows it to the end. Output is kept in `/userdata/system/logs/v3-migrate-menu.log`. Rollback is not in the menu: it rewrites the boot partition, so it stays an SSH command.

Controller: D-pad or left stick moves, **B** or **Start** selects, **A** or **Select** goes back, **X** switches buttons, **L1/R1** page up and down. Without `dialog` the menu falls back to numbered choices (keyboard). Remove it with `launcher remove`. `integrate` refreshes an installed launcher.

## The four steps

| Step | When | What it does |
| --- | --- | --- |
| 1. `scan` | Before the update | Finds everything x86-64-v3 will break or could break, and says whether integrate handles each one automatically (`+`) or needs your decision (`!`). |
| 2. `backup` | Before the update | Backs up only those things, plus the boot partition for rollback. It takes minutes, and every archive is hashed and read back. The default location is `/userdata/system/v3-migration/backups`; use `--dest /media/<drive>` for an external drive. |
| 3. `update` | Before the update | Sets aside what can't survive the switch (the old overlay, X11-only services). Then start the x86-64-v3 upgrade from Batocera's updates menu and reboot. |
| 4. `integrate` | After the reboot, on v3 | Puts everything back with full functionality, then lists what was integrated and what needs you. |

### What integrate does on its own

- **Game hooks** (`/userdata/system/scripts`) run through one guard: each in its own session, with no inherited handles and a 10-second limit. A hook's helper can no longer hold a launch open.
- **Scripts that read Xorg's `-auth` file** get a working Xwayland cookie fallback, instead of stopping with "X11 authorization unavailable".
- **X11 apps run as the `batocera` user** (Lutris, Wine, Plutonium) are let in to Xwayland at every boot, even though Xwayland starts on demand.
- **Services that set `DISPLAY=:0`** (Sunshine, for example) become Wayland-aware and are switched back on.
- **The old overlay:** files v3 doesn't have are restored and saved to a new overlay. Files v3 has its own version of are kept as v3's and listed. Files that can't load on v3 are left out.
- **A pinned display output** is re-mapped to v3's port name (Xorg `HDMI-A-0` becomes DRM `HDMI-A-1`).
- **A safety net** is installed (below).

An X11 desktop (openbox and similar) can't run under Wayland, so integrate switches it off and keeps its files. BUA's own Desktop add-on has a Wayland version.

## Safety net

- **Launch watchdog.** If a launch has nothing running under it and its log is quiet for 25 seconds, the watchdog stops whatever holds it and logs why. It never stops ES, evmapy, the hotkeys, dbus or anything that was running before the launch.
- **Rescue combo:** hold **Select + Start + L + R** for 3 seconds, or press **Ctrl + Alt + End**. It closes the running game and returns to ES, even when hotkeys are broken.
- Over SSH: `python3 /userdata/system/launch_watchdog.py diagnose`, `free` or `rescue`.

## Rollback

```
python3 /userdata/system/batocera_v3_migrate.py rollback && reboot
```

This writes the backed-up x86_64 boot partition back. `status` shows where you are.

## Build-specific setups

Anything unique to one system can be described in a small JSON file in `/userdata/system/v3-migrate.d/`, covering extra backup paths, binaries to re-check, commands to run after integrating, and checks to verify. Run `python3 batocera_v3_migrate.py init-plugin <name>` for a template.

## Requirements and limits

- Batocera 44 on a 64-bit PC with an x86-64-v3 CPU (AVX2 and others). The tool checks this and also runs Batocera's own eligibility check.
- AMD and Intel graphics. NVIDIA on x86-64-v3 is experimental in Batocera, so the tool refuses it unless you pass `--allow-nvidia`.
- One Python file, standard library only, so there's nothing to install. It has been tested end to end on one real migration (Radeon 890M, v44 stable).
- Saved emulator controller profiles aren't checked. If one points at a physical pad that a controller forwarder grabs, point it at the forwarded slot instead.

## License

GPL-3.0, like Batocera Unofficial Add-ons.
