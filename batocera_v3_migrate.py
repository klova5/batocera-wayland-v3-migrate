#!/usr/bin/env python3
"""
batocera_v3_migrate.py - safe x86_64 (Xorg) -> x86-64-v3 (Wayland/LabWC) migration
toolkit for Batocera Linux.  Single file, Python 3 standard library only.

Works on any x86_64 Batocera install.  Nothing about a specific machine is
hard-coded: everything is discovered at audit time, and anything unique to a
build is described with small JSON "integration" files in
/userdata/system/v3-migrate.d/ (see `init-plugin`).

Phases (run in order, all on the Batocera box over SSH):

  audit          read-only inventory + risk report (safe to run any time)
  backup         full backup to an external drive (+ boot partition for rollback)
  verify-backup  re-hash every archive in a backup
  migrate        preflight, then official batocera-upgrade to x86-64-v3, then
                 park the old overlay and X11-only services (nothing changes
                 if the upgrade itself fails)
  -- reboot --
  integrate      post-migration checks; add --apply to perform the safe fixes
  rollback       put the backed-up x86_64 boot partition back
  status         show where you are
  init-plugin    write an integration template for something custom
  launcher       install|remove "V3 Migration" in ES's Ports list: a menu for
                 all of the above that works with a controller (`menu`)

Every command that changes something asks for a typed confirmation unless
--yes is given, and every file it edits is copied first.
"""

import argparse
import datetime as _dt
import fnmatch
import hashlib
import json
import os
import re
import shutil
import signal
import socket
import stat
import subprocess
import sys
import tarfile
import urllib.request

VERSION = "2.1.0"

# --------------------------------------------------------------------------
# paths (everything goes through P() so the tool can be tested on a mock tree)
# --------------------------------------------------------------------------
ROOT = "/"


def P(path):
    if ROOT == "/":
        return path
    return os.path.join(ROOT, path.lstrip("/"))


def UNP(path):
    """Strip the test root again (for reporting)."""
    if ROOT != "/" and path.startswith(ROOT):
        return "/" + os.path.relpath(path, ROOT)
    return path


def TEST_MODE():
    return ROOT != "/"


STATE_DIR = "/userdata/system/v3-migration"
PLUGIN_DIR = "/userdata/system/v3-migrate.d"
BATOCERA_CONF = "/userdata/system/batocera.conf"
BOOT_CONF = "/boot/batocera-boot.conf"
BOARD_FILE = "/boot/boot/batocera.board"
OVERLAY = "/boot/boot/overlay"
V3_BOARD = "x86-64-v3"
V1_BOARD = "x86_64"
DEFAULT_UPDATE_URL = "https://updates.batocera.org"

# x86-64-v3 = v2 + these.  /proc/cpuinfo calls LZCNT "abm" on most CPUs.
V2_FLAGS = ["cx16", "lahf_lm", "popcnt", "sse4_1", "sse4_2", "ssse3"]
V3_FLAGS = ["avx", "avx2", "bmi1", "bmi2", "f16c", "fma", "movbe", "xsave"]
LZCNT_ALIASES = ["abm", "lzcnt"]

GPU_VENDORS = {"0x1002": "amd", "0x8086": "intel", "0x10de": "nvidia"}

# things that only work against an X server (or set X-only backends)
X11_PATTERNS = [
    (r"\bxrandr\b", "xrandr sets modes on Xorg only; use batocera-resolution (or wlr-randr) on v3"),
    (r"\bxdotool\b", "xdotool cannot drive Wayland windows"),
    (r"\bxset\b", "xset (DPMS/screensaver) has no effect under LabWC"),
    (r"\bxinput\b", "xinput only sees Xwayland devices; use libinput/udev rules"),
    (r"\bwmctrl\b|\bxwininfo\b|\bxprop\b", "X window inspection does not see native Wayland windows"),
    (r"\bopenbox\b|\bmatchbox", "X window manager; LabWC replaces it"),
    (r"\bstartx\b|\bxinit\b|\bXorg\b", "starts/assumes an Xorg server"),
    (r"xorg\.conf", "Xorg config is ignored on v3"),
    (r"\bxmodmap\b|\bsetxkbmap\b", "keyboard layout is set by LabWC on v3"),
    (r"\bunclutter\b", "cursor hiding is handled by the compositor"),
    (r"\bxhost\b|\bxclip\b|\bxsel\b", "X-only utility"),
    (r"QT_QPA_PLATFORM=xcb", "forces Qt onto Xwayland (works, but check scaling/input)"),
    (r"SDL_VIDEODRIVER=x11", "forces SDL onto Xwayland (works, but check fullscreen/vsync)"),
    (r"GDK_BACKEND=x11", "forces GTK onto Xwayland"),
    (r"\bDISPLAY=:?[0-9]", "hard-coded X display; Xwayland's display number is not guaranteed"),
]
X11_RE = [(re.compile(p), why) for p, why in X11_PATTERNS]

TEXT_EXT = {".sh", ".py", ".desktop", ".conf", ".cfg", ".ini", ".service", ".rules", ".keys", ""}
SKIP_DIRS = {".cache", "cache", "Cache", "upgrade", "logs", "v3-migration", ".Trash-0",
             "Trash", "thumbnails", "drive_c", "shadercache", "shader_cache", "__pycache__"}

# copies and backups of things are not "live" and only add noise to scans (never to backups)
SCAN_SKIP_GLOBS = ["*backup*", "*Backup*", "*BACKUP*", "*.before-*", "*.before_*", ".bua-update.*",
                   "*.pre-*", "*.old", "*-old", "*.bak", "*.orig", "*KNOWN-GOOD*", "*working-backup*",
                   ".bua-recovery-parked", ".bua-updater-backups", "docker", "containerd", ".git",
                   "node_modules", "steamapps", "compatdata", "pfx"]
SECRET_KEY_RE = re.compile(r"(key|pass|psk|secret|token|randomseed|password)", re.I)

SEVERITY_ORDER = {"blocker": 0, "critical": 1, "warn": 2, "info": 3}

# --------------------------------------------------------------------------
# small helpers
# --------------------------------------------------------------------------
ASSUME_YES = False


def now():
    return _dt.datetime.now().strftime("%Y-%m-%dT%H:%M:%S")


def stamp():
    return _dt.datetime.now().strftime("%Y%m%d-%H%M%S")


def say(msg=""):
    print(msg, flush=True)


def head(msg):
    say("\n== " + msg + " " + "=" * max(0, 60 - len(msg)))


def human(n):
    n = float(n or 0)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return ("%.1f %s" % (n, unit)) if unit != "B" else ("%d B" % n)
        n /= 1024.0


def read(path, default=""):
    try:
        with open(P(path), "r", errors="replace") as f:
            return f.read()
    except OSError:
        return default


def write_json(path, data):
    os.makedirs(os.path.dirname(P(path)), exist_ok=True)
    tmp = P(path) + ".tmp"
    with open(tmp, "w") as f:
        json.dump(data, f, indent=2, sort_keys=True)
    os.replace(tmp, P(path))


def load_json(path, default=None):
    try:
        with open(P(path)) as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def which(cmd):
    if TEST_MODE():
        return None  # never call real system tools against a mock tree
    return shutil.which(cmd)


def run(cmd, timeout=120, shell=False, env=None):
    """Return (rc, combined output). rc=127 when the tool is absent."""
    if TEST_MODE():
        return 127, "(test mode: not executed) %s" % (cmd if shell else " ".join(cmd))
    if not shell and not shutil.which(cmd[0]):
        return 127, "%s: not found" % cmd[0]
    try:
        r = subprocess.run(cmd, shell=shell, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           timeout=timeout, env=env)
        return r.returncode, r.stdout.decode(errors="replace")
    except subprocess.TimeoutExpired:
        return 124, "timeout after %ss" % timeout
    except OSError as e:
        return 126, str(e)


def confirm(word, what):
    if ASSUME_YES:
        say("(--yes) %s" % what)
        return True
    say("\n%s\nType %s to continue, anything else to stop: " % (what, word))
    try:
        ans = input().strip()
    except EOFError:
        ans = ""
    return ans == word


def sha256_file(path, bufsize=4 * 1024 * 1024):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(bufsize)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


# --------------------------------------------------------------------------
# batocera.conf (key=value, comments kept, edits always backed up)
# --------------------------------------------------------------------------
def conf_parse(path=BATOCERA_CONF):
    out = {}
    for line in read(path).splitlines():
        s = line.strip()
        if not s or s.startswith("#") or "=" not in s:
            continue
        k, v = s.split("=", 1)
        out[k.strip()] = v.strip()
    return out


def conf_backup(path=BATOCERA_CONF):
    src = P(path)
    if not os.path.exists(src):
        return None
    dst = P(STATE_DIR + "/conf-backups/" + os.path.basename(path) + "." + stamp())
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copy2(src, dst)
    return UNP(dst)


def conf_set(key, value, path=BATOCERA_CONF):
    """Set (value str) or remove (value None) one key; everything else untouched."""
    src = P(path)
    lines = read(path).splitlines()
    out, done = [], False
    for line in lines:
        s = line.strip()
        if s and not s.startswith("#") and "=" in s and s.split("=", 1)[0].strip() == key:
            if value is not None and not done:
                out.append("%s=%s" % (key, value))
            done = True
            continue
        out.append(line)
    if value is not None and not done:
        out.append("%s=%s" % (key, value))
    tmp = src + ".v3m.tmp"
    with open(tmp, "w") as f:
        f.write("\n".join(out) + "\n")
    os.replace(tmp, src)


# --------------------------------------------------------------------------
# step journal: a step started from the menu records how to undo each change
# before making it, so Cancel (or a crash, or a power cut) can put everything back
# --------------------------------------------------------------------------
JOURNAL_DIR = STATE_DIR + "/journal"
CANCEL_RC = 130
JOURNAL = None
_ORIG = {}


class Journal:
    def __init__(self, label):
        self.root = P(JOURNAL_DIR)
        self.label, self.ops, self.seen = label, [], set()
        self.busy = False
        self.critical_reason, self.cancel_pending = None, False
        _ORIG["makedirs"](os.path.join(self.root, "files"), exist_ok=True)
        self.save()

    def mine(self, real):
        return real == self.root or real.startswith(self.root + os.sep)

    def save(self):
        tmp = os.path.join(self.root, "journal.json.tmp")
        with _ORIG["open"](tmp, "w") as fh:
            json.dump({"label": self.label, "start": now(), "ops": self.ops}, fh)
        _ORIG["replace"](tmp, os.path.join(self.root, "journal.json"))

    def add(self, op):
        self.ops.append(op)
        self.save()

    def file(self, path):
        """Before a file is written, replaced, moved or removed: keep what it was."""
        real = os.path.abspath(os.fsdecode(path))
        if real in self.seen or self.mine(real) or os.path.isdir(real) and not os.path.islink(real):
            return
        self.seen.add(real)
        self.busy = True
        try:
            if os.path.islink(real):
                op = {"op": "file", "path": real, "link": os.readlink(real)}
            elif os.path.exists(real):
                copy = os.path.join(self.root, "files", str(len(self.ops)))
                _ORIG["copy2"](real, copy)
                op = {"op": "file", "path": real, "copy": copy}
            else:
                op = {"op": "file", "path": real, "absent": True}
        finally:
            self.busy = False
        self.add(op)

    def dirs(self, path):
        """Before folders are created: note each one that doesn't exist yet."""
        d, missing = os.path.abspath(os.fsdecode(path)), []
        while d and not os.path.lexists(d) and d != os.path.dirname(d):
            missing.append(d)
            d = os.path.dirname(d)
        for d in reversed(missing):
            if d not in self.seen and not self.mine(d):
                self.seen.add(d)
                self.add({"op": "dir", "path": d})

    def move(self, src, dst):
        self.add({"op": "move", "src": os.path.abspath(os.fsdecode(src)), "dst": os.path.abspath(os.fsdecode(dst))})

    def note(self, op):
        self.add(op)

    def discard(self):
        _ORIG["rmtree"](self.root, ignore_errors=True)


def _journaling():
    return JOURNAL is not None and not JOURNAL.busy


def _j_path(p):
    return isinstance(p, (str, bytes, os.PathLike))


def _jw_open(file, mode="r", *args, **kw):
    if _journaling() and _j_path(file) and any(c in mode for c in "wax+"):
        JOURNAL.file(file)
    return _ORIG["open"](file, mode, *args, **kw)


def _jw_two(name):
    def wrapper(src, dst, *args, **kw):
        if _journaling() and _j_path(src) and _j_path(dst):
            if os.path.isdir(src) and not os.path.islink(src):
                JOURNAL.dirs(os.path.dirname(os.path.abspath(os.fsdecode(dst))))
                JOURNAL.move(src, dst)
            else:
                JOURNAL.file(src)
                JOURNAL.file(dst)
        return _ORIG[name](src, dst, *args, **kw)
    return wrapper


def _jw_one(name):
    def wrapper(path, *args, **kw):
        if _journaling() and _j_path(path):
            JOURNAL.file(path)
        return _ORIG[name](path, *args, **kw)
    return wrapper


def _jw_symlink(src, dst, *args, **kw):
    if _journaling() and _j_path(dst):
        JOURNAL.file(dst)
    return _ORIG["symlink"](src, dst, *args, **kw)


def _jw_mkdirs(name):
    def wrapper(path, *args, **kw):
        if _journaling() and _j_path(path):
            JOURNAL.dirs(path)
        return _ORIG[name](path, *args, **kw)
    return wrapper


def _jw_shmove(src, dst, *args, **kw):
    if _journaling() and _j_path(src) and _j_path(dst):
        real = os.path.join(dst, os.path.basename(os.fsdecode(src))) if os.path.isdir(dst) else dst
        if os.path.isdir(src) and not os.path.islink(src):
            JOURNAL.dirs(os.path.dirname(os.path.abspath(os.fsdecode(real))))
            JOURNAL.move(src, real)
            JOURNAL.busy = True              # the move's own renames are covered by the record above
            try:
                return _ORIG["shmove"](src, dst, *args, **kw)
            finally:
                JOURNAL.busy = False
        JOURNAL.file(src)
        JOURNAL.file(real)
    return _ORIG["shmove"](src, dst, *args, **kw)


def journal_start(label):
    """Record every change this process makes from now on (see Journal)."""
    global JOURNAL
    import builtins
    _ORIG.update({"open": builtins.open, "replace": os.replace, "rename": os.rename, "remove": os.remove,
                  "unlink": os.unlink, "symlink": os.symlink, "chmod": os.chmod, "makedirs": os.makedirs,
                  "mkdir": os.mkdir, "copy2": shutil.copy2, "shmove": shutil.move, "rmtree": shutil.rmtree})
    JOURNAL = Journal(label)
    builtins.open = _jw_open
    os.replace, os.rename = _jw_two("replace"), _jw_two("rename")
    os.remove, os.unlink, os.chmod = _jw_one("remove"), _jw_one("unlink"), _jw_one("chmod")
    os.symlink = _jw_symlink
    os.makedirs, os.mkdir = _jw_mkdirs("makedirs"), _jw_mkdirs("mkdir")
    shutil.move = _jw_shmove
    signal.signal(signal.SIGTERM, _on_cancel)
    return JOURNAL


def journal_stop(keep):
    """Stop recording; keep the journal (cancelled: undo-step uses it) or drop it (step finished)."""
    global JOURNAL
    import builtins
    if not _ORIG:
        return
    signal.signal(signal.SIGTERM, signal.SIG_DFL)
    builtins.open = _ORIG["open"]
    os.replace, os.rename, os.remove, os.unlink = _ORIG["replace"], _ORIG["rename"], _ORIG["remove"], _ORIG["unlink"]
    os.symlink, os.chmod, os.makedirs, os.mkdir = _ORIG["symlink"], _ORIG["chmod"], _ORIG["makedirs"], _ORIG["mkdir"]
    shutil.move = _ORIG["shmove"]
    if JOURNAL and not keep:
        JOURNAL.discard()
    JOURNAL = None


def _on_cancel(signum, frame):
    if JOURNAL is not None and JOURNAL.critical_reason:
        JOURNAL.cancel_pending = True     # finish the part that must not be cut short first
        return
    raise SystemExit(CANCEL_RC)


class critical:
    """A part that must not be cut short (writing /boot): Cancel waits for it to finish."""

    def __init__(self, reason):
        self.reason = reason

    def __enter__(self):
        if JOURNAL is not None:
            JOURNAL.critical_reason = self.reason
            with _ORIG["open"](os.path.join(JOURNAL.root, "critical"), "w") as fh:
                fh.write(self.reason)
        return self

    def __exit__(self, et, ev, tb):
        if JOURNAL is not None:
            JOURNAL.critical_reason = None
            try:
                _ORIG["remove"](os.path.join(JOURNAL.root, "critical"))
            except OSError:
                pass
            if JOURNAL.cancel_pending and et is None:
                raise SystemExit(CANCEL_RC)
        return False


def _test_pause(point):
    """Tests only: V3M_TEST_PAUSE=point:seconds holds a step at that point so it can be cancelled there."""
    spec = os.environ.get("V3M_TEST_PAUSE", "")
    if spec.split(":")[0] == point:
        import time
        time.sleep(float(spec.split(":")[1]))


def journal_note(op):
    if JOURNAL is not None:
        JOURNAL.note(op)


def journal_pending():
    """The journal of a step that was cancelled or cut off, if one is waiting to be undone."""
    return load_json(JOURNAL_DIR + "/journal.json")


def journal_critical():
    return read(JOURNAL_DIR + "/critical").strip()


def _undo_safe_tree(path):
    """Only folders a step created, and never a top-level one, are removed as a whole."""
    rel = UNP(path)
    parts = [x for x in rel.split("/") if x]
    return len(parts) >= 3 and parts[0] in ("userdata", "media", "tmp", "boot") and \
        not (parts[0] == "boot" and len(parts) < 3)


def _on_boot(path):
    return UNP(path) == "/boot" or UNP(path).startswith("/boot/")


def undo_op(op, restart):
    kind = op["op"]
    if kind == "file":
        path = op["path"]
        boot = _on_boot(path)
        if boot:
            remount_boot(True)
        try:
            if op.get("absent"):
                if os.path.lexists(path) and not (os.path.isdir(path) and not os.path.islink(path)):
                    os.remove(path)
                return
            if os.path.lexists(path) and not (os.path.isdir(path) and not os.path.islink(path)):
                os.remove(path)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            if "link" in op:
                os.symlink(op["link"], path)
            else:
                shutil.copy2(op["copy"], path)
        finally:
            if boot:
                remount_boot(False)
    elif kind == "dir":
        path = op["path"]
        if os.path.isdir(path) and not os.path.islink(path):
            if _undo_safe_tree(path):
                shutil.rmtree(path)
            else:
                os.rmdir(path)
    elif kind == "move":
        if os.path.lexists(op["dst"]) and not os.path.lexists(op["src"]):
            shutil.move(op["dst"], op["src"])
    elif kind == "service_started":
        script = "/userdata/system/services/" + op["name"]
        if os.path.exists(P(script)):
            run([script, "stop"], timeout=20)
        if op.get("was_enabled"):
            restart.append(op["name"])
    elif kind == "mounted":
        run(["umount", op["path"]], timeout=30)
    elif kind == "boot_replaced":
        say("  writing the previous boot partition back from %s ..." % op["backup"])
        if not restore_boot(op["backup"]):
            raise RuntimeError("could not restore the boot partition; use: rollback")


def cmd_undo_step(args):
    j = journal_pending()
    if not j:
        say("Nothing to undo.")
        return 0
    if getattr(args, "discard", False):
        shutil.rmtree(P(JOURNAL_DIR), ignore_errors=True)
        say("Kept the changes of '%s'; its undo record was removed." % j.get("label"))
        return 0
    ops = j.get("ops", [])
    head("Putting back what '%s' changed (%d records)" % (j.get("label"), len(ops)))
    restart, errors = [], []
    for op in reversed(ops):
        try:
            undo_op(op, restart)
        except Exception as e:  # keep going: everything else should still go back
            errors.append("%s %s: %s" % (op["op"], UNP(op.get("path") or op.get("dst") or op.get("name") or ""), e))
    for svc in restart:
        run(["/userdata/system/services/" + svc, "start"], timeout=20)
    if errors:
        say("Could not put back:")
        for e in errors:
            say("  ! " + e)
        say("\nThe undo record is kept; run this again (undo-step) after fixing the cause.")
        return 1
    shutil.rmtree(P(JOURNAL_DIR), ignore_errors=True)
    say("Everything this step changed is back as it was before it started.")
    return 0


# --------------------------------------------------------------------------
# discovery
# --------------------------------------------------------------------------
def system_info():
    conf = conf_parse()
    return {
        "board": read(BOARD_FILE).strip() or "unknown",
        "version": read("/usr/share/batocera/batocera.version").strip() or "unknown",
        "arch": read("/usr/share/batocera/batocera.arch").strip() or "unknown",
        "kernel": os.uname().release if not TEST_MODE() else "test",
        "hostname": socket.gethostname(),
        "update_type": conf.get("updates.type", "stable"),
        "update_url": conf.get("updates.url", DEFAULT_UPDATE_URL),
    }


def cpu_info():
    model, flags = "unknown", set()
    for line in read("/proc/cpuinfo").splitlines():
        if line.startswith("model name") and model == "unknown":
            model = line.split(":", 1)[1].strip()
        if line.startswith("flags"):
            flags = set(line.split(":", 1)[1].split())
            break
    missing = [f for f in V2_FLAGS + V3_FLAGS if f not in flags]
    if not any(a in flags for a in LZCNT_ALIASES):
        missing.append("lzcnt/abm")
    official = "unavailable"
    if which("batocera-x64-compatibility"):
        rc, _ = run(["batocera-x64-compatibility"])
        official = "pass" if rc == 0 else "fail"
    return {"model": model, "v3_flags_ok": not missing, "missing_flags": missing,
            "official_check": official}


def gpu_info():
    gpus = []
    base = P("/sys/class/drm")
    if os.path.isdir(base):
        for n in sorted(os.listdir(base)):
            if not re.fullmatch(r"card\d+", n):
                continue
            vend = read("/sys/class/drm/%s/device/vendor" % n).strip()
            drv = ""
            link = P("/sys/class/drm/%s/device/driver" % n)
            if os.path.islink(link):
                drv = os.path.basename(os.readlink(link))
            gpus.append({"card": n, "vendor_id": vend, "vendor": GPU_VENDORS.get(vend, "other"),
                         "driver": drv})
    return gpus


def connector_type(name):
    """HDMI-A-0 -> HDMI-A, DisplayPort-1 -> DP, eDP-1 -> eDP (Xorg and DRM spellings)."""
    t = name.rsplit("-", 1)[0] if re.search(r"-\d+$", name) else name
    return {"DisplayPort": "DP", "HDMI": "HDMI-A", "DVI": "DVI-D"}.get(t, t)


def display_info():
    conns = []
    base = P("/sys/class/drm")
    if os.path.isdir(base):
        for n in sorted(os.listdir(base)):
            m = re.fullmatch(r"card\d+-(.+)", n)
            if not m:
                continue
            modes = [x for x in read("/sys/class/drm/%s/modes" % n).split() if x]
            conns.append({"name": m.group(1), "type": connector_type(m.group(1)),
                          "status": read("/sys/class/drm/%s/status" % n).strip() or "unknown",
                          "modes": modes[:40]})
    conf = conf_parse()
    keys = {k: v for k, v in conf.items()
            if k.startswith("global.videooutput") or k.startswith("es.resolution")
            or k.startswith("global.videomode") or k.startswith("display.")
            or k.startswith("es.screen") or k.startswith("global.screen")}
    resolution_tool = None
    if which("batocera-resolution"):
        rc, out = run(["batocera-resolution", "listOutputs"], timeout=20)
        resolution_tool = {"listOutputs": out.split() if rc == 0 else [],
                           "currentResolution": run(["batocera-resolution", "currentResolution"], 20)[1].strip()}
    return {"connectors": conns, "conf_keys": keys, "batocera_resolution": resolution_tool}


def boot_info():
    ov = P(OVERLAY)
    overlay = {"present": os.path.exists(ov)}
    if overlay["present"]:
        overlay["size"] = os.path.getsize(ov)
        overlay["sha256"] = sha256_file(ov)
        overlay["files"] = overlay_listing()
    bconf = {}
    for line in read(BOOT_CONF).splitlines():
        s = line.strip()
        if s and not s.startswith("#") and "=" in s:
            k, v = s.split("=", 1)
            k = k.strip()
            bconf[k] = "<redacted>" if SECRET_KEY_RE.search(k) else v.strip()
    free = None
    if os.path.isdir(P("/boot")):
        try:
            free = shutil.disk_usage(P("/boot")).free
        except OSError:
            pass
    return {"overlay": overlay, "boot_conf": bconf, "boot_free": free}


def overlay_listing():
    """List files inside the overlay image (squashfs via unsquashfs, else ext via debugfs)."""
    if which("unsquashfs"):
        rc, out = run(["unsquashfs", "-l", "-d", "", P(OVERLAY)], timeout=60)
        if rc == 0:
            return [l.strip() for l in out.splitlines() if l.strip().startswith("/")][:2000]
    if not TEST_MODE() and os.geteuid() == 0:
        mnt = "/tmp/v3m-overlay-ro"
        os.makedirs(mnt, exist_ok=True)
        rc, _ = run(["mount", "-o", "loop,ro", P(OVERLAY), mnt], timeout=30)
        if rc == 0:
            try:
                files = []
                for dp, dns, fns in os.walk(mnt):
                    for fn in fns:
                        files.append("/" + os.path.relpath(os.path.join(dp, fn), mnt))
                return sorted(files)[:5000]
            finally:
                run(["umount", mnt], timeout=30)
    return ["(contents not listable here: mount it read-only to inspect)"]


def userdata_info():
    try:
        du = shutil.disk_usage(P("/userdata"))
        return {"free": du.free, "total": du.total}
    except OSError:
        return {"free": None, "total": None}


def services_info():
    conf = conf_parse()
    avail = set()
    for d in ("/usr/share/batocera/services", "/userdata/system/services"):
        if os.path.isdir(P(d)):
            for n in os.listdir(P(d)):
                if not n.startswith("."):
                    avail.add(n)
    enabled = conf.get("system.services", "").split()
    user = sorted(os.listdir(P("/userdata/system/services"))) if os.path.isdir(
        P("/userdata/system/services")) else []
    return {"available": sorted(avail), "enabled": enabled, "user_services": user,
            "custom_sh": os.path.exists(P("/userdata/system/custom.sh"))}


def skip_name(n):
    return n in SKIP_DIRS or any(fnmatch.fnmatch(n, g) for g in SCAN_SKIP_GLOBS)


EXTRA_EXCLUDES = []  # from plugins' exclude_paths


def excluded(path):
    u = UNP(path)
    return any(u == e or u.startswith(e.rstrip("/") + "/") for e in EXTRA_EXCLUDES)


def walk(root, follow=False):
    rp = P(root)
    if not os.path.exists(rp) or excluded(rp):
        return
    if os.path.isfile(rp):
        yield rp
        return
    for dp, dns, fns in os.walk(rp, followlinks=follow):
        dns[:] = [d for d in dns if not skip_name(d) and not excluded(os.path.join(dp, d))]
        for fn in fns:
            if not skip_name(fn):
                yield os.path.join(dp, fn)


def is_text_candidate(path):
    ext = os.path.splitext(path)[1].lower()
    try:
        st = os.lstat(path)
    except OSError:
        return False
    if not os.path.isfile(path) or os.path.islink(path) or st.st_size > 1024 * 1024:
        return False
    if ext not in TEXT_EXT and not (st.st_mode & 0o111):
        return False
    try:
        with open(path, "rb") as f:
            chunk = f.read(8192)
    except OSError:
        return False
    return b"\0" not in chunk


SCRIPT_ROOTS = ["/userdata/system/services", "/userdata/system/scripts", "/userdata/system/custom.sh",
                "/userdata/system/bin", "/userdata/system/add-ons", "/userdata/roms/ports",
                "/userdata/system/configs/emulationstation", "/userdata/system/configs/evmapy",
                "/userdata/system/udev", "/userdata/system/.config/autostart",
                "/userdata/system/configs/labwc"]


def x11_scan(roots):
    hits, seen = [], set()
    for root in roots:
        for f in walk(root):
            if f in seen or not is_text_candidate(f):
                continue
            seen.add(f)
            try:
                with open(f, errors="replace") as fh:
                    for i, line in enumerate(fh, 1):
                        if line.lstrip().startswith("#") and not f.endswith(".desktop"):
                            continue
                        for rx, why in X11_RE:
                            if rx.search(line):
                                hits.append({"file": UNP(f), "line": i, "text": line.strip()[:160],
                                             "why": why})
                                break
            except OSError:
                pass
    return hits


ELF_ROOTS = ["/userdata/system", "/userdata/roms/ports", "/userdata/bin"]


def elf_kind(path):
    try:
        with open(path, "rb") as f:
            h = f.read(20)
    except OSError:
        return None
    if len(h) < 20 or h[:4] != b"\x7fELF":
        return None
    cls = {1: "32", 2: "64"}.get(h[4], "?")
    machine = int.from_bytes(h[18:20], "little")
    return {"class": cls, "machine": {62: "x86_64", 3: "i386", 183: "aarch64"}.get(machine, str(machine))}


def find_ld_so():
    for c in ("/lib64/ld-linux-x86-64.so.2", "/lib/ld-linux-x86-64.so.2", "/usr/lib/ld-linux-x86-64.so.2"):
        if os.path.exists(P(c)):
            return P(c)
    return None


# paths that belong to self-contained runtimes (Steam/UMU containers, AppImage extracts, add-on
# rootfs trees): they load their own libraries, so "missing" against the host means nothing
RUNTIME_RE = re.compile(r"(steamrt|steam-runtime|pressure-vessel|_platform_|/umu/|/\.local/share/Steam/|"
                        r"/lutris/runtime/|-extracted/|squashfs-root/|/runtime/usr/lib/|/\.dep/|/rootfs/|"
                        r"/wine/|/proton|/dist/lib)")


def bundled_dirs(path):
    """Library folders an app most likely brings along (what its launcher puts on LD_LIBRARY_PATH)."""
    d = os.path.dirname(path)
    cands = [d, d + "/lib", d + "/lib64", d + "/../lib", d + "/../lib64", d + "/runtime/usr/lib",
             d + "/../runtime/usr/lib", d + "/usr/lib", d + "/shared/lib", d + "/../shared/lib"]
    a = d
    for _ in range(4):
        a = os.path.dirname(a)
        if not a or a == "/":
            break
        cands += [a + "/lib", a + "/usr/lib", a + "/shared/lib", a + "/runtime/usr/lib"]
    out = []
    for c in cands:
        c = os.path.normpath(c)
        if os.path.isdir(c) and c not in out:
            out.append(c)
    return out


def missing_libs(path, extra_dirs=None):
    """Ask the system dynamic loader (no code from the binary runs)."""
    ld = find_ld_so()
    if not ld or TEST_MODE():
        return None
    try:
        # same mechanism as ldd: trace mode lists every dependency and does not run the program
        env = dict(os.environ, LD_TRACE_LOADED_OBJECTS="1")
        env.pop("LD_PRELOAD", None)
        if extra_dirs:
            env["LD_LIBRARY_PATH"] = ":".join(extra_dirs + [env.get("LD_LIBRARY_PATH", "")]).rstrip(":")
        r = subprocess.run([ld, path], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           timeout=20, env=env)
    except (OSError, subprocess.TimeoutExpired):
        return None
    out = r.stdout.decode(errors="replace")
    if "not a dynamic executable" in out or "statically linked" in out:
        return []
    miss = {l.split("=>")[0].strip() for l in out.splitlines() if "not found" in l}
    miss |= set(re.findall(r"error while loading shared libraries: ([^:]+):", out))
    return sorted(miss)


def elf_scan(roots, extra=()):
    elfs, appimages = [], []
    seen = set()
    for root in list(roots) + list(extra):
        for f in walk(root):
            if f in seen or os.path.islink(f) or not os.path.isfile(f):
                continue
            seen.add(f)
            if f.lower().endswith(".appimage"):
                appimages.append({"path": UNP(f), "size": os.path.getsize(f)})
                continue
            k = elf_kind(f)
            if not k:
                continue
            st = os.stat(f)
            miss = missing_libs(f) if k["machine"] == "x86_64" else None
            if miss:  # give it the libraries it ships with before calling anything missing
                miss = missing_libs(f, bundled_dirs(f))
            elfs.append({"path": UNP(f), "size": st.st_size, "mtime": int(st.st_mtime),
                         "class": k["class"], "machine": k["machine"], "missing_libs": miss,
                         "bundled_runtime": bool(RUNTIME_RE.search(UNP(f)))})
    return elfs, appimages


HOOK_DIR = "/userdata/system/scripts"
BG_LINE_RE = re.compile(r"(?<![&|])&\s*(#.*)?$")
FD_CLOSE = " ".join("%d>&-" % n for n in range(3, 21))
XORG_AUTH_RE = re.compile(r"/usr/bin/X :0[^\n]*-auth|X :0 -auth")
NONROOT_RE = re.compile(r"\bsu\s+(-s\s+\S+\s+)?(-c\s+)?['\"]?[a-z_][a-z0-9_-]*\b(?<!root)|\bsudo\s+-u\s+\S+|\brunuser\b")


def is_backup_name(n):
    return any(fnmatch.fnmatch(n, g) for g in ["*backup*", "*Backup*", "*BACKUP*", "*.bak", "*.bak-*",
                                               "*.before-*", "*.orig", "*.old", "*-old", "*.pre-*",
                                               "*KNOWN-GOOD*", "*~"])


def hook_scan():
    """Game-event hooks: ES/batocera-launch run every file in the scripts folder and wait on a
    status pipe; a background child that inherits that pipe makes the launch hang."""
    bg, backups = [], []
    d = P(HOOK_DIR)
    if not os.path.isdir(d):
        return bg, backups
    for n in sorted(os.listdir(d)):
        fp = os.path.join(d, n)
        if not os.path.isfile(fp):
            continue
        if is_backup_name(n):
            backups.append(HOOK_DIR + "/" + n)
            continue
        if not is_text_candidate(fp):
            continue
        heredoc = None
        for i, line in enumerate(read(UNP(fp)).splitlines(), 1):
            st = line.strip()
            if heredoc:
                if st == heredoc:
                    heredoc = None
                continue
            m = re.search(r"<<-?\s*['\"]?([A-Za-z_][A-Za-z0-9_]*)['\"]?", line)
            if m:
                heredoc = m.group(1)
            if not st or st.startswith("#") or not BG_LINE_RE.search(line):
                continue
            if re.search(r"(^|\s)([3-9]|[1-9][0-9])>&-", line):
                continue  # already closes inherited descriptors
            bg.append({"file": HOOK_DIR + "/" + n, "line": i, "text": st[:160]})
    return bg, backups


def x11_compat_scan(roots):
    """Xorg-only assumptions that break X11 apps under Xwayland on the v3 image."""
    xauth, nonroot = [], []
    seen = set()
    for root in roots:
        for f in walk(root):
            if f in seen or not is_text_candidate(f):
                continue
            seen.add(f)
            txt = read(UNP(f))
            if "DISPLAY" not in txt and "-auth" not in txt:
                continue
            uses_x = "DISPLAY" in txt
            for i, line in enumerate(txt.splitlines(), 1):
                if line.lstrip().startswith("#"):
                    continue
                if XORG_AUTH_RE.search(line):
                    xauth.append({"file": UNP(f), "line": i, "text": line.strip()[:160]})
                if uses_x and NONROOT_RE.search(line):
                    nonroot.append({"file": UNP(f), "line": i, "text": line.strip()[:160]})
    return xauth, nonroot


def bua_info():
    addons = P("/userdata/system/add-ons")
    apps = sorted(os.listdir(addons)) if os.path.isdir(addons) else []
    launchers = []
    ports = P("/userdata/roms/ports")
    if os.path.isdir(ports):
        for n in sorted(os.listdir(ports)):
            fp = os.path.join(ports, n)
            if n.endswith(".sh") and "add-ons" in read(UNP(fp))[:20000]:
                launchers.append(UNP(fp))
    return {"present": bool(apps) or bool(launchers), "apps": apps, "launchers": launchers}


def es_custom_info():
    d = "/userdata/system/configs/emulationstation"
    out = []
    if os.path.isdir(P(d)):
        for n in sorted(os.listdir(P(d))):
            if re.match(r"(es_systems_.*\.cfg|es_features.*\.cfg|es_input\.cfg|es_settings\.cfg|"
                        r"es_systems\.cfg|.*\.xml)$", n):
                out.append(d + "/" + n)
    return out


def link_resolves(fp, depth=0):
    """os.path.exists for a link, but absolute targets are resolved inside ROOT (test trees)."""
    if ROOT == "/":
        return os.path.exists(fp)
    if depth > 20 or not os.path.islink(fp):
        return os.path.exists(fp)
    t = os.readlink(fp)
    nxt = P(t) if os.path.isabs(t) else os.path.join(os.path.dirname(fp), t)
    return link_resolves(nxt, depth + 1)


def symlink_info():
    links = []
    for root in ("/userdata/roms", "/userdata/bios", "/userdata/saves", "/userdata/system"):
        rp = P(root)
        if not os.path.isdir(rp):
            continue
        for dp, dns, fns in os.walk(rp, followlinks=False):
            dns[:] = [d for d in dns if d not in SKIP_DIRS]
            depth = dp[len(rp):].count(os.sep)
            for n in dns + fns:
                fp = os.path.join(dp, n)
                if os.path.islink(fp):
                    links.append({"link": UNP(fp), "target": os.readlink(fp),
                                  "resolves": link_resolves(fp)})
            if depth >= 2:  # top levels are what matter (system dirs -> other drives)
                dns[:] = []
    return links


def mounts_info():
    by_uuid = {}
    d = P("/dev/disk/by-uuid")
    if os.path.isdir(d):
        for u in os.listdir(d):
            try:
                by_uuid[os.path.realpath(os.path.join(d, u))] = u
            except OSError:
                pass
    out = []
    for line in read("/proc/mounts").splitlines():
        parts = line.split()
        if len(parts) < 3:
            continue
        dev, mnt, fs = parts[0], parts[1].replace("\\040", " "), parts[2]
        if not (mnt.startswith("/media") or mnt.startswith("/userdata") or mnt == "/boot"):
            continue
        out.append({"device": dev, "mountpoint": mnt, "fstype": fs,
                    "uuid": by_uuid.get(P(dev) if ROOT != "/" else dev, by_uuid.get(dev))})
    return out


def udev_info():
    out = []
    for root in ("/userdata/system/udev", "/userdata/system/udev/rules.d"):
        if os.path.isdir(P(root)):
            out += [root + "/" + n for n in sorted(os.listdir(P(root))) if n.endswith(".rules")]
    return sorted(set(out))


# --------------------------------------------------------------------------
# integrations (JSON files in /userdata/system/v3-migrate.d)
# --------------------------------------------------------------------------
PLUGIN_TEMPLATE = {
    "name": "my-custom-thing",
    "description": "What this is and why it needs special care",
    "backup_paths": ["/userdata/system/my-custom-thing"],
    "binaries": ["/userdata/system/my-custom-thing/bin/mytool"],
    "scan_paths": ["/userdata/system/my-custom-thing"],
    "required_paths": ["/userdata/system/my-custom-thing/bin/mytool"],
    "services": [],
    "exclude_paths": [],
    "pre_migrate": [],
    "post_integrate": [],
    "verify": [{"name": "binary starts", "cmd": "/userdata/system/my-custom-thing/bin/mytool --version",
                "expect_rc": 0, "timeout": 20}],
}

PLUGIN_KEYS = set(PLUGIN_TEMPLATE)


def load_plugins():
    plugins, errors = [], []
    d = P(PLUGIN_DIR)
    if not os.path.isdir(d):
        return plugins, errors
    for n in sorted(os.listdir(d)):
        if not n.endswith(".json"):
            continue
        try:
            with open(os.path.join(d, n)) as f:
                p = json.load(f)
            if not isinstance(p, dict) or "name" not in p:
                raise ValueError("missing 'name'")
            unknown = set(p) - PLUGIN_KEYS
            if unknown:
                raise ValueError("unknown keys: %s" % ", ".join(sorted(unknown)))
            for k in PLUGIN_KEYS - {"name", "description"}:
                p.setdefault(k, [])
            p["_file"] = PLUGIN_DIR + "/" + n
            plugins.append(p)
        except (OSError, ValueError) as e:
            errors.append("%s: %s" % (n, e))
    return plugins, errors


def run_plugin_cmds(plugins, key, phase, backup_dir, apply):
    results = []
    for p in plugins:
        for cmd in p.get(key, []):
            if not apply:
                results.append({"plugin": p["name"], "cmd": cmd, "rc": None, "out": "(planned)"})
                continue
            env = dict(os.environ, V3M_PHASE=phase, V3M_BACKUP=backup_dir or "",
                       V3M_PLUGIN=p["name"])
            rc, out = run(["/bin/bash", "-c", cmd], timeout=600, env=env)
            results.append({"plugin": p["name"], "cmd": cmd, "rc": rc, "out": out[-2000:]})
    return results


def run_plugin_verify(plugins):
    results = []
    for p in plugins:
        for path in p.get("required_paths", []):
            results.append({"plugin": p["name"], "check": "exists " + path,
                            "ok": os.path.exists(P(path))})
        for b in p.get("binaries", []):
            if os.path.exists(P(b)):
                ml = missing_libs(P(b))
                results.append({"plugin": p["name"], "check": "libs " + b,
                                "ok": not ml, "detail": ", ".join(ml or [])})
        for v in p.get("verify", []):
            rc, out = run(["/bin/bash", "-c", v["cmd"]], timeout=v.get("timeout", 30))
            ok = None if TEST_MODE() else rc == v.get("expect_rc", 0)
            results.append({"plugin": p["name"], "check": v.get("name", v["cmd"]), "ok": ok,
                            "detail": out.strip()[-300:]})
    return results


# --------------------------------------------------------------------------
# audit
# --------------------------------------------------------------------------
def finding(lst, sev, fid, title, detail="", action=""):
    lst.append({"severity": sev, "id": fid, "title": title, "detail": detail, "action": action})


def do_audit(quiet=False, light=False):
    plugins, perrors = load_plugins()
    EXTRA_EXCLUDES[:] = [x for p in plugins for x in p.get("exclude_paths", [])]
    extra_scan = [x for p in plugins for x in p.get("scan_paths", [])]
    extra_bins = [x for p in plugins for x in p.get("binaries", [])]

    if not quiet:
        say("Scanning (read-only)...")
    a = {
        "tool_version": VERSION, "time": now(),
        "system": system_info(), "cpu": cpu_info(), "gpus": gpu_info(),
        "display": display_info(), "boot": boot_info(), "userdata": userdata_info(),
        "services": services_info(), "bua": bua_info(), "es_custom": es_custom_info(),
        "symlinks": symlink_info(), "mounts": mounts_info(), "udev": udev_info(),
        "plugins": [{"name": p["name"], "file": p["_file"]} for p in plugins],
        "plugin_errors": perrors,
    }
    a["x11_refs"] = x11_scan(SCRIPT_ROOTS + extra_scan)
    a["hook_bg"], a["hook_backups"] = hook_scan()
    a["xorg_auth"], a["nonroot_x"] = x11_compat_scan(SCRIPT_ROOTS + [HOOK_DIR, "/userdata/system/hooks-guarded"]
                                                     + extra_scan)
    a["xwayland_access"] = xwayland_access_state()
    # light: skip the slow library check (fix doesn't need it)
    a["elfs"], a["appimages"] = ([], []) if light else elf_scan(ELF_ROOTS, extra_bins)

    f = []
    s, cpu = a["system"], a["cpu"]
    if s["board"] not in (V1_BOARD, V3_BOARD):
        finding(f, "blocker", "board", "Board is '%s', not x86_64" % s["board"],
                "x86-64-v3 migration only exists for the PC x86_64 image.",
                "Nothing to do on this device.")
    elif s["board"] == V3_BOARD:
        finding(f, "info", "already-v3", "Already running the x86-64-v3 image",
                action="Run `integrate` to check everything carried over.")
    if not cpu["v3_flags_ok"]:
        finding(f, "blocker", "cpu", "CPU lacks x86-64-v3 instructions",
                "Missing: " + ", ".join(cpu["missing_flags"]),
                "Stay on the x86_64 image; v3 binaries would crash with illegal-instruction.")
    if cpu["official_check"] == "fail":
        finding(f, "blocker", "cpu-official", "batocera-x64-compatibility says this hardware is not eligible",
                action="Stay on x86_64 (this is Batocera's own check).")
    vendors = {g["vendor"] for g in a["gpus"]}
    if "nvidia" in vendors:
        finding(f, "critical" if vendors <= {"nvidia"} else "warn", "nvidia",
                "NVIDIA GPU present",
                "Batocera marks NVIDIA on the v3/Wayland image as experimental; desktop NVIDIA users "
                "are told to stay on x86_64/Xorg.",
                "Only migrate with --allow-nvidia and keep the rollback backup.")
    nv = a["boot"]["boot_conf"].get("nvidia-driver")
    if nv and nv != "false":
        finding(f, "warn", "nvidia-boot", "batocera-boot.conf forces nvidia-driver=%s" % nv,
                action="Check the setting still exists on v3 after migrating.")
    if a["boot"]["overlay"]["present"]:
        finding(f, "critical", "overlay", "A root-filesystem overlay is installed (%s)"
                % human(a["boot"]["overlay"]["size"]),
                "The overlay holds files you changed in the read-only system (custom binaries, patched "
                "EmulationStation, configgen edits...). It was built against the x86_64 image and must "
                "not be layered onto v3.",
                "`migrate` parks it in the backup after the upgrade succeeds. Rebuild each item for "
                "x86-64-v3 and re-save it with batocera-save-overlay.")
    if a["services"]["custom_sh"]:
        finding(f, "warn", "custom-sh", "custom.sh still exists",
                "custom.sh is deprecated (converted once into a service since v43).",
                "Move its logic into a service under /userdata/system/services.")
    if a["x11_refs"]:
        files = sorted({h["file"] for h in a["x11_refs"]})
        finding(f, "warn", "x11", "%d X11-only references in %d files" % (len(a["x11_refs"]), len(files)),
                "\n".join(files[:30]),
                "Port these (see report). Services that contain them are parked during migration.")
    vo = {k: v for k, v in a["display"]["conf_keys"].items() if k.startswith("global.videooutput")}
    if vo:
        finding(f, "warn", "videooutput", "Display output pinned in batocera.conf: " +
                ", ".join("%s=%s" % kv for kv in vo.items()),
                "Xorg and the DRM/Wayland stack can name the same port differently "
                "(e.g. AMD under Xorg uses HDMI-A-0 / DisplayPort-0).",
                "`integrate` re-maps the name if it no longer exists.")
    if a["display"]["conf_keys"].get("es.resolution") or a["display"]["conf_keys"].get("global.videomode"):
        finding(f, "info", "resolution", "Custom resolution set",
                ", ".join("%s=%s" % (k, v) for k, v in a["display"]["conf_keys"].items()
                          if k in ("es.resolution", "global.videomode")),
                "`integrate` checks the mode is still offered after migrating.")
    broken = [e for e in a["elfs"] if e.get("missing_libs")]
    if broken:
        finding(f, "info", "elf-baseline", "%d custom binaries already have missing libraries" % len(broken),
                "\n".join(e["path"] for e in broken[:20]),
                "Usually bundled libraries found at run time via LD_LIBRARY_PATH. Recorded as a baseline, "
                "so integrate only reports NEW breakage.")
    if a["elfs"]:
        finding(f, "info", "elfs", "%d custom ELF binaries/libraries in /userdata" % len(a["elfs"]),
                action="Re-checked against the v3 libraries after migrating.")
    if a["bua"]["present"]:
        finding(f, "info", "bua", "Batocera Unofficial Add-ons found: %d apps" % len(a["bua"]["apps"]),
                ", ".join(a["bua"]["apps"][:40]),
                "AppImage/Flatpak-style apps bundle their libraries and usually survive; launchers are "
                "scanned for X11-only flags.")
    dangling = [l for l in a["symlinks"] if not l["resolves"]]
    if dangling:
        finding(f, "warn", "symlinks", "%d symlinks already dangling" % len(dangling),
                "\n".join("%s -> %s" % (l["link"], l["target"]) for l in dangling[:20]),
                "Mount the target drive before backing up, or the backup records them as broken.")
    ext = [m for m in a["mounts"] if m["mountpoint"].startswith("/media")]
    if ext:
        finding(f, "info", "mounts", "%d extra drives mounted" % len(ext),
                "\n".join("%s on %s (%s)" % (m["device"], m["mountpoint"], m["fstype"]) for m in ext),
                "integrate checks each one (by UUID) is back.")
    if a["hook_bg"]:
        finding(f, "critical", "hook-bg", "%d game hooks start background programs that can hang every launch"
                % len(a["hook_bg"]),
                "\n".join("%s:%d  %s" % (h["file"], h["line"], h["text"]) for h in a["hook_bg"][:20]),
                "The launcher waits on a status pipe the background program inherits (seen on v3 as "
                "'game hangs on the launch screen until I kill X'). Run `fix --apply hooks`.")
    hg = hook_guard_state()
    if hg["direct_hooks"] and not hg["installed"]:
        finding(f, "warn" if a["system"]["board"] != V3_BOARD else "critical", "hook-guard",
                "%d game hooks run unguarded" % len(hg["direct_hooks"]), "\n".join(hg["direct_hooks"]),
                "A helper a hook starts can hold the launch open on v3 (seen with exit-hotkey watchers even "
                "with pipes closed). Run `fix --apply hook-guard` (undo: `fix --apply hook-unguard`).")
    if a["hook_backups"]:
        finding(f, "warn", "hook-backups", "%d backup copies in the scripts folder run on every game start"
                % len(a["hook_backups"]), "\n".join(a["hook_backups"]),
                "Batocera runs every file there. Run `fix --apply hook-backups` to move them out.")
    if a["xorg_auth"]:
        finding(f, "warn", "xorg-auth", "%d scripts look for the Xorg -auth file" % len(a["xorg_auth"]),
                "\n".join("%s:%d  %s" % (h["file"], h["line"], h["text"]) for h in a["xorg_auth"][:20]),
                "v3 has no Xorg server, so this finds nothing. If the script stops when it's empty, guard "
                "that part with a board check (x86-64-v3 -> skip). Non-root access comes from "
                "`fix --apply xwayland-access`.")
    if a["nonroot_x"] and not a["xwayland_access"]["enabled"]:
        finding(f, "warn" if a["system"]["board"] != V3_BOARD else "critical", "nonroot-x",
                "%d X11 apps are started as a non-root user" % len(a["nonroot_x"]),
                "\n".join("%s:%d  %s" % (h["file"], h["line"], h["text"]) for h in a["nonroot_x"][:20]),
                "On v3 Xwayland only admits root ('unable to open display' / 'Invalid MIT-MAGIC-COOKIE'). "
                "Run `fix --apply xwayland-access`.")
    uf = a["userdata"]["free"]
    if uf is not None and uf < 4 * 1024 ** 3:
        finding(f, "blocker", "space", "Only %s free on /userdata" % human(uf),
                "The upgrade downloads a ~2-3 GB boot.tar.xz to /userdata/system/upgrade.",
                "Free at least 4 GB.")
    for e in perrors:
        finding(f, "critical", "plugin-error", "Integration file problem", e, "Fix the JSON.")
    if a["es_custom"]:
        finding(f, "info", "es-custom", "%d EmulationStation customisations" % len(a["es_custom"]),
                "\n".join(a["es_custom"]), "Backed up; usually format-compatible across images.")

    f.sort(key=lambda x: SEVERITY_ORDER[x["severity"]])
    a["findings"] = f
    return a


def audit_markdown(a):
    s, cpu = a["system"], a["cpu"]
    L = ["# Batocera x86-64-v3 migration audit", "",
         "- Time: %s  |  tool %s" % (a["time"], a["tool_version"]),
         "- Host: %s  |  board **%s**  |  version %s" % (s["hostname"], s["board"], s["version"]),
         "- CPU: %s  |  v3 flags: %s  |  Batocera check: %s" % (
             cpu["model"], "OK" if cpu["v3_flags_ok"] else "MISSING " + ",".join(cpu["missing_flags"]),
             cpu["official_check"]),
         "- GPUs: " + (", ".join("%s %s (%s)" % (g["card"], g["vendor"], g["driver"]) for g in a["gpus"])
                       or "none detected"),
         "- Update channel: %s" % s["update_type"], ""]
    L.append("## Findings")
    for x in a["findings"]:
        L.append("### [%s] %s" % (x["severity"].upper(), x["title"]))
        if x["detail"]:
            L += ["```", x["detail"], "```"]
        if x["action"]:
            L.append("**Action:** " + x["action"])
        L.append("")
    if a["x11_refs"]:
        by = {}
        for h in a["x11_refs"]:
            by.setdefault(h["file"], []).append(h)
        L.append("## X11-only references (%d in %d files)" % (len(a["x11_refs"]), len(by)))
        for fpath in sorted(by)[:150]:
            hs = by[fpath]
            L.append("- `%s` (%d): %s" % (fpath, len(hs), "; ".join(
                "L%d `%s`" % (h["line"], h["text"][:70].replace("`", "'")) for h in hs[:3])))
        if len(by) > 150:
            L.append("- ... %d more files (see .json)" % (len(by) - 150))
        L.append("")
    L.append("## Inventory")
    L.append("- Services enabled: " + (" ".join(a["services"]["enabled"]) or "none"))
    L.append("- User services: " + (" ".join(a["services"]["user_services"]) or "none"))
    L.append("- BUA apps: " + (", ".join(a["bua"]["apps"]) or "none"))
    L.append("- AppImages: %d, custom ELF files: %d" % (len(a["appimages"]), len(a["elfs"])))
    L.append("- Symlinks tracked: %d, extra mounts: %d, udev rules: %d" % (
        len(a["symlinks"]), len(a["mounts"]), len(a["udev"])))
    L.append("- Integrations loaded: " + (", ".join(p["name"] for p in a["plugins"]) or "none"))
    return "\n".join(L) + "\n"


def print_findings(a):
    for x in a["findings"]:
        say("[%-8s] %s" % (x["severity"].upper(), x["title"]))
        if x["action"]:
            say("           -> " + x["action"])
    if not a["findings"]:
        say("No findings.")


def cmd_audit(args):
    a = do_audit()
    out = P(STATE_DIR + "/audit-%s" % stamp())
    write_json(UNP(out) + ".json", a)
    with open(out + ".md", "w") as fh:
        fh.write(audit_markdown(a))
    head("Audit")
    print_findings(a)
    say("\nFull report: %s.md (and .json)" % UNP(out))
    blockers = [x for x in a["findings"] if x["severity"] == "blocker"]
    return 2 if blockers else 0


# --------------------------------------------------------------------------
# backup
# --------------------------------------------------------------------------
def backup_sets(level, plugins, includes):
    """name -> (list of source roots, excluded basenames/globs)"""
    sys_ex = set(SKIP_DIRS)
    if level == "essential":
        sys_ex.add("add-ons")
    sets = {
        "boot": (["/boot"], set()),
        "system": (["/userdata/system"], sys_ex),
        "saves": (["/userdata/saves"], set()),
        "bios": (["/userdata/bios"], set()),
        "gamelists": (["/userdata/roms"], {"__only_gamelists__"}),
    }
    if level == "full":
        for n in ("screenshots", "themes", "decorations", "cheats", "splash", "music", "library",
                  "kodi"):
            sets[n] = (["/userdata/" + n], set())
    extra = [x for p in plugins for x in p.get("backup_paths", [])] + list(includes)
    if extra:
        sets["extra"] = (extra, set(SKIP_DIRS))
    return sets


def iter_set(roots, excludes):
    only_gl = "__only_gamelists__" in excludes
    for root in roots:
        rp = P(root)
        if not os.path.lexists(rp):
            continue
        if os.path.isfile(rp) or os.path.islink(rp):
            yield rp
            continue
        root_dev = os.lstat(rp).st_dev
        for dp, dns, fns in os.walk(rp, followlinks=False):
            keep = []
            for d in dns:
                full = os.path.join(dp, d)
                try:
                    other_fs = os.lstat(full).st_dev != root_dev
                except OSError:
                    continue
                if other_fs and not only_gl:
                    continue  # bind mounts / docker layers / other drives are not ours to copy
                if d in excludes or any(fnmatch.fnmatch(d, e) for e in excludes if "*" in e):
                    continue
                if os.path.islink(full):
                    if not only_gl:
                        yield full  # store the link itself, never follow onto other drives
                    continue
                keep.append(d)
            dns[:] = keep
            if UNP(dp) == "/userdata/system" and "upgrade" in dns:
                dns.remove("upgrade")
            for fn in fns:
                full = os.path.join(dp, fn)
                if only_gl and fn != "gamelist.xml":
                    continue
                try:
                    if stat.S_ISSOCK(os.lstat(full).st_mode):
                        continue  # sockets can't be stored in tar and are recreated at run time
                except OSError:
                    continue
                yield full


def estimate(paths_iter):
    n = total = 0
    for p in paths_iter:
        try:
            st = os.lstat(p)
        except OSError:
            continue
        n += 1
        if not os.path.islink(p):
            total += st.st_size
    return n, total


def same_device(a, b):
    try:
        return os.stat(a).st_dev == os.stat(b).st_dev
    except OSError:
        return False


def cmd_backup(args):
    plugins, perrors = load_plugins()
    if perrors:
        say("Fix integration files first:\n  " + "\n  ".join(perrors))
        return 2
    dest_root = args.dest
    if not os.path.isdir(P(dest_root)):
        say("Destination %s does not exist (mount your external drive first)." % dest_root)
        return 2
    if same_device(P(dest_root), P("/userdata")) and not args.allow_same_disk:
        say("Destination is on the same disk as /userdata. A dead disk would take the backup with it.\n"
            "Use an external drive, or pass --allow-same-disk if you really mean it.")
        return 2
    sets = backup_sets(args.level, plugins, args.include or [])
    head("Estimating size")
    plan, need = {}, 0
    for name, (roots, ex) in sets.items():
        n, size = estimate(iter_set(roots, ex))
        plan[name] = (n, size)
        need += size
        say("  %-12s %7d files  %s" % (name, n, human(size)))
    free = shutil.disk_usage(P(dest_root)).free
    say("  total %s, destination free %s" % (human(need), human(free)))
    if free < need * 1.1 + 512 * 1024 ** 2:
        say("Not enough free space on the destination.")
        return 2

    bdir = os.path.join(P(dest_root), "batocera-v3-backup-" + stamp())
    os.makedirs(bdir)
    head("Auditing")
    a = do_audit(quiet=True)
    with open(os.path.join(bdir, "audit.json"), "w") as fh:
        json.dump(a, fh, indent=2)
    with open(os.path.join(bdir, "audit.md"), "w") as fh:
        fh.write(audit_markdown(a))
    shutil.copy2(os.path.abspath(__file__), os.path.join(bdir, "batocera_v3_migrate.py"))

    manifest = {"tool_version": VERSION, "time": now(), "level": args.level,
                "board": a["system"]["board"], "version": a["system"]["version"],
                "hostname": a["system"]["hostname"], "archives": {}}
    for name, (roots, ex) in sets.items():
        n, size = plan[name]
        if n == 0:
            continue
        compress = name not in ("boot",)  # boot holds squashfs: already compressed
        fn = name + (".tar.gz" if compress else ".tar")
        path = os.path.join(bdir, fn)
        say("Writing %s (%d files, %s)..." % (fn, n, human(size)))
        count, errors = 0, []
        tar_obj = tarfile.open(path, "w:gz", compresslevel=3) if compress else tarfile.open(path, "w")
        with tar_obj as tar:
            for src in iter_set(roots, ex):
                arc = UNP(src).lstrip("/")
                try:
                    tar.add(src, arcname=arc, recursive=False)
                    count += 1
                except OSError as e:
                    errors.append("%s: %s" % (UNP(src), e))
                if count and count % 5000 == 0:
                    say("   %d / %d" % (count, n))
        digest = sha256_file(path)
        manifest["archives"][fn] = {"set": name, "roots": roots, "files": count, "bytes_in": size,
                                    "bytes_out": os.path.getsize(path), "sha256": digest,
                                    "errors": errors[:200]}
        if errors:
            say("   %d files could not be read (listed in manifest)" % len(errors))
    with open(os.path.join(bdir, "manifest.json"), "w") as fh:
        json.dump(manifest, fh, indent=2)

    head("Verifying")
    ok = verify_backup_dir(bdir)
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    st.update({"backup_dir": UNP(bdir), "backup_time": manifest["time"], "backup_verified": ok,
               "phase": "backed-up" if ok else "backup-failed", "source_board": manifest["board"]})
    write_json(STATE_DIR + "/state.json", st)
    write_json(STATE_DIR + "/baseline-audit.json", a)
    say("\nBackup %s: %s" % ("OK" if ok else "FAILED", UNP(bdir)))
    return 0 if ok else 1


def verify_backup_dir(bdir, deep=True):
    m_path = os.path.join(bdir, "manifest.json")
    try:
        with open(m_path) as fh:
            m = json.load(fh)
    except (OSError, ValueError):
        say("  no readable manifest.json")
        return False
    ok = True
    if "boot.tar" not in m["archives"]:
        say("  WARNING: no boot.tar (rollback not possible from this backup)")
    for fn, info in m["archives"].items():
        p = os.path.join(bdir, fn)
        if not os.path.exists(p):
            say("  %-18s MISSING" % fn)
            ok = False
            continue
        good = sha256_file(p) == info["sha256"]
        members = None
        if good and deep:
            try:
                with tarfile.open(p) as t:
                    members = sum(1 for _ in t)
                good = members == info["files"]
            except (tarfile.TarError, OSError, EOFError):
                good = False
        say("  %-18s %s  (%s files)" % (fn, "ok" if good else "BAD", members if members is not None else "?"))
        ok = ok and good
    return ok


def cmd_verify_backup(args):
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    bdir = args.backup or st.get("backup_dir")
    if not bdir:
        say("No backup recorded; pass --backup DIR.")
        return 2
    ok = verify_backup_dir(P(bdir))
    say("Backup %s" % ("OK" if ok else "FAILED"))
    return 0 if ok else 1


# --------------------------------------------------------------------------
# migrate
# --------------------------------------------------------------------------
def services_to_park(a):
    files = {h["file"] for h in a["x11_refs"]}
    park = []
    for svc in a["services"]["enabled"]:
        if "/userdata/system/services/" + svc in files:
            park.append(svc)
    return park


def service_toggle(name, enable):
    if which("batocera-services"):
        rc, out = run(["batocera-services", "enable" if enable else "disable", name])
        if rc == 0:
            return True
    conf = conf_parse()
    cur = conf.get("system.services", "").split()
    if enable and name not in cur:
        cur.append(name)
    if not enable:
        cur = [x for x in cur if x != name]
    conf_set("system.services", " ".join(cur) if cur else None)
    return True


def url_exists(url):
    if TEST_MODE():
        return True
    try:
        req = urllib.request.Request(url, method="HEAD")
        with urllib.request.urlopen(req, timeout=20) as r:
            return 200 <= r.status < 400
    except Exception:
        return False


def cmd_migrate(args):
    if not TEST_MODE() and os.geteuid() != 0:
        say("Run as root (the default on Batocera).")
        return 2
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    head("Preflight")
    a = do_audit(quiet=True)
    s = a["system"]
    problems = []
    if s["board"] != V1_BOARD:
        problems.append("board is %s, expected %s" % (s["board"], V1_BOARD))
    for x in a["findings"]:
        if x["severity"] == "blocker":
            problems.append(x["title"])
    if any(g["vendor"] == "nvidia" for g in a["gpus"]) and not args.allow_nvidia:
        problems.append("NVIDIA GPU present (experimental on v3); pass --allow-nvidia to override")
    bdir = st.get("backup_dir")
    if not bdir or not os.path.isdir(P(bdir)):
        problems.append("no backup recorded - run `backup --dest /media/<drive>` first")
    elif not args.skip_backup_check:
        say("Re-verifying backup %s ..." % bdir)
        if not verify_backup_dir(P(bdir)):
            problems.append("backup failed verification")
        m = load_json(bdir + "/manifest.json", {}) or {}
        if "boot.tar" not in m.get("archives", {}):
            problems.append("backup has no boot partition copy (needed for rollback)")
    if args.manual:
        if not os.path.exists(P("/userdata/system/upgrade/boot.tar.xz")):
            problems.append("--manual: /userdata/system/upgrade/boot.tar.xz not found")
        url = None
    else:
        base = args.url or "%s/%s/%s/last" % (s["update_url"].rstrip("/"), V3_BOARD,
                                              args.type or s["update_type"])
        url = base.rstrip("/")
        say("Target: %s" % url)
        if not url_exists(url + "/boot.tar.xz"):
            problems.append("cannot reach %s/boot.tar.xz" % url)
    if problems:
        say("Not migrating:\n  - " + "\n  - ".join(problems))
        return 2

    park = services_to_park(a)
    say("Board %s -> %s. Version now %s." % (s["board"], V3_BOARD, s["version"]))
    say("After a successful upgrade, before reboot:")
    if a["boot"]["overlay"]["present"]:
        say("  - move the x86_64 overlay into the backup (it is not v3 compatible)")
    for svc in park:
        say("  - park service '%s' (uses X11-only tools)" % svc)
    say("Integrations pre_migrate commands: %d" % sum(len(p.get("pre_migrate", [])) for p in load_plugins()[0]))
    if not confirm("MIGRATE", "This replaces the system partition with the x86-64-v3 image."):
        say("Stopped. Nothing changed.")
        return 1

    plugins = load_plugins()[0]
    pre = run_plugin_cmds(plugins, "pre_migrate", "pre_migrate", bdir, True)
    for r in pre:
        say("  pre_migrate [%s] rc=%s: %s" % (r["plugin"], r["rc"], r["cmd"]))
        if r["rc"] != 0 and not TEST_MODE():
            say("A pre_migrate command failed; stopping before the upgrade. Nothing in the system changed.")
            return 1

    head("Upgrading (official batocera-upgrade)")
    cmd = (["batocera-upgrade", "--media-upgrade", "--file", "/userdata/system/upgrade/boot.tar.xz"]
           if args.manual else ["batocera-upgrade", "--upgrade", "--url", url])
    say(" ".join(cmd))
    if JOURNAL is not None:
        # a cancel writes the backed-up /boot back; these keep what they are now, not what the backup had
        JOURNAL.file(P(OVERLAY))
        JOURNAL.file(P(BOOT_CONF))
    with critical("Batocera's upgrader installing the new system"):
        if TEST_MODE():
            say("(test mode) pretending the upgrade succeeded")
            rc = 0
        else:
            rc = subprocess.call(cmd)
        if rc == 0:
            journal_note({"op": "boot_replaced", "backup": bdir})
        _test_pause("upgrader")
    if rc != 0:
        say("batocera-upgrade failed (rc=%d). Your x86_64 system is unchanged; nothing else was touched." % rc)
        return 1

    park_for_v3(a, st, bdir, park, "upgraded")
    say("\nDone. Reboot now (`reboot`), then run:\n  python3 %s integrate\n  python3 %s integrate --apply"
        % (UNP(os.path.abspath(__file__)), UNP(os.path.abspath(__file__))))
    if args.reboot and not TEST_MODE():
        subprocess.call(["reboot"])
    return 0


def park_for_v3(a, st, bdir, park, phase):
    """Record state, park the overlay and X11-only services. Safe before or after the upgrade:
    the overlay only takes effect at boot, and the original stays in boot.tar."""
    head("Preparing first v3 boot")
    actions = {"parked_services": [], "overlay_moved_to": None, "conf_backup": None, "warnings": []}
    # record the upgrade FIRST, so nothing below can lose track of it
    st.update({"phase": phase, "migrated_time": now(), "migrate_actions": actions,
               "source_board": a["system"]["board"], "source_version": a["system"]["version"]})
    write_json(STATE_DIR + "/state.json", st)
    try:
        actions["conf_backup"] = conf_backup()
    except OSError as e:
        actions["warnings"].append("batocera.conf copy failed: %s" % e)
    if a["boot"]["overlay"]["present"]:
        target = os.path.join(P(bdir), "overlay.x86_64")
        if not os.path.exists(P(OVERLAY)):
            # the upgrader already dropped it; the copy inside boot.tar is the original
            actions["overlay_moved_to"] = UNP(bdir) + "/boot.tar (boot/overlay)"
            say("overlay already removed by the upgrade (original kept in boot.tar)")
        else:
            with critical("moving the old overlay off the boot partition"):
                remount_boot(True)
                try:
                    shutil.copy2(P(OVERLAY), target)
                    if sha256_file(target) != a["boot"]["overlay"]["sha256"]:
                        raise OSError("copy of overlay does not match")
                    os.remove(P(OVERLAY))
                    _test_pause("overlay-moved")
                    actions["overlay_moved_to"] = UNP(target)
                    say("overlay -> %s" % UNP(target))
                except OSError as e:
                    actions["warnings"].append("could not move overlay: %s" % e)
                    say("WARNING: could not move the overlay (%s). Remove /boot/boot/overlay before "
                        "rebooting; the original is in boot.tar." % e)
                finally:
                    remount_boot(False)
    _test_pause("park-services")
    for svc in park:
        try:
            service_toggle(svc, False)
            actions["parked_services"].append(svc)
            say("parked service %s" % svc)
        except Exception as e:  # keep going: the remaining steps still matter
            actions["warnings"].append("could not park %s: %s" % (svc, e))
            say("WARNING: could not park %s: %s" % (svc, e))
    st["migrate_actions"] = actions
    write_json(STATE_DIR + "/state.json", st)


def cmd_prepare(args, from_update=False):
    """For people who upgrade from the Batocera menu: do the pre-reboot steps now."""
    if not TEST_MODE() and os.geteuid() != 0:
        say("Run as root (the default on Batocera).")
        return 2
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    a = do_audit(quiet=True)
    problems = []
    if a["system"]["board"] != V1_BOARD:
        problems.append("board is %s, expected %s" % (a["system"]["board"], V1_BOARD))
    problems += [x["title"] for x in a["findings"] if x["severity"] == "blocker"]
    if any(g["vendor"] == "nvidia" for g in a["gpus"]) and not args.allow_nvidia:
        problems.append("NVIDIA GPU present (experimental on v3); pass --allow-nvidia to override")
    bdir = st.get("backup_dir")
    if not bdir or not st.get("backup_verified") or not os.path.isdir(P(bdir)):
        problems.append("no verified backup recorded - run `backup` first")
    if problems:
        say("Not preparing:\n  - " + "\n  - ".join(problems))
        return 2
    park = services_to_park(a)
    head("Prepare for the in-menu x86-64-v3 upgrade")
    if a["boot"]["overlay"]["present"]:
        say("  - move the x86_64 overlay into the backup (takes effect at next boot)")
    for svc in park:
        say("  - park service '%s' (uses X11-only tools)" % svc)
    if not confirm("PREPARE", "Do these now? Then start the upgrade from the Batocera menu."):
        say("Stopped. Nothing changed.")
        return 1
    park_for_v3(a, st, bdir, park, "prepared")
    if from_update:
        return 0
    say("\nPrepared. Now start the x86-64-v3 upgrade from Batocera's updates menu,"
        "\nreboot when it asks, then run:\n  python3 %s integrate" % UNP(os.path.abspath(__file__)))
    say("Changed your mind? `python3 %s unprepare` puts the overlay and services back."
        % UNP(os.path.abspath(__file__)))
    return 0


def cmd_unprepare(args):
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    if st.get("phase") != "prepared":
        say("Nothing to undo (phase is %s)." % st.get("phase"))
        return 2
    if read(BOARD_FILE).strip() != V1_BOARD:
        say("The upgrade already happened; use integrate (or rollback) instead.")
        return 2
    ma = st.get("migrate_actions") or {}
    moved = ma.get("overlay_moved_to") or ""
    if moved.endswith("overlay.x86_64") and os.path.exists(P(moved)):
        with critical("putting the overlay back on the boot partition"):
            remount_boot(True)
            try:
                shutil.copy2(P(moved), P(OVERLAY))
                say("overlay restored")
            finally:
                remount_boot(False)
    for svc in ma.get("parked_services", []):
        service_toggle(svc, True)
        say("re-enabled service %s" % svc)
    st["phase"] = "backed-up"
    st.pop("migrate_actions", None)
    write_json(STATE_DIR + "/state.json", st)
    say("Undone.")
    return 0


GRANT_PATH = "/userdata/system/x11_grant_user.py"
ACCESS_SERVICE = "xwayland_batocera_access"
ACCESS_USER = "batocera"
GRANT_SRC = r'''#!/usr/bin/env python3
"""
x11_grant_user.py - allow a local user to open windows on an X server (Xwayland on
Batocera's x86-64-v3 image), without needing the `xhost` tool.

Does exactly what `xhost +SI:localuser:<user>` does: sends one X11 ChangeHosts
request.  Must be run by a user the X server already accepts (root on Batocera).
Standard library only.

  python3 x11_grant_user.py batocera            # grant, display :0
  python3 x11_grant_user.py batocera --display :1
  python3 x11_grant_user.py --check             # just test whether *this* user can connect
  python3 x11_grant_user.py batocera --wait 120 # wait up to 120 s for the X server first
  python3 x11_grant_user.py batocera --hold     # stay connected (keeps an on-demand Xwayland up)
                                                # and re-grant whenever the X server restarts

Exit codes: 0 ok, 1 refused/error, 2 no X server.
"""
import argparse
import os
import socket
import struct
import sys
import time


def x_connect(display):
    num = display.lstrip(":").split(".")[0] or "0"
    paths = ["\0/tmp/.X11-unix/X" + num, "/tmp/.X11-unix/X" + num]  # abstract first, then file
    last = None
    for p in paths:
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.settimeout(10)
        try:
            s.connect(p)
        except OSError as e:
            last = e
            s.close()
            continue
        # connection setup, little endian, protocol 11.0; MIT cookie if one is available
        name, data = cookie_for(num)
        pad = lambda b: b + b"\0" * ((-len(b)) % 4)
        s.sendall(struct.pack("<BxHHHHxx", 0x6C, 11, 0, len(name), len(data)) + pad(name) + pad(data))
        head = recvn(s, 8)
        status, reason_len, _maj, _min, extra = struct.unpack("<BBHHH", head)
        body = recvn(s, extra * 4)
        if status != 1:
            s.close()
            reason = body[:reason_len].decode(errors="replace").strip() if status == 0 else "authentication needed"
            raise PermissionError(reason or "connection refused")
        return s
    raise ConnectionError("no X server on %s (%s)" % (display, last))


def cookie_for(num):
    """MIT-MAGIC-COOKIE-1 for display `num` from $XAUTHORITY / ~/.Xauthority, else none."""
    path = os.environ.get("XAUTHORITY") or os.path.expanduser("~/.Xauthority")
    try:
        raw = open(path, "rb").read()
    except OSError:
        return b"", b""
    i = 0
    def field():
        nonlocal i
        n = struct.unpack(">H", raw[i + 0:i + 2])[0]
        v = raw[i + 2:i + 2 + n]
        i += 2 + n
        return v
    try:
        while i < len(raw):
            i += 2  # family
            _addr, number, name, data = field(), field(), field(), field()
            if name == b"MIT-MAGIC-COOKIE-1" and number in (num.encode(), b""):
                return name, data
    except (struct.error, IndexError):
        pass
    return b"", b""


def recvn(s, n):
    buf = b""
    while len(buf) < n:
        chunk = s.recv(n - len(buf))
        if not chunk:
            raise ConnectionError("X server closed the connection")
        buf += chunk
    return buf


def round_trip(s):
    """GetInputFocus: returns the error code of anything sent before it, or 0."""
    s.sendall(struct.pack("<BxH", 43, 1))
    while True:
        pkt = recvn(s, 32)
        if pkt[0] == 0:          # error
            return pkt[1]
        if pkt[0] == 1:          # reply (to GetInputFocus)
            extra = struct.unpack("<I", pkt[4:8])[0]
            if extra:
                recvn(s, extra * 4)
            return 0
        # an event: ignore and keep reading


def grant(s, user):
    addr = b"localuser\0" + user.encode()
    pad = (-len(addr)) % 4
    length = 2 + (len(addr) + pad) // 4
    # ChangeHosts(opcode 109), mode Insert(0), family ServerInterpreted(5)
    req = struct.pack("<BBHBxH", 109, 0, length, 5, len(addr)) + addr + b"\0" * pad
    s.sendall(req)
    return round_trip(s)


ERRORS = {2: "BadValue", 10: "BadAccess (not allowed to change the host list)", 16: "BadLength"}


def hold(a):
    """Stay connected so an on-demand Xwayland keeps running and keeps the grant."""
    while True:
        try:
            s = x_connect(a.display)
        except PermissionError as e:
            print("refused by %s: %s (retrying in 5 s)" % (a.display, e), flush=True)
            time.sleep(5)
            continue
        except (ConnectionError, OSError):
            time.sleep(1)
            continue
        err = grant(s, a.user)
        if err:
            print("X server refused: %s (retrying in 5 s)" % ERRORS.get(err, "error %d" % err), flush=True)
            s.close()
            time.sleep(5)
            continue
        print("%s granted: SI:localuser:%s on %s (holding)" % (time.strftime("%H:%M:%S"), a.user, a.display),
              flush=True)
        s.settimeout(None)
        try:
            while s.recv(4096):
                pass  # no events are selected; anything here is ignorable
        except OSError:
            pass
        s.close()
        print("%s X server went away; reconnecting" % time.strftime("%H:%M:%S"), flush=True)
        time.sleep(1)


def main():
    ap = argparse.ArgumentParser(description="xhost +SI:localuser:USER without xhost")
    ap.add_argument("user", nargs="?")
    ap.add_argument("--display", default=os.environ.get("DISPLAY") or ":0")
    ap.add_argument("--check", action="store_true", help="only test whether this user can connect")
    ap.add_argument("--wait", type=int, default=0, help="seconds to wait for the X server")
    ap.add_argument("--hold", action="store_true",
                    help="keep the connection open and re-grant after every X server restart")
    a = ap.parse_args()
    if not a.check and not a.user:
        ap.error("give a user name, or --check")
    if a.hold:
        return hold(a)

    deadline = time.time() + a.wait
    while True:
        try:
            s = x_connect(a.display)
            break
        except PermissionError as e:
            print("refused by %s: %s" % (a.display, e))
            return 1
        except (ConnectionError, OSError) as e:
            if time.time() >= deadline:
                print(str(e))
                return 2
            time.sleep(1)

    if a.check:
        print("connected to %s OK" % a.display)
        return 0
    err = grant(s, a.user)
    s.close()
    if err:
        print("X server refused: %s" % ERRORS.get(err, "error %d" % err))
        return 1
    print("granted: SI:localuser:%s on %s" % (a.user, a.display))
    return 0


if __name__ == "__main__":
    sys.exit(main())
'''

ACCESS_SERVICE_SRC = """#!/bin/bash
# Keeps Xwayland open to the '%(user)s' user (Lutris/Wine/ports) on the x86-64-v3 image.
# Installed by batocera_v3_migrate.py fix --apply xwayland-access
case "$1" in
  start)
    [ "$(cat /boot/boot/batocera.board 2>/dev/null)" = "x86-64-v3" ] || exit 0
    pgrep -f 'x11_grant_user.py %(user)s --hold' >/dev/null && exit 0
    nohup python3 %(grant)s %(user)s --hold </dev/null >>/userdata/system/logs/xwayland-access.log 2>&1 &
    ;;
  stop) pkill -f 'x11_grant_user.py %(user)s --hold' ;;
esac
"""


def xwayland_access_state():
    svc = "/userdata/system/services/" + ACCESS_SERVICE
    return {"installed": os.path.exists(P(svc)) and os.path.exists(P(GRANT_PATH)),
            "enabled": ACCESS_SERVICE in conf_parse().get("system.services", "").split()}


def fix_backup(path, tag):
    src = P(path)
    dst = P(STATE_DIR + "/fix-backups/" + tag + path)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    if os.path.exists(src) and not os.path.exists(dst):
        shutil.copy2(src, dst)
    return UNP(dst)


def bash_ok(path):
    if TEST_MODE() and not shutil.which("bash"):
        return True
    try:
        return subprocess.run(["bash", "-n", path], stdout=subprocess.DEVNULL,
                              stderr=subprocess.DEVNULL, timeout=20).returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


def fix_hooks(a, tag):
    done = []
    by = {}
    for h in a["hook_bg"]:
        by.setdefault(h["file"], []).append(h["line"])
    for path, lines in by.items():
        bk = fix_backup(path, tag)
        L = read(path).split("\n")
        for n in lines:
            line = L[n - 1]
            m = BG_LINE_RE.search(line)
            body, comment = line[:m.start()].rstrip(), (m.group(1) or "")
            stdin = "" if re.search(r"(^|\s)0?<", body) else " </dev/null"
            L[n - 1] = "%s%s %s &%s" % (body, stdin, FD_CLOSE, (" " + comment) if comment else "")
        tmp = P(path) + ".v3m.tmp"
        with open(tmp, "w") as fh:
            fh.write("\n".join(L))
        shutil.copymode(P(path), tmp)
        if bash_ok(tmp):
            os.replace(tmp, P(path))
            done.append("%s: lines %s detach cleanly now (backup %s)" % (path, ",".join(map(str, lines)), bk))
        else:
            os.remove(tmp)
            done.append("%s: SKIPPED, result failed bash -n (file unchanged)" % path)
    return done


def fix_hook_backups(a, tag):
    done = []
    dest = P(STATE_DIR + "/parked-hooks")
    os.makedirs(dest, exist_ok=True)
    for path in a["hook_backups"]:
        shutil.move(P(path), os.path.join(dest, os.path.basename(path)))
        done.append("moved %s -> %s/" % (path, UNP(dest)))
    return done


def fix_xwayland_access(a, tag):
    for path, src, mode in ((GRANT_PATH, GRANT_SRC, 0o755),
                            ("/userdata/system/services/" + ACCESS_SERVICE,
                             ACCESS_SERVICE_SRC % {"user": ACCESS_USER, "grant": GRANT_PATH}, 0o755)):
        if os.path.exists(P(path)):
            fix_backup(path, tag)
        os.makedirs(os.path.dirname(P(path)), exist_ok=True)
        with open(P(path), "w") as fh:
            fh.write(src)
        os.chmod(P(path), mode)
    was = ACCESS_SERVICE in conf_parse().get("system.services", "").split()
    service_toggle(ACCESS_SERVICE, True)
    msg = ["installed %s and service %s (enabled)" % (GRANT_PATH, ACCESS_SERVICE)]
    if a["system"]["board"] == V3_BOARD and not TEST_MODE():
        journal_note({"op": "service_started", "name": ACCESS_SERVICE, "was_enabled": was})
        rc, out = run(["/userdata/system/services/" + ACCESS_SERVICE, "start"], timeout=20)
        msg.append("started (log: /userdata/system/logs/xwayland-access.log)")
    return msg


GUARDED_DIR = "/userdata/system/hooks-guarded"
GUARD_NAME = "00-hook-guard"
GUARD_SRC = r'''#!/usr/bin/env python3
# hook-guard: installed by batocera_v3_migrate.py (fix --apply hook-guard).
# Batocera runs every file in /userdata/system/scripts at game start/stop and waits for them.
# On the x86-64-v3 image a helper started by a hook (exit-hotkey watchers, controller bridges)
# can keep the launch waiting forever. This guard runs each real hook from
# /userdata/system/hooks-guarded/ in its own session, with no inherited handles, its output
# in a log, and a time limit - so no hook can ever hold a launch open.
# Put new hooks in /userdata/system/hooks-guarded/ (same arguments as before).
import os, subprocess, sys, time
HOOKS = "/userdata/system/hooks-guarded"
LOG = "/userdata/system/logs/hook-guard.log"
LIMIT = float(os.environ.get("HOOK_GUARD_TIMEOUT", "10"))
def log(msg):
    try:
        with open(LOG, "a") as f:
            f.write(time.strftime("%Y-%m-%d %H:%M:%S ") + msg + "\n")
    except OSError:
        pass
def main():
    args = sys.argv[1:]
    try:
        names = sorted(n for n in os.listdir(HOOKS) if not n.startswith("."))
    except OSError:
        return 0
    for n in names:
        path = os.path.join(HOOKS, n)
        if not (os.path.isfile(path) and os.access(path, os.X_OK)):
            continue
        try:
            out = open(LOG, "a")
        except OSError:
            out = subprocess.DEVNULL
        t = time.time()
        try:
            p = subprocess.Popen([path] + args, stdin=subprocess.DEVNULL, stdout=out, stderr=subprocess.STDOUT,
                                 close_fds=True, start_new_session=True, cwd="/userdata/system")
        except OSError as e:
            log("%s %s: could not start (%s)" % (n, " ".join(args[:2]), e))
            continue
        finally:
            if out is not subprocess.DEVNULL:
                out.close()
        try:
            rc = p.wait(timeout=LIMIT)
            log("%s %s: rc=%s in %.1fs" % (n, " ".join(args[:2]), rc, time.time() - t))
        except subprocess.TimeoutExpired:
            log("%s %s: still running after %.0fs - launch continues without it" % (n, " ".join(args[:2]), LIMIT))
    return 0
if __name__ == "__main__":
    sys.exit(main())
'''


def hook_guard_state():
    g = P(HOOK_DIR + "/" + GUARD_NAME)
    direct = []
    if os.path.isdir(P(HOOK_DIR)):
        for n in sorted(os.listdir(P(HOOK_DIR))):
            fp = os.path.join(P(HOOK_DIR), n)
            if n != GUARD_NAME and os.path.isfile(fp) and os.access(fp, os.X_OK) and not is_backup_name(n):
                direct.append(n)
    return {"installed": os.path.exists(g), "direct_hooks": direct}


def fix_hook_guard(a, tag):
    done = []
    os.makedirs(P(GUARDED_DIR), exist_ok=True)
    for n in hook_guard_state()["direct_hooks"]:
        src = os.path.join(P(HOOK_DIR), n)
        fix_backup(HOOK_DIR + "/" + n, tag)
        dst = os.path.join(P(GUARDED_DIR), n)
        if os.path.exists(dst):
            os.rename(dst, dst + ".replaced-" + tag)
        shutil.move(src, dst)
        done.append("moved %s -> %s/" % (n, GUARDED_DIR))
    g = P(HOOK_DIR + "/" + GUARD_NAME)
    with open(g, "w") as fh:
        fh.write(GUARD_SRC)
    os.chmod(g, 0o755)
    done.append("installed %s/%s (log: /userdata/system/logs/hook-guard.log)" % (HOOK_DIR, GUARD_NAME))
    return done


def fix_hook_unguard(a, tag):
    done = []
    g = P(HOOK_DIR + "/" + GUARD_NAME)
    if os.path.exists(g):
        os.remove(g)
        done.append("removed %s/%s" % (HOOK_DIR, GUARD_NAME))
    if os.path.isdir(P(GUARDED_DIR)):
        for n in sorted(os.listdir(P(GUARDED_DIR))):
            dst = os.path.join(P(HOOK_DIR), n)
            if os.path.exists(dst):
                done.append("kept %s in %s (a file with that name is already in scripts/)" % (n, GUARDED_DIR))
                continue
            shutil.move(os.path.join(P(GUARDED_DIR), n), dst)
            done.append("moved %s back to %s/" % (n, HOOK_DIR))
    return done


WATCHDOG_PATH = "/userdata/system/launch_watchdog.py"
WATCHDOG_SERVICE = "launch_watchdog"
WATCHDOG_SRC = r'''#!/usr/bin/env python3
"""
launch_watchdog.py - universal safety net for Batocera game launches.

1. Stuck-launch watchdog
   A launch is "stuck" when batocera-launch is alive, nothing runs under it, and its
   log has not moved for a while. That is what every hang looks like from the outside,
   whatever caused it: a hook helper holding the launcher's pipes, a helper left in the
   launcher's session, or a launch that never got going. The watchdog then frees it:
   it finds processes holding the launcher's pipes or sitting in its session that are
   not part of the launch itself, stops them, and logs what it found.

2. Rescue combo (always gets you back to EmulationStation)
   Hold SELECT + START + L + R for 3 s on any controller, or press Ctrl + Alt + End.
   Devices are only read, never grabbed, so hotkeys and controller forwarders still work.

  python3 launch_watchdog.py run            # what the service runs
  python3 launch_watchdog.py diagnose       # one-off: is a launch stuck, and on what?
  python3 launch_watchdog.py free           # one-off: free a stuck launch now
  python3 launch_watchdog.py rescue         # one-off: close the running game now

Log: /userdata/system/logs/launch-watchdog.log      Standard library + python-evdev (optional).
"""
import os
import re
import signal
import subprocess
import sys
import threading
import time

LOG = os.environ.get("WATCHDOG_LOG", "/userdata/system/logs/launch-watchdog.log")
LAUNCH_LOG = os.environ.get("WATCHDOG_LAUNCH_LOG", "/userdata/system/logs/batocera-launch.log")
LAUNCH_RE = re.compile(os.environ.get("WATCHDOG_LAUNCH_RE", r"^/usr/bin/python3? /usr/bin/batocera-launch( |$)"))
IDLE = float(os.environ.get("WATCHDOG_IDLE", "25"))       # no child + quiet log this long = stuck
POLL = float(os.environ.get("WATCHDOG_POLL", "2"))
HOLD = float(os.environ.get("WATCHDOG_HOLD", "3"))        # rescue combo hold time
# processes that don't mean "the game is running" (a launch with only these under it is idle)
TRIVIAL_RE = re.compile(r"^(\S*/)?(sh|bash|sleep|head|timeout|pgrep|cat|tee|logger)( |$)")
# legitimate parts of a launch or of the system that may share its pipes: never stopped
NEVER_RE = re.compile(r"evmapy|hotkeygen|emulationstation|batocera-launch|dbus-daemon|dbus-run-session|"
                      r"launch_watchdog\.py|^head |^(\S*/)?head$|systemd|udevd|labwc|Xwayland|pipewire|wireplumber")


def log(msg):
    line = time.strftime("%Y-%m-%d %H:%M:%S ") + msg
    print(line, flush=True)
    try:
        with open(LOG, "a") as f:
            f.write(line + "\n")
    except OSError:
        pass


# ---------------------------------------------------------------- /proc helpers
def pids():
    for n in os.listdir("/proc"):
        if n.isdigit():
            yield int(n)


def cmdline(pid):
    try:
        with open("/proc/%d/cmdline" % pid, "rb") as f:
            return f.read().replace(b"\0", b" ").decode(errors="replace").strip()
    except OSError:
        return ""


def stat(pid):
    """(ppid, sid, starttime-in-ticks) or None."""
    try:
        with open("/proc/%d/stat" % pid) as f:
            rest = f.read().rsplit(")", 1)[1].split()
        return int(rest[1]), int(rest[3]), int(rest[19])
    except (OSError, IndexError, ValueError):
        return None


def pipes(pid):
    out = set()
    try:
        for fd in os.listdir("/proc/%d/fd" % pid):
            try:
                t = os.readlink("/proc/%d/fd/%s" % (pid, fd))
            except OSError:
                continue
            if t.startswith("pipe:"):
                out.add(t)
    except OSError:
        pass
    return out


def tree():
    parent, sid = {}, {}
    START.clear()
    for p in pids():
        s = stat(p)
        if s:
            parent[p], sid[p], START[p] = s
    kids = {}
    for p, pp in parent.items():
        kids.setdefault(pp, []).append(p)
    return parent, sid, kids


START = {}


def descendants(pid, kids):
    out, todo = [], list(kids.get(pid, []))
    while todo:
        p = todo.pop()
        out.append(p)
        todo.extend(kids.get(p, []))
    return out


def ancestors(pid, parent):
    out = []
    while pid in parent and parent[pid] > 1:
        pid = parent[pid]
        out.append(pid)
    return out


def launchers():
    return [p for p in pids() if LAUNCH_RE.search(cmdline(p))]


# ---------------------------------------------------------------- diagnosis
def holders(lpid):
    """Processes outside the launch that hold its pipes or sit in its session."""
    parent, sid, kids = tree()
    mine = {lpid} | set(descendants(lpid, kids)) | set(ancestors(lpid, parent))
    wrapper = set(ancestors(lpid, parent))
    watched = pipes(lpid)
    for a in wrapper:                     # ES's sh wrappers carry the status pipe too
        if "batocera-launch" in cmdline(a) and "emulationstation" not in cmdline(a):
            watched |= pipes(a)
    lsid = sid.get(lpid)
    lstart = START.get(lpid, 0)
    found = {}
    for p in parent:
        if p in mine or p == os.getpid() or START.get(p, 0) < lstart:
            continue          # only things started during this launch
        cl = cmdline(p)
        if not cl or NEVER_RE.search(cl):
            continue
        shared = pipes(p) & watched
        same_session = (lsid is not None and sid.get(p) == lsid and parent.get(p) == 1)  # orphaned helper
        if shared or same_session:
            found[p] = {"cmd": cl[:160], "pipes": sorted(shared), "same_session": same_session}
    return found


class Watch:
    def __init__(self):
        self.seen = {}      # launcher pid -> last time it had children
        self.freed = set()

    def check(self, act=True):
        parent, sid, kids = tree()
        now = time.time()
        try:
            log_age = now - os.path.getmtime(LAUNCH_LOG)
        except OSError:
            log_age = 1e9
        for lp in launchers():
            busy = [k for k in descendants(lp, kids) if not TRIVIAL_RE.search(cmdline(k))]
            if busy or lp not in self.seen:
                self.seen[lp] = now
                continue
            idle = now - self.seen[lp]
            if idle < IDLE or log_age < IDLE or lp in self.freed:
                continue
            h = holders(lp)
            if not h:
                log("launch %d idle %.0fs but nothing outside it holds it (waiting on itself)" % (lp, idle))
                self.freed.add(lp)
                continue
            log("launch %d looks STUCK (idle %.0fs, log quiet %.0fs); held by:" % (lp, idle, log_age))
            for p, d in h.items():
                why = ", ".join(filter(None, ["pipe " + " ".join(d["pipes"]) if d["pipes"] else "",
                                              "same session" if d["same_session"] else ""]))
                log("   %d  %s  [%s]" % (p, d["cmd"], why))
            if act:
                stop(list(h))
                log("launch %d freed" % lp)
            self.freed.add(lp)
        for lp in list(self.seen):
            if not os.path.exists("/proc/%d" % lp):
                self.seen.pop(lp, None)
                self.freed.discard(lp)


def stop(plist, grace=3):
    for p in plist:
        try:
            os.kill(p, signal.SIGTERM)
        except OSError:
            pass
    deadline = time.time() + grace
    while time.time() < deadline and any(os.path.exists("/proc/%d" % p) for p in plist):
        time.sleep(0.2)
    for p in plist:
        if os.path.exists("/proc/%d" % p):
            try:
                os.kill(p, signal.SIGKILL)
            except OSError:
                pass


# ---------------------------------------------------------------- rescue
def rescue(reason):
    log("RESCUE (%s): closing the running game" % reason)
    parent, sid, kids = tree()
    ls = launchers()
    if not ls:
        log("   no game launch running")
        return
    if subprocess.run(["sh", "-c", "command -v batocera-es-swissknife >/dev/null"]).returncode == 0:
        subprocess.run(["batocera-es-swissknife", "--emukill"], stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL, timeout=15)
        time.sleep(2)
    for lp in ls:                         # whatever survived, plus anything holding the launch
        if not os.path.exists("/proc/%d" % lp):
            continue
        parent, sid, kids = tree()
        victims = [p for p in descendants(lp, kids)] + list(holders(lp))
        stop(victims)
        if os.path.exists("/proc/%d" % lp):
            stop([lp])
        log("   launch %d closed (%d processes stopped)" % (lp, len(victims)))


def rescue_listener():
    try:
        import evdev
        from evdev import ecodes as e
    except ImportError:
        log("python-evdev missing: rescue combo disabled (watchdog still active)")
        return
    pad_combo = {e.BTN_SELECT, e.BTN_START, e.BTN_TL, e.BTN_TR}
    kb_ctrl = {e.KEY_LEFTCTRL, e.KEY_RIGHTCTRL}
    kb_alt = {e.KEY_LEFTALT, e.KEY_RIGHTALT}
    held = {}            # path -> set of pressed codes
    since = {}           # path -> time the pad combo became complete
    devices = {}
    last_scan = 0
    import select
    while True:
        if time.time() - last_scan > 5:           # pick up controllers that connect later
            last_scan = time.time()
            for path in evdev.list_devices():
                if path in devices:
                    continue
                try:
                    d = evdev.InputDevice(path)
                    keys = set(d.capabilities().get(e.EV_KEY, []))
                except OSError:
                    continue
                if pad_combo <= keys or (e.KEY_END in keys and kb_ctrl & keys):
                    devices[path] = d
                else:
                    d.close()
        if not devices:
            time.sleep(1)
            continue
        r, _, _ = select.select(list(devices.values()), [], [], 0.5)
        for d in r:
            try:
                for ev in d.read():
                    if ev.type != e.EV_KEY:
                        continue
                    s = held.setdefault(d.path, set())
                    (s.add if ev.value else s.discard)(ev.code)
                    if ev.code == e.KEY_END and ev.value == 1 and s & kb_ctrl and s & kb_alt:
                        rescue("Ctrl+Alt+End on %s" % d.name)
            except OSError:
                devices.pop(d.path, None)
                held.pop(d.path, None)
                continue
        now = time.time()
        for path, s in held.items():
            if pad_combo <= s:
                start = since.setdefault(path, now)
                if now - start >= HOLD:
                    rescue("Select+Start+L+R held on %s" % devices[path].name if path in devices else path)
                    since[path] = now + 30          # one rescue per hold
            else:
                since.pop(path, None)


# ---------------------------------------------------------------- main
def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else "run"
    if cmd == "run":
        log("watchdog started (stuck after %.0fs idle; rescue: Select+Start+L+R %.0fs or Ctrl+Alt+End)"
            % (IDLE, HOLD))
        threading.Thread(target=rescue_listener, daemon=True).start()
        w = Watch()
        while True:
            try:
                w.check()
            except Exception as ex:      # never die: this is the safety net
                log("watchdog error: %r" % ex)
            time.sleep(POLL)
    elif cmd in ("diagnose", "free"):
        ls = launchers()
        if not ls:
            print("No game launch running.")
            return 0
        parent, sid, kids = tree()
        for lp in ls:
            busy = [k for k in descendants(lp, kids) if not TRIVIAL_RE.search(cmdline(k))]
            print("launch %d: %s" % (lp, "running %d processes (game is up)" % len(busy) if busy else
                                     "NOTHING running under it"))
            h = holders(lp)
            for p, d in h.items():
                print("   held by %d  %s  pipes=%s same_session=%s" % (p, d["cmd"], d["pipes"], d["same_session"]))
            if not h:
                print("   nothing outside the launch is holding it")
            if cmd == "free" and h:
                stop(list(h))
                print("   freed: stopped %d processes" % len(h))
        return 0
    elif cmd == "rescue":
        rescue("command line")
        return 0
    else:
        print(__doc__)
        return 2


if __name__ == "__main__":
    sys.exit(main() or 0)
'''
WATCHDOG_SERVICE_SRC = """#!/bin/bash
# Launch watchdog + rescue combo. Installed by batocera_v3_migrate.py fix --apply launch-watchdog
case "$1" in
  start)
    pgrep -f 'launch_watchdog.py run' >/dev/null && exit 0
    nohup python3 %(path)s run </dev/null >/dev/null 2>&1 &
    ;;
  stop) pkill -f 'launch_watchdog.py run' ;;
esac
"""


def watchdog_state():
    return {"installed": os.path.exists(P(WATCHDOG_PATH)),
            "enabled": WATCHDOG_SERVICE in conf_parse().get("system.services", "").split()}


def fix_launch_watchdog(a, tag):
    for path, src in ((WATCHDOG_PATH, WATCHDOG_SRC),
                      ("/userdata/system/services/" + WATCHDOG_SERVICE, WATCHDOG_SERVICE_SRC % {"path": WATCHDOG_PATH})):
        if os.path.exists(P(path)):
            fix_backup(path, tag)
        os.makedirs(os.path.dirname(P(path)), exist_ok=True)
        with open(P(path), "w") as fh:
            fh.write(src)
        os.chmod(P(path), 0o755)
    was = watchdog_state()["enabled"]
    service_toggle(WATCHDOG_SERVICE, True)
    out = ["installed %s and service %s (enabled)" % (WATCHDOG_PATH, WATCHDOG_SERVICE)]
    if not TEST_MODE():
        journal_note({"op": "service_started", "name": WATCHDOG_SERVICE, "was_enabled": was})
        run(["pkill", "-f", "launch_watchdog.py run"])
        run(["/userdata/system/services/" + WATCHDOG_SERVICE, "start"], timeout=20)
        out.append("started. Log: /userdata/system/logs/launch-watchdog.log")
    out.append("rescue: hold Select+Start+L+R for 3 s, or Ctrl+Alt+End")
    return out


FIXES = {
    "hooks": ("Detach background programs started by game hooks (closes inherited pipes)",
              lambda a: len(a["hook_bg"]), fix_hooks),
    "hook-guard": ("Run ALL game hooks through one guard: own session, no inherited handles, 10 s limit",
                   lambda a: len(hook_guard_state()["direct_hooks"]) if a["system"]["board"] == V3_BOARD
                   or hook_guard_state()["direct_hooks"] else 0, fix_hook_guard),
    "launch-watchdog": ("Watchdog that frees any stuck launch + rescue combo (Select+Start+L+R 3 s / Ctrl+Alt+End)",
                        lambda a: 0 if watchdog_state()["enabled"] and watchdog_state()["installed"] else 1,
                        fix_launch_watchdog),
    "hook-unguard": ("Undo hook-guard: put the hooks back in the scripts folder",
                     lambda a: 1 if hook_guard_state()["installed"] else 0, fix_hook_unguard),
    "hook-backups": ("Move backup copies out of the scripts folder",
                     lambda a: len(a["hook_backups"]), fix_hook_backups),
    "xwayland-access": ("Let the '%s' user open windows on Xwayland (installs a small boot service)" % ACCESS_USER,
                        lambda a: (0 if a["xwayland_access"]["enabled"] else max(1, len(a["nonroot_x"])))
                        if a["nonroot_x"] or a["system"]["board"] == V3_BOARD else 0,
                        fix_xwayland_access),
}


def cmd_fix(args):
    say("Checking (read-only, a few seconds)...")
    a = do_audit(quiet=True, light=True)
    if not args.apply:
        head("Available fixes")
        for fid, (desc, count, _) in FIXES.items():
            n = count(a)
            say("  %-16s %-4s %s" % (fid, n if n else "-", desc))
        for x in a["findings"]:
            if x["id"] == "xorg-auth":
                say("\n(report only) %s - see the audit report for lines to review" % x["title"])
        say("\nApply with: fix --apply hook-guard launch-watchdog   (or --apply all)")
        return 0
    wanted = [f for f in FIXES if f != "hook-unguard"] if args.apply == ["all"] else args.apply
    bad = [w for w in wanted if w not in FIXES]
    if bad:
        say("Unknown fix: %s" % ", ".join(bad))
        return 2
    order = ["hook-backups", "hooks", "hook-guard", "hook-unguard", "xwayland-access", "launch-watchdog"]
    todo = [w for w in sorted(wanted, key=lambda x: order.index(x) if x in order else 99) if FIXES[w][1](a)]
    if not todo:
        say("Nothing to fix.")
        return 0
    if not confirm("FIX", "Apply: %s? Every changed file is backed up first." % ", ".join(todo)):
        return 1
    tag = stamp()
    for w in todo:
        head(w)
        for line in FIXES[w][2](a, tag):
            say("  " + line)
    say("\nBackups: %s/fix-backups/%s" % (STATE_DIR, tag))
    return 0


def remount_boot(rw):
    if TEST_MODE():
        return
    run(["mount", "-o", "remount,%s" % ("rw" if rw else "ro"), "/boot"])


# --------------------------------------------------------------------------
# integrate (post-migration)
# --------------------------------------------------------------------------
def plan_videooutput(base, cur):
    """Return list of (key, old, new_or_None, reason)."""
    names = {c["name"] for c in cur["connectors"]}
    if cur.get("batocera_resolution") and cur["batocera_resolution"]["listOutputs"]:
        names |= set(cur["batocera_resolution"]["listOutputs"])
    out = []
    conf = conf_parse()
    for k, v in sorted(conf.items()):
        if not k.startswith("global.videooutput") or not v or v in names:
            continue
        t = connector_type(v)
        same = [c for c in cur["connectors"] if c["type"] == t]
        conn = [c for c in same if c["status"] == "connected"]
        if len(conn) == 1:
            out.append((k, v, conn[0]["name"], "only connected %s port" % t))
        elif len(same) == 1:
            out.append((k, v, same[0]["name"], "only %s port" % t))
        else:
            m = re.search(r"-(\d+)$", v)
            guess = "%s-%d" % (t, int(m.group(1)) + 1) if m else None
            if guess in names:
                out.append((k, v, guess, "Xorg counts from 0, DRM from 1"))
            else:
                out.append((k, v, None, "no matching port; let Batocera auto-detect"))
    return out


def do_integrate(apply_fixes, ack_overlay=False):
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    base = load_json(STATE_DIR + "/baseline-audit.json")
    if base is None and st.get("backup_dir"):
        base = load_json(st["backup_dir"] + "/audit.json")
    cur = do_audit(quiet=True)
    plugins = load_plugins()[0]
    R = {"time": now(), "applied": apply_fixes, "board": cur["system"]["board"],
         "version": cur["system"]["version"], "items": [], "changes": []}

    def item(sev, title, detail="", action=""):
        R["items"].append({"severity": sev, "title": title, "detail": detail, "action": action})

    if cur["system"]["board"] != V3_BOARD:
        item("blocker", "Still on board %s" % cur["system"]["board"],
             action="Did the upgrade finish and did you reboot?")
    if base is None:
        item("warn", "No baseline audit found", "Checks run without before/after comparison.")
        base = {"elfs": [], "symlinks": [], "mounts": [], "services": {"enabled": []}, "x11_refs": []}

    # 1. display output names
    vo = plan_videooutput(base, cur["display"])
    for k, old, new, why in vo:
        if apply_fixes:
            if not R["changes"]:
                R["changes"].append("batocera.conf backed up to %s" % conf_backup())
            conf_set(k, new)
            R["changes"].append("%s: %s -> %s (%s)" % (k, old, new or "(removed)", why))
        item("warn" if not apply_fixes else "info", "Display output %s=%s does not exist on v3" % (k, old),
             why, "set to %s" % (new or "auto (key removed)"))
    # 2. resolution still offered?
    for key in ("es.resolution", "global.videomode"):
        val = conf_parse().get(key)
        if not val or val in ("auto", "default", "max-1920x1080"):
            continue
        modes = set()
        for c in cur["display"]["connectors"]:
            if c["status"] == "connected":
                modes |= set(c["modes"])
        res = val.split(".")[0] if re.match(r"\d+x\d+", val) else val
        if modes and not any(m.startswith(res.split("@")[0]) for m in modes):
            item("warn", "%s=%s is not offered by the connected display" % (key, val),
                 "Offered: " + ", ".join(sorted(modes)[:12]), "Pick a mode from the ES video settings.")
        else:
            item("info", "%s=%s kept" % (key, val))
    # 3. parked services
    reenabled = set()
    for svc in (st.get("migrate_actions") or {}).get("parked_services", []):
        refs = [h for h in cur["x11_refs"] if h["file"] == "/userdata/system/services/" + svc]
        if refs:
            item("warn", "Service %s still parked: X11-only calls remain" % svc,
                 "\n".join("%s:%d %s" % (h["file"], h["line"], h["text"]) for h in refs),
                 "Port these lines, then run integrate --apply again.")
        elif apply_fixes:
            service_toggle(svc, True)
            R["changes"].append("re-enabled service %s" % svc)
            reenabled.add(svc)
            item("info", "Service %s re-enabled" % svc)
            ma = st.setdefault("migrate_actions", {})
            ma["parked_services"] = [x for x in ma.get("parked_services", []) if x != svc]
        else:
            item("warn", "Service %s parked, now clean" % svc, action="integrate --apply re-enables it")
    # 4. overlay
    moved = (st.get("migrate_actions") or {}).get("overlay_moved_to")
    if moved and ack_overlay and apply_fixes and not st.get("overlay_ack"):
        st["overlay_ack"] = now()
        R["changes"].append("old overlay acknowledged as rebuilt/not needed")
    if moved and st.get("overlay_ack"):
        item("info", "Old x86_64 overlay parked at %s (acknowledged)" % moved)
    elif moved:
        files = (base.get("boot", {}).get("overlay", {}) or {}).get("files", [])
        item("critical", "Old x86_64 overlay was parked (not restored)",
             "Saved at %s\n%s" % (moved, "\n".join(files[:60])),
             "Rebuild these customisations for x86-64-v3, install them, then batocera-save-overlay; "
             "then run integrate --apply --ack-overlay.")
    if cur["boot"]["overlay"]["present"]:
        item("info", "An overlay exists on v3", action="Make sure it was built on/for v3.")
    # 5. binaries
    base_missing = {e["path"]: set(e.get("missing_libs") or []) for e in base.get("elfs", [])}
    cur_by = {e["path"]: e for e in cur["elfs"]}
    runtime_hits, gone = [], []
    for path in sorted(base_missing):
        e = cur_by.get(path)
        if e is None:
            gone.append(path)
            continue
        if e.get("missing_libs") is None:
            continue
        new = set(e["missing_libs"]) - base_missing[path]
        if not new:
            continue
        if e.get("bundled_runtime") or RUNTIME_RE.search(path):
            runtime_hits.append(path)
        else:
            item("critical", "Binary now missing libraries: %s" % path, ", ".join(sorted(new)),
                 "Checked with its own lib folders too. Bundle these next to it (and add the folder to "
                 "its launcher's LD_LIBRARY_PATH) or rebuild it against the x86-64-v3 image.")
    if runtime_hits:
        item("info", "%d files inside self-contained runtimes report missing host libraries" % len(runtime_hits),
             "\n".join(runtime_hits[:15]) + ("\n..." if len(runtime_hits) > 15 else ""),
             "Normal: Steam/UMU containers, AppImage extracts and add-on rootfs trees load their own "
             "libraries. Only investigate if that app actually fails to start.")
    if gone:
        item("warn", "%d binaries from before the migration are gone" % len(gone), "\n".join(gone[:20]),
             "Usually temp/cache files. Check any that belong to your own builds.")
    # 6. links and drives
    for l in base.get("symlinks", []):
        if l["resolves"] and not link_resolves(P(l["link"])):
            item("critical", "Link broken: %s -> %s" % (l["link"], l["target"]),
                 action="Is the drive mounted? (check `integrate` again after mounting)")
    cur_uuids = {m["uuid"] for m in cur["mounts"] if m["uuid"]}
    for m in base.get("mounts", []):
        if m.get("uuid") and m["mountpoint"].startswith("/media") and m["uuid"] not in cur_uuids:
            item("critical", "Drive not mounted: %s (UUID %s, was %s)" % (m["device"], m["uuid"], m["mountpoint"]),
                 action="Plug it in / check your mount service.")
    # 7. services that should be running
    for svc in base.get("services", {}).get("enabled", []):
        if svc not in cur["services"]["enabled"] and svc not in reenabled and \
                svc not in (st.get("migrate_actions") or {}).get("parked_services", []):
            item("warn", "Service %s was enabled before, isn't now" % svc,
                 action="batocera-services enable %s" % svc)
        if svc not in cur["services"]["available"]:
            item("warn", "Service %s no longer exists" % svc)
    # 8. remaining X11 refs outside services
    other = [h for h in cur["x11_refs"] if "/services/" not in h["file"]]
    if other:
        item("warn", "%d X11-only references remain in scripts/launchers" % len(other),
             "\n".join("%s:%d %s" % (h["file"], h["line"], h["text"]) for h in other[:40]),
             "Most still run under Xwayland; mode-setting/input tools need porting.")
    # 9. integrations
    if apply_fixes:
        for r in run_plugin_cmds(plugins, "post_integrate", "post_integrate", st.get("backup_dir"), True):
            R["changes"].append("[%s] %s -> rc=%s" % (r["plugin"], r["cmd"], r["rc"]))
            if r["rc"] != 0:
                item("critical", "post_integrate failed for %s" % r["plugin"], r["out"][-500:])
    for r in run_plugin_verify(plugins):
        if r["ok"] is False:
            item("critical", "[%s] %s failed" % (r["plugin"], r["check"]), r.get("detail", ""))
        elif r["ok"]:
            item("info", "[%s] %s ok" % (r["plugin"], r["check"]))
    # 10. hard rule: rollback info always present
    if st.get("backup_dir"):
        item("info", "Rollback available from %s" % st["backup_dir"], action="rollback")
    R["items"].sort(key=lambda x: SEVERITY_ORDER[x["severity"]])
    if apply_fixes and cur["system"]["board"] == V3_BOARD:
        st["phase"] = "integrated" if not any(i["severity"] in ("blocker", "critical") for i in R["items"]) \
            else "integrated-with-issues"
        st["integrated_time"] = now()
        write_json(STATE_DIR + "/state.json", st)
    return R


def integrate_markdown(R):
    L = ["# x86-64-v3 integration report", "",
         "- %s | board %s | %s | %s" % (R["time"], R["board"], R["version"],
                                         "fixes APPLIED" if R["applied"] else "dry run"), ""]
    if R["changes"]:
        L.append("## Changes made")
        L += ["- " + c for c in R["changes"]]
        L.append("")
    L.append("## Checks")
    for i in R["items"]:
        L.append("### [%s] %s" % (i["severity"].upper(), i["title"]))
        if i["detail"]:
            L += ["```", i["detail"], "```"]
        if i["action"]:
            L.append("**Action:** " + i["action"])
        L.append("")
    return "\n".join(L) + "\n"


def cmd_integrate(args):
    if args.apply and not confirm("APPLY", "Apply the safe fixes listed by integrate (each edit is backed up)?"):
        return 1
    R = do_integrate(args.apply, args.ack_overlay)
    out = P(STATE_DIR + "/integrate-%s.md" % stamp())
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as fh:
        fh.write(integrate_markdown(R))
    write_json(UNP(out)[:-3] + ".json", R)
    head("Integration " + ("(applied)" if args.apply else "(dry run)"))
    for c in R["changes"]:
        say("  changed: " + c)
    for i in R["items"]:
        say("[%-8s] %s" % (i["severity"].upper(), i["title"]))
        if i["action"] and i["severity"] != "info":
            say("           -> " + i["action"])
    say("\nReport: %s" % UNP(out))
    bad = any(i["severity"] in ("blocker", "critical") for i in R["items"])
    return 1 if bad else 0


# --------------------------------------------------------------------------
# rollback
# --------------------------------------------------------------------------
def restore_boot(bdir, verify=True):
    """Write the boot partition saved in a backup back to /boot. False if the backup can't be used."""
    boot_tar = os.path.join(P(bdir), "boot.tar")
    if not os.path.exists(boot_tar) or (verify and not verify_backup_dir(P(bdir))):
        say("  %s has no usable boot.tar" % bdir)
        return False
    with critical("writing the boot partition back"):
        remount_boot(True)
        try:
            with tarfile.open(boot_tar) as t:
                members = [x for x in t.getmembers() if x.name.startswith("boot")]
                kw = {"filter": "fully_trusted"} if hasattr(tarfile, "fully_trusted_filter") else {}
                t.extractall(P("/"), members=members, **kw)
            if not TEST_MODE():
                os.sync()
        finally:
            remount_boot(False)
    return True


def cmd_rollback(args):
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    bdir = args.backup or st.get("backup_dir")
    if not bdir:
        say("No backup recorded; pass --backup DIR.")
        return 2
    boot_tar = os.path.join(P(bdir), "boot.tar")
    if not os.path.exists(boot_tar):
        say("%s has no boot.tar." % bdir)
        return 2
    say("Verifying backup...")
    if not verify_backup_dir(P(bdir)):
        say("Backup failed verification; refusing to write it to /boot.")
        return 2
    m = load_json(bdir + "/manifest.json", {})
    say("This restores the boot partition captured %s (board %s, %s)." % (m["time"], m["board"], m["version"]))
    if args.restore_config:
        say("It also restores /userdata/system/batocera.conf from that backup.")
    if not confirm("ROLLBACK", "Write the old boot partition back?"):
        return 1
    restore_boot(bdir, verify=False)
    say("Boot partition restored.")
    if args.restore_config:
        sys_tar = os.path.join(P(bdir), "system.tar.gz")
        conf_backup()
        with tarfile.open(sys_tar) as t:
            mem = t.getmember("userdata/system/batocera.conf")
            kw = {"filter": "fully_trusted"} if hasattr(tarfile, "fully_trusted_filter") else {}
            t.extractall(P("/"), members=[mem], **kw)
        say("batocera.conf restored.")
    for svc in (st.get("migrate_actions") or {}).get("parked_services", []):
        service_toggle(svc, True)
        say("re-enabled service %s" % svc)
    moved = (st.get("migrate_actions") or {}).get("overlay_moved_to")
    if moved and os.path.exists(P(moved)):
        say("Your old overlay is at %s - it was included in the restored boot partition." % moved)
    st.update({"phase": "rolled-back", "rollback_time": now()})
    write_json(STATE_DIR + "/state.json", st)
    say("Reboot to start the x86_64 system again.")
    return 0


# --------------------------------------------------------------------------
# status / init-plugin
# --------------------------------------------------------------------------
def cmd_status(args):
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    s = system_info()
    say("Board now: %s   version: %s" % (s["board"], s["version"]))
    if not st:
        say("No migration state yet. Start with: audit, then backup --dest /media/<drive>")
        return 0
    for k in sorted(st):
        if k != "migrate_actions":
            say("  %-18s %s" % (k, st[k]))
    ma = st.get("migrate_actions") or {}
    if ma:
        say("  parked services   %s" % (", ".join(ma.get("parked_services", [])) or "none"))
        say("  overlay parked at %s" % (ma.get("overlay_moved_to") or "-"))
    return 0


def cmd_init_plugin(args):
    name = re.sub(r"[^A-Za-z0-9_.-]", "-", args.name)
    path = P(PLUGIN_DIR + "/" + name + ".json")
    if os.path.exists(path) and not args.force:
        say("%s exists (use --force)" % UNP(path))
        return 2
    tpl = json.loads(json.dumps(PLUGIN_TEMPLATE).replace("my-custom-thing", name))
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        json.dump(tpl, fh, indent=2)
    say("Wrote %s - edit the paths/commands, then re-run audit." % UNP(path))
    return 0


# --------------------------------------------------------------------------

# ==========================================================================
# THE SIMPLE FLOW:  scan  >  backup  >  update  >  integrate
# ==========================================================================
SCAN_FILE = STATE_DIR + "/scan.json"
XAUTH_HELPER = "/userdata/system/bin/v3-xauth"
XAUTH_HELPER_SRC = """#!/usr/bin/env python3
# v3-xauth: prints a readable X cookie file for scripts that used to take Xorg's -auth file.
# Xwayland admits root by user, and the 'batocera' user via the xwayland access service;
# any well-formed cookie lets such scripts continue. Installed by batocera_v3_migrate.py.
import os, struct
d, f = "/var/run/v3-xauth", "/var/run/v3-xauth/Xauthority"
if not os.path.exists(f):
    os.makedirs(d, exist_ok=True)
    os.chmod(d, 0o755)
    F = lambda b: struct.pack(">H", len(b)) + b
    data = struct.pack(">H", 65535) + F(b"") + F(b"0") + F(b"MIT-MAGIC-COOKIE-1") + F(os.urandom(16))
    tmp = f + ".%d" % os.getpid()
    with open(tmp, "wb") as h:
        h.write(data)
    os.chmod(tmp, 0o644)
    os.replace(tmp, f)
print(f)
"""
WAYLAND_ENV_BLOCK = """# display session: Wayland on x86-64-v3, Xorg on x86_64 [batocera_v3_migrate]
if [ "$(cat /boot/boot/batocera.board 2>/dev/null)" = "x86-64-v3" ]; then
    export XDG_RUNTIME_DIR="${XDG_RUNTIME_DIR:-/var/run}"
    for _i in $(seq 1 30); do
        _W=$(ls "$XDG_RUNTIME_DIR" 2>/dev/null | grep -m1 -E '^wayland-[0-9]+$'); [ -n "$_W" ] && break; sleep 1
    done
    export WAYLAND_DISPLAY="${_W:-wayland-0}"
fi
export DISPLAY="${DISPLAY:-:0}"
"""
DESKTOP_RE = re.compile(r"\b(openbox|startx|xinit|tint2|picom|xfce4-session|lxsession|matchbox)\b")
DISPLAY_LINE_RE = re.compile(r"^\s*export\s+DISPLAY=:0(\.0)?\s*$")
AUTH_ASSIGN_RE = re.compile(r"^(\s*)(?:local\s+|export\s+)?([A-Za-z_][A-Za-z0-9_]*)=\$\(.*X :0.*-auth")
OVERLAY_SKIP_RE = re.compile(r"^/(usr/share/(man|doc|gtk-doc|locale|info)/|usr/include/|etc/X11/|etc/xdg/openbox/|"
                             r"\.Xauthority$|\.config/pulse/|\.local/state/|.*__pycache__/|usr/lib/python3\.\d+/|"
                             r".*\.bak$)")


def plan_for(a):
    """Turn scan results into: [(what, how integrate handles it, automatic?)]"""
    P_ = []
    svc_dir = "/userdata/system/services/"
    by_file = {}
    for h in a["x11_refs"]:
        by_file.setdefault(h["file"], []).append(h)
    if a["boot"]["overlay"]["present"]:
        P_.append(("System overlay (%s)" % human(a["boot"]["overlay"]["size"]),
                   "backed up; after the update, files v3 doesn't have are restored and saved to a new overlay; "
                   "files v3 already has are kept as v3's and listed", True))
    for svc in a["services"]["enabled"]:
        f = svc_dir + svc
        if f not in by_file:
            continue
        txt = read(f)
        if DESKTOP_RE.search(txt):
            P_.append(("Service '%s' (X11 desktop)" % svc, "can't run under Wayland: switched off, files kept", False))
        elif any(DISPLAY_LINE_RE.match(l) for l in txt.splitlines()):
            P_.append(("Service '%s' (sets DISPLAY=:0)" % svc, "made Wayland-aware, then switched back on", True))
        else:
            P_.append(("Service '%s' (uses X11 tools)" % svc, "switched off for the update, back on if clean; "
                       "otherwise listed with the lines to port", False))
    hg = hook_guard_state()
    if hg["direct_hooks"] or a["hook_bg"]:
        P_.append(("%d game hooks" % len(hg["direct_hooks"]), "run through the hook guard (no launch can hang on them)",
                   True))
    if a["xorg_auth"]:
        n = len({h["file"] for h in a["xorg_auth"]})
        P_.append(("%d scripts read Xorg's -auth file" % n, "given a working Xwayland cookie fallback", True))
    if a["nonroot_x"] or a["xorg_auth"]:
        P_.append(("X11 apps run as the 'batocera' user", "Xwayland access granted at every boot", True))
    vo = [k for k in a["display"]["conf_keys"] if k.startswith("global.videooutput")]
    if vo:
        P_.append(("Pinned display output (%s)" % ", ".join(vo), "re-mapped to v3's port name if it changes", True))
    bins = [e for e in a["elfs"] if not e.get("bundled_runtime")]
    if bins:
        P_.append(("%d custom programs/libraries" % len(bins), "re-checked against v3's libraries; any that lose one "
                   "are listed", True))
    other = [f for f in by_file if not f.startswith(svc_dir)]
    if other:
        P_.append(("%d launchers/scripts use X11 tools (xdotool etc.)" % len(other),
                   "keep working through Xwayland; listed for testing", True))
    P_.append(("Safety net", "launch watchdog + rescue combo (Select+Start+L+R 3 s / Ctrl+Alt+End)", True))
    return P_


def cmd_scan(args):
    head("Scanning for things the x86-64-v3 update affects (read-only)")
    a = do_audit()
    write_json(SCAN_FILE, a)
    write_json(STATE_DIR + "/baseline-audit.json", a)
    blockers = [x for x in a["findings"] if x["severity"] == "blocker"]
    if a["system"]["board"] == V3_BOARD:
        say("You're already on x86-64-v3. Run: integrate")
        return 0
    for x in blockers:
        say("BLOCKER: %s\n  %s" % (x["title"], x["action"]))
    plan = plan_for(a)
    say("\nFound %d things that need handling:\n" % len(plan))
    for what, how, auto in plan:
        say("  %s %s\n      -> %s" % ("+" if auto else "!", what, how))
    say("\n  + = handled automatically by integrate     ! = needs a decision from you (listed at the end)")
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    st.update({"phase": "scanned", "scan_time": now()})
    write_json(STATE_DIR + "/state.json", st)
    if blockers:
        say("\nFix the blockers above first.")
        return 2
    say("\nNext: backup")
    return 0


def incompatible_paths(a, plugins):
    """Everything the update could break, as paths to back up."""
    paths = {BATOCERA_CONF, "/userdata/system/services", HOOK_DIR, "/userdata/system/hooks-guarded",
             "/userdata/system/configs/emulationstation", "/userdata/system/udev", "/userdata/system/custom.sh",
             "/userdata/system/bin", PLUGIN_DIR}
    for key in ("x11_refs", "xorg_auth", "nonroot_x", "hook_bg"):
        paths |= {h["file"] for h in a.get(key, [])}
    paths |= set(a.get("hook_backups", []))
    paths |= {e["path"] for e in a.get("elfs", []) if e.get("missing_libs") is not None
              and not e.get("bundled_runtime")}
    paths |= {x for p in plugins for x in p.get("backup_paths", [])}
    return sorted(x for x in paths if os.path.lexists(P(x)))


def cmd_backup_simple(args):
    a = load_json(SCAN_FILE)
    if not a:
        say("Run scan first.")
        return 2
    if a["system"]["board"] != V1_BOARD:
        say("Backup is for before the update (board is %s)." % a["system"]["board"])
        return 2
    plugins = load_plugins()[0]
    dest = args.dest or STATE_DIR + "/backups"
    os.makedirs(P(dest), exist_ok=True)
    sets = {"boot": ["/boot"], "incompatibles": incompatible_paths(a, plugins)}
    head("Backing up what the update affects")
    need = 0
    for name, roots in sets.items():
        n, size = estimate(iter_set(roots, set(SKIP_DIRS) if name != "boot" else set()))
        need += size
        say("  %-14s %6d files  %s" % (name, n, human(size)))
    free = shutil.disk_usage(P(dest)).free
    if free < need * 1.1 + 256 * 1024 ** 2:
        say("Not enough space in %s (%s free, %s needed)." % (dest, human(free), human(need)))
        return 2
    bdir = os.path.join(P(dest), "batocera-v3-backup-" + stamp())
    os.makedirs(bdir)
    with open(os.path.join(bdir, "audit.json"), "w") as fh:
        json.dump(a, fh)
    with open(os.path.join(bdir, "paths.txt"), "w") as fh:
        fh.write("\n".join(sets["incompatibles"]) + "\n")
    shutil.copy2(os.path.abspath(__file__), os.path.join(bdir, "batocera_v3_migrate.py"))
    manifest = {"tool_version": VERSION, "time": now(), "level": "incompatibles", "board": a["system"]["board"],
                "version": a["system"]["version"], "hostname": a["system"]["hostname"], "archives": {}}
    for name, roots in sets.items():
        fn = "boot.tar" if name == "boot" else name + ".tar.gz"
        path = os.path.join(bdir, fn)
        tar = tarfile.open(path, "w") if name == "boot" else tarfile.open(path, "w:gz", compresslevel=6)
        count, errors = 0, []
        with tar:
            for src in iter_set(roots, set(SKIP_DIRS) if name != "boot" else set()):
                try:
                    tar.add(src, arcname=UNP(src).lstrip("/"), recursive=False)
                    count += 1
                    _test_pause("backup-file")
                except OSError as e:
                    errors.append("%s: %s" % (UNP(src), e))
        manifest["archives"][fn] = {"set": name, "roots": roots[:50], "files": count,
                                    "bytes_out": os.path.getsize(path), "sha256": sha256_file(path),
                                    "errors": errors[:100]}
        say("  wrote %s (%d files)" % (fn, count))
    with open(os.path.join(bdir, "manifest.json"), "w") as fh:
        json.dump(manifest, fh, indent=2)
    ok = verify_backup_dir(bdir)
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    st.update({"backup_dir": UNP(bdir), "backup_time": manifest["time"], "backup_verified": ok,
               "phase": "backed-up" if ok else "backup-failed", "source_board": a["system"]["board"]})
    write_json(STATE_DIR + "/state.json", st)
    say("\nBackup %s: %s" % ("OK" if ok else "FAILED", UNP(bdir)))
    if ok:
        say("Next: update")
    return 0 if ok else 1


def cmd_update(args):
    """Park what can't survive the switch, then hand over to Batocera's own upgrader."""
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    if read(BOARD_FILE).strip() == V3_BOARD:
        say("Already on x86-64-v3. Next: integrate")
        return 0
    if not st.get("backup_verified"):
        say("Run scan and backup first.")
        return 2
    if st.get("phase") != "prepared":
        args.allow_nvidia = getattr(args, "allow_nvidia", False)
        rc = cmd_prepare(args, from_update=True)
        if rc:
            return rc
    if getattr(args, "now", False):
        args.skip_backup_check, args.manual, args.url, args.type, args.reboot = True, False, None, None, False
        st = load_json(STATE_DIR + "/state.json", {}) or {}
        st["phase"] = "backed-up"            # migrate re-checks; prepare's parking is idempotent
        write_json(STATE_DIR + "/state.json", st)
        return cmd_migrate(args)
    say("\nNow start the x86-64-v3 upgrade from Batocera's updates menu and reboot when it asks.\n"
        "Then run this tool again (or: integrate).")
    return 0


def patch_file_lines(path, tag, edit):
    """edit(lines) -> new lines or None. Backs up, checks bash syntax, restores on failure."""
    src = P(path)
    old = read(path)
    new = edit(old.split("\n"))
    if new is None or "\n".join(new) == old:
        return False
    fix_backup(path, tag)
    tmp = src + ".v3m.tmp"
    with open(tmp, "w") as fh:
        fh.write("\n".join(new))
    shutil.copymode(src, tmp)
    if not bash_ok(tmp):
        os.remove(tmp)
        raise ValueError("result failed bash -n")
    os.replace(tmp, src)
    return True


def integrate_xorg_auth(a, tag, done, manual):
    with_helper = False
    for f in sorted({h["file"] for h in a["xorg_auth"]}):
        if f.endswith(".py") or "v3-xauth" in read(f) or f.startswith(STATE_DIR) \
                or is_backup_name(os.path.basename(f)):
            continue
        if "x86-64-v3" in read(f):
            continue  # already handles the v3 image itself
        def edit(L):
            out, changed = [], False
            for line in L:
                out.append(line)
                m = AUTH_ASSIGN_RE.match(line)
                if m:
                    ind, var = m.group(1), m.group(2)
                    out.append('%s[ -n "${%s:-}" ] && [ -r "${%s:-}" ] || %s="$(%s 2>/dev/null)"  # v3-xauth'
                               % (ind, var, var, var, XAUTH_HELPER))
                    changed = True
            return out if changed else None
        try:
            if patch_file_lines(f, tag, edit):
                done.append("Xwayland cookie fallback added: %s" % f)
                with_helper = True
            elif "v3-xauth" not in read(f):
                manual.append("%s looks for Xorg's -auth file in a form I can't patch safely; "
                              "check it on v3" % f)
        except (OSError, ValueError) as e:
            manual.append("%s: not patched (%s)" % (f, e))
    if with_helper or a["xorg_auth"]:
        os.makedirs(os.path.dirname(P(XAUTH_HELPER)), exist_ok=True)
        with open(P(XAUTH_HELPER), "w") as fh:
            fh.write(XAUTH_HELPER_SRC)
        os.chmod(P(XAUTH_HELPER), 0o755)


def integrate_services(a, st, tag, done, manual):
    svc_dir = "/userdata/system/services/"
    parked = set((st.get("migrate_actions") or {}).get("parked_services", []))
    for svc in sorted(set(a["services"]["user_services"])):
        if is_backup_name(svc):
            continue
        f = svc_dir + svc
        txt = read(f)
        if not txt or "[batocera_v3_migrate]" in txt:
            continue
        if DESKTOP_RE.search(txt):
            if svc in parked or svc in a["services"]["enabled"]:
                manual.append("service %s is an X11 desktop; it can't run under Wayland and stays off" % svc)
            continue
        if not any(DISPLAY_LINE_RE.match(l) for l in txt.splitlines()):
            continue
        def edit(L):
            out, put = [], False
            for line in L:
                if DISPLAY_LINE_RE.match(line) and not put:
                    out.extend(WAYLAND_ENV_BLOCK.rstrip("\n").split("\n"))
                    put = True
                elif DISPLAY_LINE_RE.match(line):
                    continue
                else:
                    out.append(line)
            return out
        try:
            if patch_file_lines(f, tag, edit):
                done.append("service %s made Wayland-aware" % svc)
        except (OSError, ValueError) as e:
            manual.append("service %s: not patched (%s)" % (svc, e))


def old_overlay_tree(st):
    """Path to a readable tree of the old x86_64 overlay (mounted), or None. Returns (tree, cleanup)."""
    ma = st.get("migrate_actions") or {}
    img = ma.get("overlay_moved_to") or ""
    cand = [img] if img and not img.endswith(")") else []
    bdir = st.get("backup_dir")
    if bdir:
        cand.append(bdir + "/overlay.x86_64")
    for c in cand:
        if os.path.isdir(P(c)):
            return P(c), (lambda: None)          # test trees / already-extracted
        if os.path.isfile(P(c)):
            if TEST_MODE():
                return None, (lambda: None)
            mnt = "/tmp/v3m-old-overlay"
            os.makedirs(mnt, exist_ok=True)
            rc, out = run(["mount", "-o", "loop,ro", P(c), mnt], timeout=30)
            if rc == 0:
                journal_note({"op": "mounted", "path": mnt})
                return mnt, (lambda: run(["umount", mnt], timeout=30))
    if bdir and os.path.exists(P(bdir + "/boot.tar")):
        try:
            with tarfile.open(P(bdir + "/boot.tar")) as t:
                m = t.getmember("boot/boot/overlay")
                dst = P(STATE_DIR + "/overlay.x86_64")
                with t.extractfile(m) as src, open(dst, "wb") as out:
                    shutil.copyfileobj(src, out)
            st.setdefault("migrate_actions", {})["overlay_moved_to"] = STATE_DIR + "/overlay.x86_64"
            return old_overlay_tree(st)
        except (KeyError, tarfile.TarError, OSError):
            pass
    return None, (lambda: None)


def integrate_overlay(st, tag, done, manual):
    ma = st.get("migrate_actions") or {}
    if not ma.get("overlay_moved_to") or st.get("overlay_integrated"):
        return
    tree, cleanup = old_overlay_tree(st)
    if not tree:
        manual.append("old overlay could not be opened; it is still in your backup")
        return
    added, conflicts, broken = [], [], []
    try:
        for dp, dns, fns in os.walk(tree):
            for n in fns + [d for d in dns if os.path.islink(os.path.join(dp, d))]:
                srcp = os.path.join(dp, n)
                rel = "/" + os.path.relpath(srcp, tree)
                if OVERLAY_SKIP_RE.match(rel):
                    continue
                dst = P(rel)
                if os.path.lexists(dst):
                    same = (os.path.islink(srcp) and os.path.islink(dst) and os.readlink(srcp) == os.readlink(dst)) \
                        or (os.path.isfile(srcp) and os.path.isfile(dst) and not os.path.islink(srcp)
                            and sha256_file(srcp) == sha256_file(dst))
                    if not same:
                        conflicts.append(rel)
                    continue
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                if os.path.islink(srcp):
                    os.symlink(os.readlink(srcp), dst)
                else:
                    shutil.copy2(srcp, dst)
                added.append(rel)
                if elf_kind(dst):
                    ml = missing_libs(dst)
                    if ml:
                        broken.append("%s needs %s" % (rel, ", ".join(ml)))
    finally:
        cleanup()
    # drop restored ELFs that can't load on v3 (repeat: removing one can break another)
    pruned = []
    while True:
        bad = [r for r in added if elf_kind(P(r)) and missing_libs(P(r))]
        if not bad:
            break
        for r in bad:
            try:
                os.remove(P(r))
            except OSError:
                pass
            added.remove(r)
            pruned.append(r)
    for r in [r for r in added if os.path.islink(P(r)) and not os.path.exists(P(r))]:
        os.remove(P(r))              # links whose target was pruned
        added.remove(r)
        pruned.append(r)
    broken = []
    with open(P(STATE_DIR + "/overlay-restored.txt"), "w") as fh:
        fh.write("NOT RESTORED (need libraries v3 doesn't have):\n" + "\n".join(pruned) + "\n\n")
        fh.write("ADDED (v3 didn't have these):\n" + "\n".join(added) +
                 "\n\nKEPT v3's VERSION (your old one is in the backup):\n" + "\n".join(conflicts) + "\n")
    if added:
        if which("batocera-save-overlay"):
            if JOURNAL is not None:
                JOURNAL.file(P(OVERLAY))
            with critical("saving the new overlay to the boot partition"):
                rc, out = run(["batocera-save-overlay"], timeout=600)
            done.append("old overlay: %d files restored and saved to a new v3 overlay%s"
                        % (len(added), "" if rc == 0 else " (save-overlay rc=%d: %s)" % (rc, out[-200:])))
        else:
            done.append("old overlay: %d files restored (save them with batocera-save-overlay)" % len(added))
    if conflicts:
        manual.append("%d overlay files differ from v3's own; v3's were kept. List: %s/overlay-restored.txt"
                      % (len(conflicts), STATE_DIR))
    if pruned:
        done.append("old overlay: %d files left out (they need libraries v3 doesn't have; still in the backup)"
                    % len(pruned))
    st["overlay_integrated"] = now()


def cmd_integrate_all(args):
    if read(BOARD_FILE).strip() != V3_BOARD:
        say("Not on x86-64-v3 yet (board: %s). Run update first." % (read(BOARD_FILE).strip() or "?"))
        return 2
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    if not confirm("INTEGRATE", "Integrate everything the scan found into x86-64-v3? "
                   "Every file changed is backed up first."):
        return 1
    tag = stamp()
    done, manual = [], []
    head("Integrating")
    a = do_audit(quiet=True, light=True)

    def step(name, fn):
        try:
            fn()
        except Exception as e:  # one step failing must not stop the rest
            manual.append("%s step failed: %s" % (name, e))
        _test_pause("integrate-" + name)

    step("hook-backups", lambda: done.extend(fix_hook_backups(a, tag)) if a["hook_backups"] else None)
    step("hook-guard", lambda: done.extend(fix_hook_guard(a, tag)) if hook_guard_state()["direct_hooks"] else None)
    step("xorg-auth", lambda: integrate_xorg_auth(a, tag, done, manual))
    step("xwayland-access", lambda: done.extend(fix_xwayland_access(a, tag))
         if not xwayland_access_state()["enabled"] else None)
    step("services", lambda: integrate_services(a, st, tag, done, manual))
    step("overlay", lambda: integrate_overlay(st, tag, done, manual))
    write_json(STATE_DIR + "/state.json", st)
    step("watchdog", lambda: done.extend(fix_launch_watchdog(a, tag)) if not watchdog_state()["enabled"] else None)
    step("launcher", lambda: done.extend(launcher_install(tag))
         if launcher_state()["installed"] and not launcher_state()["current"] else None)
    # the original checks: display remap, re-enable clean services, plugins, library re-check
    R = do_integrate(True, ack_overlay=bool(st.get("overlay_integrated")))
    done += R["changes"]
    plugin_cmds = " ".join(c for p in load_plugins()[0] for c in p.get("post_integrate", []))
    for i in R["items"]:
        t = i["title"]
        if "binaries from before the migration are gone" in t:
            continue  # temp/cache files; listed in the report
        m = re.match(r"Service (\S+) was enabled before", t)
        if m and m.group(1) in plugin_cmds:
            continue  # switched off on purpose by an integration file
        if i["severity"] in ("blocker", "critical", "warn") and "Rollback" not in i["title"]:
            if "X11-only references remain" in i["title"]:
                continue  # covered by Xwayland; listed in the report
            m = re.match(r"Service (\S+) still parked", i["title"])
            if m and any(("service %s " % m.group(1)) in x for x in manual):
                continue  # already explained (X11 desktop)
            manual.append(i["title"])
    _test_pause("integrate-checks")
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    st["phase"] = "integrated" if not manual else "integrated-with-notes"
    write_json(STATE_DIR + "/state.json", st)
    rep_path = STATE_DIR + "/integrate-%s.md" % tag
    with open(P(rep_path), "w") as fh:
        fh.write("# x86-64-v3 integration %s\n\n## Integrated\n" % now() +
                 "".join("- %s\n" % d for d in done) + "\n## Needs you\n" +
                 ("".join("- %s\n" % m for m in manual) or "- nothing\n") +
                 "\n## Full check\n" + integrate_markdown(R))
    head("Done")
    say("Integrated:")
    for d in done:
        say("  + " + d)
    say("\nNeeds you:" if manual else "\nNothing needs you.")
    for m in manual:
        say("  ! " + m)
    say("\nReport: %s\nReboot once so every service starts the v3 way, then play-test." % rep_path)
    return 0


def cmd_auto(args):
    """No arguments: run whichever step comes next."""
    st = load_json(STATE_DIR + "/state.json", {}) or {}
    board = read(BOARD_FILE).strip()
    say("batocera_v3_migrate %s  |  board %s  |  step: %s" % (VERSION, board or "?", st.get("phase") or "start"))
    if board == V3_BOARD:
        if str(st.get("phase", "")).startswith("integrated"):
            say("Already integrated. Re-run with: integrate   (safe to repeat)")
            return 0
        return cmd_integrate_all(args)
    if board != V1_BOARD:
        say("This tool is for Batocera's x86_64 image (board: %s)." % board)
        return 2
    if not load_json(SCAN_FILE) or st.get("phase") in (None, "", "start"):
        rc = cmd_scan(args)
        if rc:
            return rc
        st = load_json(STATE_DIR + "/state.json", {}) or {}
    if not st.get("backup_verified"):
        args.dest = getattr(args, "dest", None)
        rc = cmd_backup_simple(args)
        if rc:
            return rc
    return cmd_update(args)


# --------------------------------------------------------------------------
# Ports launcher: "V3 Migration" in ES's Ports list opens a controller-driven menu
# --------------------------------------------------------------------------
LAUNCHER_SH = "/userdata/roms/ports/V3 Migration.sh"
LAUNCHER_KEYS = LAUNCHER_SH + ".keys"
LAUNCHER_MARK = "# v3-migrate-launcher"
MENU_LOG = "/userdata/system/logs/v3-migrate-menu.log"
MENU_LAST = STATE_DIR + "/menu-last-run.log"
MENU_RUN = STATE_DIR + "/menu-run.json"
MENU_TITLE = "x86-64-v3 Migration"
TOOL_PLACES = ["/userdata/system/add-ons/v3-migrate/batocera_v3_migrate.py",
               "/userdata/system/batocera_v3_migrate.py"]

LAUNCHER_SRC = """#!/bin/bash
%(mark)s
# x86-64-v3 Migration menu, opened from ES's Ports list. Written by
#   batocera_v3_migrate.py launcher install      (remove with: launcher remove)
# Controller (through the .keys file): D-pad/stick move, OK and back are the same buttons
# as in ES (they follow "switch confirm & cancel buttons"), Start = OK, Select = back,
# L1/R1 = page up/down.
TOOL=%(tool)s
for t in "$TOOL" %(places)s; do
    if [ -f "$t" ]; then TOOL="$t"; break; fi
done
export DISPLAY="${DISPLAY:-:0.0}"
LOG=/userdata/system/logs/v3-migrate-menu.log
mkdir -p /userdata/system/logs
if [ ! -f "$TOOL" ]; then
    echo "$(date '+%%F %%T') launcher: migration tool not found" >>"$LOG"
    curl -s -m 5 --data "x86-64-v3 Migration: the tool is missing. Reinstall it from BUA." \\
        http://127.0.0.1:1234/messagebox >/dev/null 2>&1
    exit 1
fi
# the full-screen menu (pygame, like the BUA app); exit code 3 = it can't start here
python3 -B "$TOOL" gui 2>>"$LOG"
[ $? -ne 3 ] && exit 0
if command -v xterm >/dev/null 2>&1; then
    xterm -fs 20 -maximized -fg white -bg black -fa DejaVuSansMono -en UTF-8 \\
        -T "x86-64-v3 Migration" -e python3 -B "$TOOL" menu 2>>"$LOG"
    exit 0
fi
echo "$(date '+%%F %%T') launcher: xterm not found" >>"$LOG"
curl -s -m 5 --data "x86-64-v3 Migration needs xterm, which this system lacks. Over SSH run: python3 $TOOL" \\
    http://127.0.0.1:1234/messagebox >/dev/null 2>&1
exit 1
"""

ES_SETTINGS = "/userdata/system/configs/emulationstation/es_settings.cfg"


def es_ok_button():
    """The pad button ES uses for OK: "b" (south), or "a" (east) when "switch confirm & cancel
    buttons" (InvertButtons) is on - exactly as Batocera's EmulationStation decides it."""
    m = re.search(r'<bool\s+name="InvertButtons"\s+value="(\w+)"', read(ES_SETTINGS))
    return "a" if m and m.group(1).lower() == "true" else "b"


def launcher_keys(ok=None):
    """The Ports .keys map: ES's OK button -> Enter, its back button -> Esc, like ES itself."""
    ok = ok or es_ok_button()
    back = "a" if ok == "b" else "b"
    return {"actions_player1": [
        {"trigger": "up", "type": "key", "target": "KEY_UP"},
        {"trigger": "down", "type": "key", "target": "KEY_DOWN"},
        {"trigger": "left", "type": "key", "target": "KEY_LEFT"},
        {"trigger": "right", "type": "key", "target": "KEY_RIGHT"},
        {"trigger": "joystick1up", "type": "key", "target": "KEY_UP"},
        {"trigger": "joystick1down", "type": "key", "target": "KEY_DOWN"},
        {"trigger": "joystick1left", "type": "key", "target": "KEY_LEFT"},
        {"trigger": "joystick1right", "type": "key", "target": "KEY_RIGHT"},
        {"trigger": ok, "type": "key", "target": "KEY_ENTER"},
        {"trigger": "start", "type": "key", "target": "KEY_ENTER"},
        {"trigger": back, "type": "key", "target": "KEY_ESC"},
        {"trigger": "select", "type": "key", "target": "KEY_ESC"},
        {"trigger": "x", "type": "key", "target": "KEY_TAB"},
        {"trigger": "pageup", "type": "key", "target": "KEY_PAGEUP"},
        {"trigger": "pagedown", "type": "key", "target": "KEY_PAGEDOWN"},
    ]}


def launcher_keys_text(ok=None):
    return json.dumps(launcher_keys(ok), indent=4) + "\n"


def keys_ok_button():
    """Which pad button the installed .keys file turns into Enter ("a"/"b"), or None."""
    try:
        acts = json.loads(read(LAUNCHER_KEYS) or "{}").get("actions_player1", [])
    except ValueError:
        return None
    return next((x.get("trigger") for x in acts if x.get("target") == "KEY_ENTER"
                 and x.get("trigger") in ("a", "b")), None)


def keys_out_of_date():
    """True when ES's OK/back buttons were switched since the .keys file was written. evmapy reads
    that file when the port starts, so the fix (rewriting it) applies from the next start."""
    loaded = keys_ok_button()
    if not loaded or loaded == es_ok_button():
        return False
    try:
        launcher_install()
    except (OSError, RuntimeError):
        pass
    return True


def tool_path():
    return UNP(os.path.abspath(__file__))


def launcher_text(tool=None):
    import shlex
    tool = tool or tool_path()
    return LAUNCHER_SRC % {"mark": LAUNCHER_MARK, "tool": shlex.quote(tool),
                           "places": " ".join(shlex.quote(p) for p in TOOL_PLACES if p != tool)}


def launcher_state():
    sh = read(LAUNCHER_SH)
    return {"installed": LAUNCHER_MARK in sh, "present": os.path.lexists(P(LAUNCHER_SH)),
            "current": sh == launcher_text() and read(LAUNCHER_KEYS) == launcher_keys_text()}


def es_reload_games():
    if TEST_MODE():
        return
    try:
        urllib.request.urlopen("http://127.0.0.1:1234/reloadgames", timeout=5).read()
    except Exception:
        pass  # ES not running (or no web API): the entry shows after the next ES start


def launcher_install(tag=None):
    st = launcher_state()
    if st["present"] and not st["installed"]:
        raise RuntimeError("%s exists and was not written by this tool; not touching it" % LAUNCHER_SH)
    tag = tag or stamp()
    out = []
    keys = launcher_keys_text()
    for path, text, mode in ((LAUNCHER_SH, launcher_text(), 0o755), (LAUNCHER_KEYS, keys, 0o644)):
        if read(path) == text:
            continue
        if os.path.exists(P(path)):
            fix_backup(path, tag)
        os.makedirs(os.path.dirname(P(path)), exist_ok=True)
        tmp = P(path) + ".v3m.tmp"
        with open(tmp, "w") as fh:
            fh.write(text)
        os.chmod(tmp, mode)
        os.replace(tmp, P(path))
        out.append("wrote %s" % path)
    if not bash_ok(P(LAUNCHER_SH)):
        raise RuntimeError("the launcher failed bash -n; see %s" % LAUNCHER_SH)
    if out:
        es_reload_games()
        out.append("'V3 Migration' is in Ports (runs %s)" % tool_path())
    return out


def launcher_remove():
    if not launcher_state()["installed"]:
        return []
    out = []
    for path in (LAUNCHER_SH, LAUNCHER_KEYS):
        if os.path.lexists(P(path)):
            os.remove(P(path))
            out.append("removed %s" % path)
    es_reload_games()
    return out


def cmd_launcher(args):
    try:
        if args.action == "install":
            out = launcher_install() or ["already up to date: %s" % LAUNCHER_SH]
        elif args.action == "remove":
            out = launcher_remove() or ["not installed"]
        else:
            s = launcher_state()
            out = ["%s: %s" % (LAUNCHER_SH, "installed" + ("" if s["current"] else " (older version; "
                                                                "run: launcher install)") if s["installed"]
                               else "present, not ours" if s["present"] else "not installed")]
    except (OSError, RuntimeError) as e:
        say("Launcher: %s" % e)
        return 1
    for line in out:
        say("  " + line)
    return 0


# ---- the menu itself (runs in xterm; dialog if present, plain text otherwise)
class DialogUI:
    def __init__(self, exe):
        self.exe = exe

    def _run(self, args):
        env = dict(os.environ, DIALOGRC=os.environ.get("DIALOGRC", "/userdata/system/add-ons/.dialogrc"))
        r = subprocess.run([self.exe, "--backtitle", "%s  (tool v%s)" % (MENU_TITLE, VERSION)] + args,
                           stderr=subprocess.PIPE, env=env)
        return r.returncode, r.stderr.decode(errors="replace").strip()

    def menu(self, text, items, default=None, cancel="Back"):
        args = ["--title", MENU_TITLE, "--no-tags", "--ok-label", "Select", "--cancel-label", cancel]
        if default:
            args += ["--default-item", default]
        flat = [x for k, label in items for x in (k, label)]
        rc, out = self._run(args + ["--menu", text, "0", "0", str(min(len(items), 12))] + flat)
        return out if rc == 0 else None

    def yesno(self, text):
        return self._run(["--title", MENU_TITLE, "--yesno", text, "0", "0"])[0] == 0

    def msgbox(self, text):
        self._run(["--title", MENU_TITLE, "--msgbox", text, "0", "0"])

    def textbox(self, path, title):
        self._run(["--title", title, "--exit-label", "Back", "--textbox", path, "-1", "-1"])

    def clear(self):
        sys.stdout.write("\033[2J\033[H")
        sys.stdout.flush()


class PlainUI:
    """No dialog: numbered menus for a keyboard (or SSH)."""

    def _ask(self, prompt):
        try:
            return input(prompt).strip()
        except EOFError:
            return ""

    def menu(self, text, items, default=None, cancel="Back"):
        say("\n" + text)
        for n, (k, label) in enumerate(items, 1):
            say("  %d) %s%s" % (n, label, "   <- next" if k == default else ""))
        ans = self._ask("Number (Enter = %s): " % cancel.lower())
        return items[int(ans) - 1][0] if ans.isdigit() and 0 < int(ans) <= len(items) else None

    def yesno(self, text):
        return self._ask("\n%s\n[y/N] " % text).lower() in ("y", "yes")

    def msgbox(self, text):
        self._ask("\n%s\n(Enter) " % text)

    def textbox(self, path, title):
        say("\n== %s ==" % title)
        say(read(path))
        self._ask("(Enter) ")

    def clear(self):
        pass


def menu_ui():
    exe = os.environ.get("V3M_DIALOG") or shutil.which("dialog")
    return DialogUI(exe) if exe else PlainUI()


def pid_alive(pid, marker=None):
    try:
        os.kill(int(pid), 0)
        if marker:
            with open("/proc/%d/cmdline" % int(pid), "rb") as fh:
                return marker.encode() in fh.read()
        return True
    except (OSError, ValueError, TypeError):
        return False


def backup_targets():
    """(path, label) for every mounted drive under /media, plus the internal default."""
    out, mounts = [], {}
    for line in read("/proc/mounts").splitlines():
        f = line.split()
        if len(f) >= 3:
            mounts[f[1].replace("\\040", " ")] = f[2]
    media = P("/media")
    for n in sorted(os.listdir(media)) if os.path.isdir(media) else []:
        path = "/media/" + n
        if path not in mounts and not TEST_MODE():
            continue
        try:
            du = shutil.disk_usage(P(path))
        except OSError:
            continue
        out.append((path, "%s free of %s  (%s)" % (human(du.free), human(du.total), mounts.get(path, "?"))))
    internal = STATE_DIR + "/backups"
    try:
        free = human(shutil.disk_usage(P("/userdata")).free)
    except OSError:
        free = "?"
    out.append((internal, "internal /userdata (%s free) - no protection if this disk fails" % free))
    return out


def menu_steps(st, board):
    """[(key, label, argv, confirm text)] for this board and phase; plus the suggested next key."""
    phase = st.get("phase") or "start"
    if board == V3_BOARD:
        again = phase.startswith("integrated")
        steps = [("integrate", "Integrate%s" % (" again (safe to repeat)" if again else
                                                 "  - finish the move to x86-64-v3"), ["integrate"],
                  "Integrate everything the update affected into x86-64-v3: hooks, Xwayland access, "
                  "services, overlay files, display output, launch watchdog and rescue combo.\n\n"
                  "Every file it changes is backed up first. Run it?")]
        nxt = "integrate"
    elif board == V1_BOARD:
        scanned = bool(load_json(SCAN_FILE)) and phase != "start"
        backed = bool(st.get("backup_verified"))
        steps = [("scan", "Scan%s  - find what the update affects (read-only)" % (" again" if scanned else ""),
                  ["scan"], "Scan the system for everything the x86-64-v3 update affects?\n\n"
                  "Read-only. It takes a few minutes."),
                 ("backup", "Back up  - those files + the boot partition (for rollback)", None, None)]
        if phase == "prepared":
            steps += [("update-now", "Update now  - download and install x86-64-v3 from here", ["update", "--now"],
                       "Download and install the x86-64-v3 image now with Batocera's upgrader?\n\n"
                       "When it finishes, reboot, then open V3 Migration again to integrate."),
                      ("unprepare", "Undo prepare  - put the overlay and services back", ["unprepare"],
                       "Undo prepare: put the parked overlay and services back as they were?")]
        else:
            steps += [("prepare", "Prepare for the update  - then use Updates & Downloads", ["update"],
                       "Prepare for the update: move the x86_64 overlay into the backup and park the "
                       "X11-only services (both take effect at the next boot).\n\n"
                       "Afterwards start the x86-64-v3 upgrade from Updates & Downloads. Run it?")]
        nxt = "scan" if not scanned else "backup" if not backed else \
            "update-now" if phase == "prepared" else "prepare"
    else:
        steps, nxt = [], None
    steps += [("status", "Status  - where the migration is", ["status"], None),
              ("log", "Last result  - the output of the last step", None, None)]
    return steps, nxt


def step_start(argv, label, append=False):
    """Start one step of this tool in its own session, so closing the window (or the exit
    hotkey) can't cut it off, with a journal so it can be cancelled and undone.
    Output goes to MENU_LAST. Returns the Popen."""
    os.makedirs(os.path.dirname(P(MENU_LAST)), exist_ok=True)
    os.makedirs(os.path.dirname(P(MENU_LOG)), exist_ok=True)
    cmd = [sys.executable, "-u", "-B", os.path.abspath(__file__), "--yes"]
    if TEST_MODE():
        cmd += ["--root", ROOT]
    if argv[0] != "undo-step":
        cmd += ["--journal"]
    cmd += argv
    with open(P(MENU_LAST), "a" if append else "w") as fh:
        fh.write("%s  %s: %s\n\n" % (now(), label, " ".join(argv)))
        fh.flush()
        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=fh, stderr=subprocess.STDOUT,
                                start_new_session=True, close_fds=True)
    write_json(MENU_RUN, {"pid": proc.pid, "label": label, "argv": argv, "start": now(),
                          "marker": os.path.basename(__file__)})
    return proc


def step_finish(rc):
    try:
        os.remove(P(MENU_RUN))
    except OSError:
        pass
    with open(P(MENU_LAST), "a") as fh:
        fh.write("\n%s  exit code %s\n" % (now(), rc))
    with open(P(MENU_LOG), "a") as fh:
        fh.write(read(MENU_LAST) + "\n")


class StepCancel:
    """Cancel for a running step: ask it to stop (it finishes any part that writes /boot first),
    force it if it ignores that, then put back what it changed (undo-step).
    tick() drives it; state is running / stopping / undoing / done."""
    FORCE_AFTER = 20.0

    def __init__(self, pid, poll):
        import time
        self.time = time
        self.pid, self.poll = pid, poll
        self.state, self.rc, self.undo_rc, self.undo = "running", None, None, None
        self.asked = None

    def request(self):
        if self.state != "running":
            return
        self.state, self.asked = "stopping", self.time.time()
        try:
            os.kill(self.pid, signal.SIGTERM)
        except OSError:
            pass

    def waiting_for(self):
        return journal_critical() if self.state == "stopping" else ""

    def tick(self):
        if self.state in ("running", "stopping"):
            rc = self.poll()
            if rc is None:
                if self.state == "stopping" and not journal_critical() and \
                        self.time.time() - self.asked > self.FORCE_AFTER:
                    try:
                        os.killpg(self.pid, signal.SIGKILL)   # it ignored the request: stop it and its helpers
                    except OSError:
                        pass
                return None
            self.rc = rc
            if self.state == "stopping" and journal_pending():
                with open(P(MENU_LAST), "a") as fh:
                    fh.write("\n%s  stopped (code %s)\n\n" % (now(), rc))
                self.undo = step_start(["undo-step"], "Cancel: putting things back", append=True)
                self.state = "undoing"
                return None
            self.state = "done"
            return rc
        if self.state == "undoing":
            rc = self.undo.poll()
            if rc is None:
                return None
            self.undo_rc, self.state = rc, "done"
            return self.rc
        return self.rc

    @property
    def cancelled(self):
        return self.undo is not None


def step_running():
    """The MENU_RUN record of a step that is still running (started by an earlier menu), or None."""
    info = load_json(MENU_RUN)
    if info and pid_alive(info.get("pid"), info.get("marker")):
        return info
    if info:
        try:
            os.remove(P(MENU_RUN))
        except OSError:
            pass
    return None


def menu_run(ui, argv, label):
    """Run one step, showing its output live (Esc = cancel and put back); then show the result."""
    ui.clear()
    say("== %s ==  (Esc = cancel; the step finishes even if this window closes)\n" % label)
    proc = step_start(argv, label)
    ctl = StepCancel(proc.pid, proc.poll)

    def on_key(ch):
        if ch == "\x1b" and ctl.state == "running" and ui.yesno(
                "Cancel %s?\n\nIt stops and puts back everything this step changed, so your system is as "
                "it was before you started it." % label):
            ctl.request()
            ui.clear()
            say("== Cancelling %s: stopping, then putting back what it changed ==\n" % label)
    rc = menu_follow(ctl.tick, on_key=on_key if argv[0] != "undo-step" else None)
    step_finish(rc)
    if ctl.cancelled:
        title = "%s: cancelled, %s" % (label, "all put back" if ctl.undo_rc == 0 else "undo incomplete")
    else:
        title = "%s: %s" % (label, "done" if rc == 0 else "stopped (code %s)" % rc)
    ui.textbox(P(MENU_LAST), title)
    return rc


def menu_follow(poll, interval=0.3, on_key=None):
    """Copy MENU_LAST to the terminal as it grows until poll() returns a code (not None).
    on_key(ch) gets keys typed meanwhile (terminal only)."""
    tty = None
    if on_key and sys.stdin.isatty():
        import termios
        import tty as _tty
        tty = termios.tcgetattr(sys.stdin)
        _tty.setcbreak(sys.stdin)
    try:
        return _menu_follow(poll, interval, on_key if tty else None)
    finally:
        if tty:
            import termios
            termios.tcsetattr(sys.stdin, termios.TCSADRAIN, tty)


def _menu_follow(poll, interval, on_key):
    import select
    import time
    pos, rc = 0, None
    while True:
        rc = poll()
        try:
            with open(P(MENU_LAST), "rb") as fh:
                fh.seek(pos)
                chunk = fh.read()
            pos += len(chunk)
            if chunk:
                sys.stdout.write(chunk.decode(errors="replace"))
                sys.stdout.flush()
        except OSError:
            pass
        if rc is not None:
            return rc
        if on_key:
            if select.select([sys.stdin], [], [], interval)[0]:
                ch = os.read(sys.stdin.fileno(), 1).decode(errors="replace")
                on_key(ch)
        else:
            time.sleep(interval)


def cmd_menu(args):
    ui = menu_ui()
    if keys_out_of_date():
        ui.msgbox("ES's confirm and back buttons were switched since this menu was last opened, so the "
                  "buttons here don't match ES yet.\n\nThat is fixed now: close this and open "
                  "V3 Migration again.")
        return 0
    run_info = step_running()
    if run_info:
        ui.clear()
        say("== %s is still running (started %s) ==\n" % (run_info.get("label"), run_info.get("start")))
        pid, marker = run_info["pid"], run_info.get("marker")
        menu_follow(lambda: None if pid_alive(pid, marker) else 0, interval=1)
        try:
            os.remove(P(MENU_RUN))
        except OSError:
            pass
        ui.textbox(P(MENU_LAST), "%s: finished" % run_info.get("label"))
    j = journal_pending()
    if j and not step_running():
        if ui.yesno("The last step ('%s') didn't finish (cancelled, a power cut, or a crash).\n\n"
                    "Put back what it changed?" % j.get("label")):
            menu_run(ui, ["undo-step"], "Putting things back")
        elif ui.yesno("Keep its changes instead? This can't be undone afterwards."):
            menu_run(ui, ["undo-step", "--discard"], "Keeping the changes")
    while True:
        st = load_json(STATE_DIR + "/state.json", {}) or {}
        board = read(BOARD_FILE).strip()
        steps, nxt = menu_steps(st, board)
        if board not in (V1_BOARD, V3_BOARD):
            ui.msgbox("This is for Batocera on PCs (x86_64 or x86-64-v3).\n\nThis system: %s" % (board or "unknown"))
            return 2
        head_text = "Board: %s    Step: %s\nNext: %s" % (
            board, st.get("phase") or "start", next((l.split("  -")[0] for k, l, _, _ in steps if k == nxt), "-"))
        choice = ui.menu(head_text, [(k, l) for k, l, _, _ in steps], default=nxt, cancel="Exit")
        if choice is None:
            return 0
        key, label, argv, question = next(s for s in steps if s[0] == choice)
        if key == "log":
            if os.path.exists(P(MENU_LAST)):
                ui.textbox(P(MENU_LAST), "Last result")
            else:
                ui.msgbox("Nothing has run from this menu yet.")
            continue
        if key == "backup":
            targets = backup_targets()
            dest = ui.menu("Where should the backup go? An external drive is safest.\n"
                           "Needed: the files the scan found plus the boot partition (about 5 GB).",
                           targets, default=targets[0][0])
            if dest is None:
                continue
            argv = ["backup"] + (["--dest", dest] if dest != STATE_DIR + "/backups" else [])
            question = "Back up to %s?\n\nThis can take a while on a slow drive." % dest
        if question and not ui.yesno(question):
            continue
        rc = menu_run(ui, argv, label.split("  -")[0])
        if key == "update-now" and rc == 0 and ui.yesno("The x86-64-v3 image is installed.\n\nReboot now?"):
            if not TEST_MODE():
                subprocess.run(["sync"])
                subprocess.run(["reboot"])
            return 0


# ---- the full-screen menu (pygame, styled after the BUA app); the dialog menu is the fallback
GUI_UNAVAILABLE = 3          # exit code the launcher reads as "use the terminal menu instead"
GUI_BG = (10, 13, 18)
GUI_CARD = (27, 35, 45)
GUI_CARD_HI = (36, 48, 62)
GUI_ACCENT = (58, 166, 255)
GUI_FG = (236, 242, 248)
GUI_MUTED = (139, 152, 166)
GUI_SUCCESS = (76, 205, 140)
GUI_DANGER = (232, 96, 96)
GUI_FOOTER = (6, 8, 12)
GUI_TILE_COLORS = {"scan": (64, 116, 214), "backup": (136, 92, 214), "prepare": (214, 118, 62),
                   "update-now": (40, 156, 136), "unprepare": (190, 150, 36), "integrate": (40, 156, 136),
                   "status": (52, 138, 186), "log": (92, 148, 58), "drive": (64, 116, 214)}
GUI_TILE_TEXT = {"scan": "1", "backup": "2", "prepare": "3", "update-now": "4", "unprepare": "↺",
                 "integrate": "4", "status": "i", "log": "≡", "drive": "▤"}
# What each controller family prints on its south and east buttons. ES's OK is the south button
# (its "b"), or the east one ("a") when ES's confirm/cancel buttons are switched; the launcher's
# .keys file turns OK into Enter and back into Esc to match.
GUI_PADS = {"nintendo": {"south": "B", "east": "A", "pgup": "L", "pgdn": "R"},
            "xbox": {"south": "A", "east": "B", "pgup": "LB", "pgdn": "RB"},
            "playstation": {"south": "\u2715", "east": "\u25cb", "pgup": "L1", "pgdn": "R1"},
            "keyboard": {"south": "Enter", "east": "Esc", "pgup": "PgUp", "pgdn": "PgDn"}}
NO_CONFIRM_DEFAULT = ("update-now", "unprepare")   # these dialogs start on "No"
CANCEL_NOTES = {
    "update-now": "If Batocera's upgrader has already started, it finishes first; then your previous boot "
                  "partition is written back from the backup.",
    "integrate": "If the new overlay was already saved, the previous one is put back on the boot partition.",
    "prepare": "If the overlay is being moved, that finishes first; then it is put back.",
    "backup": "The unfinished backup is deleted.",
}


class MigrateGui:
    def __init__(self, pg, windowed=False, script=None, shots=None):
        self.pg = pg
        os.environ.setdefault("SDL_VIDEO_WINDOW_POS", "0,0")
        if windowed:
            self.screen = pg.display.set_mode((1280, 720))
        else:
            info = pg.display.Info()
            self.screen = pg.display.set_mode((info.current_w, info.current_h), pg.NOFRAME)
        pg.display.set_caption(MENU_TITLE)
        pg.mouse.set_visible(False)
        pg.key.set_repeat(350, 70)
        self.W, self.H = self.screen.get_size()
        self.k = max(1.0, min(self.W / 1280.0, self.H / 720.0))
        f = lambda size, bold=False, mono=False: pg.font.SysFont(
            "DejaVu Sans Mono" if mono else "DejaVu Sans", self.s(size), bold=bold)
        self.f = {"hero": f(30, True), "tile": f(20, True), "body": f(17), "small": f(14),
                  "mono": f(15, mono=True), "glyph": f(26, True), "key": f(14, True)}
        self.bg = self._background()
        self.clock = pg.time.Clock()
        self.pad = os.environ.get("V3M_PAD") if os.environ.get("V3M_PAD") in GUI_PADS else self._pad_style()
        self.ok_btn = es_ok_button()
        self.script = list(script or [])
        self.shots, self.shot_n, self.next_inject = shots, 0, 0

    def s(self, n):
        return int(round(n * self.k))

    # ---------- drawing helpers (same look as the BUA app)
    def _background(self):
        pg = self.pg
        surf = pg.Surface((self.W, self.H)).convert()
        top = (16, 22, 32)
        for i in range(self.H):
            t = i / max(1, self.H - 1)
            pg.draw.line(surf, tuple(int(top[c] + (GUI_BG[c] - top[c]) * t) for c in range(3)), (0, i), (self.W, i))
        glow = pg.Surface((64, 36), pg.SRCALPHA)
        for r in range(28, 0, -1):
            pg.draw.circle(glow, (*GUI_ACCENT, int(5 * (28 - r) / 28) + 1), (8, 4), r)
        surf.blit(pg.transform.smoothscale(glow, (self.W, self.H)), (0, 0))
        return surf

    def _pad_style(self):
        pg = self.pg
        try:
            pg.joystick.init()
            names = " ".join((pg.joystick.Joystick(i).get_name() or "").lower()
                             for i in range(pg.joystick.get_count()))
        except Exception:
            names = ""
        if not names.strip():
            return "keyboard"
        if any(x in names for x in ("sony", "playstation", "dualsense", "dualshock")):
            return "playstation"
        if any(x in names for x in ("nintendo", "pro controller", "switch", "joy-con")):
            return "nintendo"
        return "xbox"

    def text(self, txt, font, color, pos):
        img = self.f[font].render(txt, True, color)
        self.screen.blit(img, pos)
        return img.get_width()

    def fit(self, txt, font, width):
        fnt = self.f[font]
        if fnt.size(txt)[0] <= width:
            return txt
        while txt and fnt.size(txt + "...")[0] > width:
            txt = txt[:-1]
        return txt.rstrip() + "..."

    def wrap(self, txt, font, width):
        out = []
        for para in txt.split("\n"):
            line = ""
            for word in para.split(" "):
                trial = (line + " " + word).strip()
                if self.f[font].size(trial)[0] <= width or not line:
                    line = trial
                else:
                    out.append(line)
                    line = word
            out.append(line)
        return out

    def tile(self, rect, selected=False, radius=None, fill=None, accent=None):
        pg = self.pg
        radius = self.s(14) if radius is None else radius
        shadow = pg.Surface(rect.size, pg.SRCALPHA)
        pg.draw.rect(shadow, (0, 0, 0, 110), shadow.get_rect(), border_radius=radius)
        self.screen.blit(shadow, rect.move(0, self.s(5)))
        pg.draw.rect(self.screen, fill or (GUI_CARD_HI if selected else GUI_CARD), rect, border_radius=radius)
        if selected:
            pg.draw.rect(self.screen, accent or GUI_ACCENT, rect, width=max(2, self.s(3)), border_radius=radius)

    def chip(self, txt, color, right_top=None, left_mid=None):
        img = self.f["body"].render(txt, True, GUI_FG)
        r = self.pg.Rect(0, 0, img.get_width() + self.s(28), img.get_height() + self.s(12))
        if right_top:
            r.topright = right_top
        else:
            r.midleft = left_mid
        self.pg.draw.rect(self.screen, color, r, border_radius=r.h // 2)
        self.screen.blit(img, img.get_rect(center=r.center))
        return r

    def header(self, title, subtitle=""):
        m, y = self.s(48), self.s(28)
        self.text(self.fit(title, "hero", self.W - 2 * m - self.s(260)), "hero", GUI_FG, (m, y))
        y += self.f["hero"].get_height() + self.s(4)
        if subtitle:
            self.text(self.fit(subtitle, "body", self.W - 2 * m), "body", GUI_MUTED, (m, y))
            y += self.f["body"].get_height()
        return y + self.s(24)

    def button_glyph(self, x, y, name):
        """A round controller button (or a keycap) with its label; returns the width."""
        pg, fnt = self.pg, self.f["key"]
        img = fnt.render(name, True, GUI_FG)
        h = self.f["body"].get_height() + self.s(6)
        w = max(h, img.get_width() + self.s(14))
        r = pg.Rect(x, y - self.s(3), w, h)
        pg.draw.rect(self.screen, (48, 62, 80), r, border_radius=h // 2 if len(name) <= 2 else self.s(6))
        pg.draw.rect(self.screen, (98, 116, 138), r, width=max(1, self.s(2)),
                     border_radius=h // 2 if len(name) <= 2 else self.s(6))
        self.screen.blit(img, img.get_rect(center=r.center))
        return w

    def footer(self, hints, status=""):
        """hints: [(button key in GUI_PADS, label)]"""
        pg = self.pg
        h = self.s(54)
        pg.draw.rect(self.screen, GUI_FOOTER, (0, self.H - h, self.W, h))
        pg.draw.line(self.screen, (34, 45, 58), (0, self.H - h), (self.W, self.H - h), 1)
        y = self.H - h + (h - self.f["body"].get_height()) // 2
        names = dict(GUI_PADS[self.pad])
        if self.pad == "keyboard":
            names.update(ok="Enter", back="Esc")
        else:
            ok_pos = "east" if self.ok_btn == "a" else "south"
            names.update(ok=names[ok_pos], back=names["south" if ok_pos == "east" else "east"])
        parts = []
        for key, label in hints:
            parts.append((names.get(key, key), label))
        widths = [self.f["body"].size(lbl)[0] + max(self.f["body"].get_height() + self.s(6),
                                                     self.f["key"].size(n)[0] + self.s(14)) + self.s(10)
                  for n, lbl in parts]
        x = self.W - self.s(48) - sum(widths) - self.s(36) * max(0, len(parts) - 1)
        if status:
            self.text(self.fit(status, "body", max(0, x - self.s(96))), "body", GUI_MUTED, (self.s(48), y))
        for (n, lbl), w in zip(parts, widths):
            gw = self.button_glyph(x, y, n)
            self.text(lbl, "body", GUI_FG, (x + gw + self.s(10), y))
            x += w + self.s(36)

    def row(self, rect, selected, key, title, subtitle="", badge=None):
        pg = self.pg
        self.tile(rect, selected, radius=self.s(12))
        mono = rect.h - self.s(16)
        mrect = pg.Rect(rect.x + self.s(8), rect.y + self.s(8), int(mono * 1.25), mono)
        pg.draw.rect(self.screen, GUI_TILE_COLORS.get(key, (64, 116, 214)), mrect, border_radius=self.s(10))
        g = self.f["glyph"].render(GUI_TILE_TEXT.get(key, "?"), True, GUI_FG)
        self.screen.blit(g, g.get_rect(center=mrect.center))
        x = mrect.right + self.s(18)
        right = rect.right - self.s(18)
        if badge:
            img = self.f["small"].render(badge[0], True, GUI_FG)
            b = pg.Rect(0, 0, img.get_width() + self.s(20), img.get_height() + self.s(8))
            b.midright = (right, rect.centery)
            pg.draw.rect(self.screen, badge[1], b, border_radius=b.h // 2)
            self.screen.blit(img, img.get_rect(center=b.center))
            right = b.x - self.s(14)
        w = right - x
        if subtitle:
            y = rect.centery - (self.f["tile"].get_height() + self.f["small"].get_height() + self.s(2)) // 2
            self.text(self.fit(title, "tile", w), "tile", GUI_FG, (x, y))
            self.text(self.fit(subtitle, "small", w), "small", GUI_MUTED,
                      (x, y + self.f["tile"].get_height() + self.s(2)))
        else:
            self.text(self.fit(title, "tile", w), "tile", GUI_FG,
                      (x, rect.centery - self.f["tile"].get_height() // 2))

    def rows(self, items, idx, top, badge_for=None):
        """items: [(key, title, subtitle)]; scrolls to keep idx visible."""
        pitch, h = self.s(84), self.s(72)
        bottom = self.H - self.s(54) - self.s(16)
        fit_n = max(1, (bottom - top) // pitch)
        first = 0 if len(items) <= fit_n else max(0, min(idx - fit_n // 2, len(items) - fit_n))
        for i in range(first, min(len(items), first + fit_n)):
            key, title, sub = items[i]
            r = self.pg.Rect(self.s(48), top + (i - first) * pitch, self.W - 2 * self.s(48), h)
            self.row(r, i == idx, key, title, sub, badge_for(i) if badge_for else None)

    def dim(self):
        shade = self.pg.Surface((self.W, self.H), self.pg.SRCALPHA)
        shade.fill((0, 0, 0, 165))
        self.screen.blit(shade, (0, 0))

    def spinner(self, center, radius):
        import math
        a = (self.pg.time.get_ticks() / 1000.0) * 2 * math.pi
        rect = self.pg.Rect(0, 0, 2 * radius, 2 * radius)
        rect.center = center
        self.pg.draw.arc(self.screen, GUI_ACCENT, rect, a, a + 4.2, max(2, self.s(4)))

    # ---------- input (keyboard; the launcher's .keys file turns the pad into these keys)
    def keys(self):
        pg = self.pg
        out = []
        now_ms = pg.time.get_ticks()
        if self.script and now_ms >= self.next_inject:
            tok = self.script[0]
            if tok == "wait":
                if not getattr(self, "busy", False):
                    self.script.pop(0)
            else:
                self.script.pop(0)
                self.next_inject = now_ms + 450
                if tok == "shot":
                    self.flip()
                    self.shot()
                else:
                    out.append(tok)
        for e in pg.event.get():
            if e.type == pg.QUIT:
                out.append("quit")
            elif e.type == pg.KEYDOWN:
                k = {pg.K_UP: "up", pg.K_DOWN: "down", pg.K_LEFT: "left", pg.K_RIGHT: "right",
                     pg.K_TAB: "right", pg.K_RETURN: "ok", pg.K_KP_ENTER: "ok", pg.K_SPACE: "ok",
                     pg.K_ESCAPE: "back", pg.K_BACKSPACE: "back", pg.K_PAGEUP: "pgup",
                     pg.K_PAGEDOWN: "pgdn", pg.K_HOME: "home", pg.K_END: "end"}.get(e.key)
                if k:
                    out.append(k)
        return out

    def shot(self):
        if self.shots:
            self.shot_n += 1
            self.pg.image.save(self.screen, os.path.join(self.shots, "gui-%02d.png" % self.shot_n))

    def flip(self):
        self.pg.display.flip()

    def frame(self):
        self.flip()
        self.clock.tick(30)
        if self.script == [] and self.shots and not getattr(self, "_ended", False):
            self._ended = True
            return ["quit"]
        return self.keys()

    # ---------- screens
    def home_draw(self, steps, idx, nxt, st, board):
        self._home = (steps, idx, nxt, st, board)
        self.screen.blit(self.bg, (0, 0))
        phase = st.get("phase") or "start"
        if board == V3_BOARD:
            sub = "You're on x86-64-v3. Integrate puts everything back with full functionality."
        elif phase == "prepared":
            sub = "Prepared. Start the x86-64-v3 upgrade from Updates & Downloads, or choose Update now."
        else:
            sub = "Moves this PC to the x86-64-v3 (Wayland) image and keeps your setup working."
        top = self.header(MENU_TITLE, sub)
        self.chip(board or "?", GUI_ACCENT, right_top=(self.W - self.s(48), self.s(34)))
        st_txt = "Step: %s" % phase.replace("-", " ")
        self.text(st_txt, "body", GUI_MUTED, (self.W - self.s(48) - self.f["body"].size(st_txt)[0],
                                              self.s(34) + self.f["body"].get_height() + self.s(20)))
        items = [(k, l.split("  - ")[0], l.split("  - ")[1] if "  - " in l else "") for k, l, _, _ in steps]
        self.rows(items, idx, top, lambda i: ("NEXT", GUI_ACCENT) if steps[i][0] == nxt else None)
        self.footer([("ok", "Select"), ("back", "Exit")], "x86-64-v3 Migration %s" % VERSION)

    def confirm(self, under, title, body, default_yes=True, labels=("Yes", "No")):
        sel = 0 if default_yes else 1
        while True:
            under()
            self.dim()
            pg = self.pg
            w = min(self.W - 2 * self.s(120), self.s(860))
            lines = self.wrap(body, "body", w - 2 * self.s(28))
            lh = self.f["body"].get_height() + self.s(4)
            h = self.s(28) + self.f["tile"].get_height() + self.s(18) + lh * len(lines) + self.s(30) + self.s(56) + self.s(24)
            panel = pg.Rect(0, 0, w, h)
            panel.center = (self.W // 2, self.H // 2)
            self.tile(panel, radius=self.s(20), fill=(24, 31, 41))
            pg.draw.rect(self.screen, GUI_ACCENT, panel, width=max(1, self.s(2)), border_radius=self.s(20))
            x, y = panel.x + self.s(28), panel.y + self.s(28)
            self.text(title, "tile", GUI_FG, (x, y))
            y += self.f["tile"].get_height() + self.s(18)
            for ln in lines:
                self.text(ln, "body", GUI_FG, (x, y))
                y += lh
            bw = max(self.s(170), max(self.f["tile"].size(x)[0] for x in labels) + self.s(48))
            bh = self.s(56)
            for i, lbl in enumerate(labels):
                b = pg.Rect(0, 0, bw, bh)
                b.bottomright = (panel.right - self.s(28) - (1 - i) * (bw + self.s(16)), panel.bottom - self.s(24))
                self.tile(b, i == sel, radius=self.s(12))
                img = self.f["tile"].render(lbl, True, GUI_FG)
                self.screen.blit(img, img.get_rect(center=b.center))
            self.footer([("ok", "Choose"), ("back", "Back")])
            for k in self.frame():
                if k in ("left", "right", "up", "down"):
                    sel = 1 - sel
                elif k == "ok":
                    return sel == 0
                elif k in ("back", "quit"):
                    return False

    def message(self, title, body):
        while True:
            self.screen.blit(self.bg, (0, 0))
            top = self.header(title)
            for ln in self.wrap(body, "body", self.W - 2 * self.s(48)):
                self.text(ln, "body", GUI_FG, (self.s(48), top))
                top += self.f["body"].get_height() + self.s(4)
            self.footer([("ok", "OK")])
            if any(k in ("ok", "back", "quit") for k in self.frame()):
                return

    def pick_drive(self):
        targets = backup_targets()
        idx = 0
        items = [("drive", p, lbl) for p, lbl in targets]
        while True:
            self.screen.blit(self.bg, (0, 0))
            top = self.header("Back up to...", "An external drive is safest. Needed: the files the scan found "
                                               "plus the boot partition (about 5 GB).")
            self.rows(items, idx, top)
            self.footer([("ok", "Select"), ("back", "Back")])
            for k in self.frame():
                if k == "up":
                    idx = max(0, idx - 1)
                elif k == "down":
                    idx = min(len(items) - 1, idx + 1)
                elif k == "ok":
                    return targets[idx][0]
                elif k in ("back", "quit"):
                    return None

    def log_lines(self, width):
        cw = max(1, self.f["mono"].size("M")[0])
        cols = max(20, width // cw)
        out = []
        for ln in read(MENU_LAST).replace("\r", "").split("\n"):
            ln = ln.expandtabs(4)
            while len(ln) > cols:
                out.append(ln[:cols])
                ln = ln[cols:]
            out.append(ln)
        while out and not out[-1].strip():
            out.pop()
        return out

    def watch(self, label, poll, attached=False, static=False, pid=None, cancel_text=""):
        """Show a step's output live, then its result; with pid, B/Esc offers Cancel
        (stop + put back what it changed). Returns the step's exit code."""
        pg = self.pg
        t0, t_end = pg.time.get_ticks(), None
        ctl = StepCancel(pid, poll) if pid else None
        rc, follow, offset = None, True, 0
        view = {"offset": 0, "follow": True, "vis": 1, "most": 0}
        self.busy = True

        def draw():
            self.screen.blit(self.bg, (0, 0))
            secs = ((t_end or pg.time.get_ticks()) - t0) // 1000
            state = ctl.state if ctl else ("done" if rc is not None else "running")
            if static:
                sub = "Full log: %s" % MENU_LOG
            elif state == "running":
                sub = "Running %d:%02d  -  it keeps going even if this window closes" % (secs // 60, secs % 60)
            elif state == "stopping":
                w = ctl.waiting_for()
                sub = ("Stopping once this part is done (it must not be cut short): %s" % w) if w else "Stopping..."
            elif state == "undoing":
                sub = "Putting back what it changed..."
            else:
                sub = "Finished in %d:%02d. Full log: %s" % (secs // 60, secs % 60, MENU_LOG)
            top = self.header(label, sub)
            if state in ("running", "stopping", "undoing"):
                self.spinner((self.W - self.s(70), self.s(52)), self.s(16))
            elif static:
                pass
            elif ctl and ctl.cancelled:
                if ctl.undo_rc == 0:
                    self.chip("Cancelled - all put back", (196, 140, 40), right_top=(self.W - self.s(48), self.s(34)))
                else:
                    self.chip("Cancelled - undo incomplete", GUI_DANGER, right_top=(self.W - self.s(48), self.s(34)))
            elif rc == 0:
                self.chip("Done", GUI_SUCCESS, right_top=(self.W - self.s(48), self.s(34)))
            else:
                self.chip("Stopped (code %s)" % rc, GUI_DANGER, right_top=(self.W - self.s(48), self.s(34)))
            box = pg.Rect(self.s(48), top, self.W - 2 * self.s(48), self.H - self.s(54) - self.s(16) - top)
            pg.draw.rect(self.screen, GUI_FOOTER, box, border_radius=self.s(12))
            pg.draw.rect(self.screen, (34, 45, 58), box, width=1, border_radius=self.s(12))
            lines = self.log_lines(box.w - 2 * self.s(18))
            lh = self.f["mono"].get_height() + self.s(2)
            vis = max(1, (box.h - 2 * self.s(14)) // lh)
            most = max(0, len(lines) - vis)
            view["offset"] = most if view["follow"] else max(0, min(view["offset"], most))
            view["vis"], view["most"] = vis, most
            y = box.y + self.s(14)
            for ln in lines[view["offset"]:view["offset"] + vis]:
                color = GUI_DANGER if re.match(r"\s*(!|BLOCKER|STOP|ERROR|FAIL)", ln) else \
                    GUI_SUCCESS if re.match(r"\s*\+ ", ln) else GUI_FG
                self.text(ln, "mono", color, (box.x + self.s(18), y))
                y += lh
            if most:
                bar_h = max(self.s(24), box.h * vis // len(lines))
                bar_y = box.y + (box.h - bar_h) * view["offset"] // most
                pg.draw.rect(self.screen, (60, 76, 96), (box.right - self.s(8), bar_y, self.s(4), bar_h),
                             border_radius=self.s(2))
            if state == "done" or static:
                hints = [("ok", "Back")]
            elif state == "running" and ctl:
                hints = [("back", "Cancel")]
            else:
                hints = []
            self.footer(hints + [("pgup", "Page up"), ("pgdn", "Page down")],
                        "Started from this menu earlier" if attached else "")

        while True:
            if rc is None:
                rc = ctl.tick() if ctl else poll()
                if rc is not None:
                    self.busy = False
                    t_end = pg.time.get_ticks()
            draw()
            for k in self.frame():
                if k in ("up", "pgup", "home"):
                    view["follow"] = False
                    view["offset"] = max(0, view["offset"] - (1 if k == "up" else view["vis"] if k == "pgup"
                                                              else view["most"]))
                elif k in ("down", "pgdn", "end"):
                    view["offset"] = min(view["most"], view["offset"] + (1 if k == "down" else view["vis"]
                                                                         if k == "pgdn" else view["most"]))
                    view["follow"] = view["offset"] >= view["most"]
                elif rc is not None and k in ("ok", "back", "quit"):
                    return rc
                elif rc is None and k == "back" and ctl and ctl.state == "running":
                    if self.confirm(draw, "Cancel %s?" % label,
                                    "It stops and puts back everything this step changed, so your system is "
                                    "as it was before you started it." + (("\n\n" + cancel_text) if cancel_text
                                                                         else ""), default_yes=False,
                                    labels=("Stop and undo", "Keep going")):
                        ctl.request()

    def run(self):
        if self.pad != "keyboard" and keys_out_of_date():
            self.message(MENU_TITLE, "ES's confirm and back buttons were switched since this menu was last "
                         "opened, so the buttons here don't match ES yet.\n\nThat is fixed now: close this "
                         "and open V3 Migration again.")
            return 0
        info = step_running()
        if info:
            pid, marker = info["pid"], info.get("marker")
            self.watch(info.get("label") or "Step", lambda: None if pid_alive(pid, marker) else 0, attached=True,
                       pid=pid if (info.get("argv") or [""])[0] != "undo-step" else None)
            try:
                os.remove(P(MENU_RUN))
            except OSError:
                pass
        self.offer_undo()
        idx, last_nxt = 0, object()
        while True:
            st = load_json(STATE_DIR + "/state.json", {}) or {}
            board = read(BOARD_FILE).strip()
            if board not in (V1_BOARD, V3_BOARD):
                self.message(MENU_TITLE, "This is for Batocera on PCs (x86_64 or x86-64-v3).\n\nThis system: %s"
                             % (board or "unknown"))
                return 2
            steps, nxt = menu_steps(st, board)
            if nxt != last_nxt:
                idx = next((i for i, s_ in enumerate(steps) if s_[0] == nxt), 0)
                last_nxt = nxt
            idx = min(idx, len(steps) - 1)
            self.home_draw(steps, idx, nxt, st, board)
            for k in self.frame():
                if k == "up":
                    idx = max(0, idx - 1)
                elif k == "down":
                    idx = min(len(steps) - 1, idx + 1)
                elif k in ("back", "quit"):
                    return 0
                elif k == "ok":
                    rc = self.choose(steps[idx], st, board)
                    if rc == "exit":
                        return 0
                    last_nxt = object()  # re-select the (new) next step
                    break

    def offer_undo(self):
        """A step was cut off last time (power cut, crash, forced stop): offer to put things back."""
        j = journal_pending()
        if not j or step_running():
            return
        blank = lambda: self.screen.blit(self.bg, (0, 0))
        while True:
            if self.confirm(blank, "The last step didn't finish",
                            "'%s' was stopped before it finished (cancelled, a power cut, or a crash), and "
                            "some of its changes are still in place.\n\nPut back what it changed?" % j.get("label")):
                proc = step_start(["undo-step"], "Putting things back")
                step_finish(self.watch("Putting things back", proc.poll))
                return
            if self.confirm(blank, "Keep its changes?", "The system stays as the unfinished step left it, and "
                                                         "this can't be undone afterwards.", default_yes=False):
                proc = step_start(["undo-step", "--discard"], "Keeping the changes")
                step_finish(self.watch("Keeping the changes", proc.poll))
                return

    def choose(self, step, st, board):
        key, label, argv, question = step
        title = label.split("  - ")[0]
        under = lambda: self.home_draw(*self._home)
        if key == "log":
            if not os.path.exists(P(MENU_LAST)):
                self.message("Last result", "Nothing has run from this menu yet.")
            else:
                self.watch("Last result", lambda: 0, static=True)
            return None
        if key == "backup":
            dest = self.pick_drive()
            if dest is None:
                return None
            argv = ["backup"] + (["--dest", dest] if dest != STATE_DIR + "/backups" else [])
            question = "Back up to %s?\n\nThis can take a while on a slow drive." % dest
            under = lambda: self.screen.blit(self.bg, (0, 0))
        if question and not self.confirm(under, title, question, default_yes=key not in NO_CONFIRM_DEFAULT):
            return None
        proc = step_start(argv, title)
        rc = self.watch(title, proc.poll, pid=proc.pid, cancel_text=CANCEL_NOTES.get(key, ""))
        step_finish(rc)
        if key == "update-now" and rc == 0 and self.confirm(lambda: self.screen.blit(self.bg, (0, 0)),
                                                             "Reboot now?", "The x86-64-v3 image is installed. "
                                                             "Reboot now to start it?"):
            if not TEST_MODE():
                subprocess.run(["sync"])
                subprocess.run(["reboot"])
            return "exit"
        return None


def cmd_gui(args):
    os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")
    if not (os.environ.get("DISPLAY") or os.environ.get("WAYLAND_DISPLAY")):
        say("Full-screen menu unavailable (no display); use: menu")
        return GUI_UNAVAILABLE
    try:
        import pygame
        pygame.display.init()
        pygame.font.init()
        driver = pygame.display.get_driver()
        if driver in ("offscreen", "dummy", "evdev"):
            pygame.quit()
            raise RuntimeError("no usable display (SDL driver %s)" % driver)
    except Exception as e:  # no pygame or no display: the launcher falls back to the terminal menu
        say("Full-screen menu unavailable (%s); use: menu" % e)
        return GUI_UNAVAILABLE
    try:
        shots = getattr(args, "shots", None)
        if shots:
            os.makedirs(shots, exist_ok=True)
        script = [t for t in (getattr(args, "script", None) or "").split(",") if t]
        return MigrateGui(pygame, windowed=getattr(args, "windowed", False), script=script, shots=shots).run()
    finally:
        pygame.quit()


def main(argv=None):
    global ROOT, ASSUME_YES
    ap = argparse.ArgumentParser(prog="batocera_v3_migrate.py",
                                 description="Safe Batocera x86_64 -> x86-64-v3 migration (v%s)" % VERSION)
    ap.add_argument("--yes", action="store_true", help="don't ask for typed confirmations")
    ap.add_argument("--root", default="/", help=argparse.SUPPRESS)  # testing against a mock tree
    ap.add_argument("--journal", action="store_true", help=argparse.SUPPRESS)  # set by the menu: makes Cancel possible
    sub = ap.add_subparsers(dest="cmd")
    sub.add_parser("scan", help="1. find everything the x86-64-v3 update affects")
    b = sub.add_parser("backup", help="2. back up those things (+ boot partition for rollback)")
    b.add_argument("--dest", help="folder or external drive (default: /userdata/system/v3-migration/backups)")
    b.add_argument("--full", action="store_true", help="full system backup instead (needs --dest)")
    u = sub.add_parser("update", help="3. prepare, then update from Batocera's menu")
    u.add_argument("--now", action="store_true", help="run Batocera's upgrader from here instead of the menu")
    u.add_argument("--allow-nvidia", action="store_true")
    sub.add_parser("integrate", help="4. integrate everything into x86-64-v3 (run after the update)")
    sub.add_parser("audit", help="(advanced) detailed inventory report")
    b.add_argument("--level", choices=["essential", "full"], default="full")
    b.add_argument("--include", action="append", help="extra path to include (repeatable)")
    b.add_argument("--allow-same-disk", action="store_true")
    v = sub.add_parser("verify-backup", help="re-hash a backup")
    v.add_argument("--backup")
    m = sub.add_parser("migrate", help="upgrade to the x86-64-v3 image")
    m.add_argument("--type", choices=["stable", "butterfly"], help="default: your updates.type")
    m.add_argument("--url", help="explicit upgrade directory URL")
    m.add_argument("--manual", action="store_true", help="use /userdata/system/upgrade/boot.tar.xz")
    m.add_argument("--allow-nvidia", action="store_true")
    m.add_argument("--skip-backup-check", action="store_true")
    m.add_argument("--reboot", action="store_true")
    i = sub.add_parser("check", help="(advanced) post-update checks; --apply for the basic fixes only")
    i.add_argument("--apply", action="store_true")
    i.add_argument("--ack-overlay", action="store_true",
                   help="you have rebuilt (or don't need) what was in the old overlay")
    r = sub.add_parser("rollback", help="restore the backed-up x86_64 boot partition")
    r.add_argument("--backup")
    r.add_argument("--restore-config", action="store_true")
    pr = sub.add_parser("prepare", help="pre-reboot steps, for upgrading from the Batocera menu")
    pr.add_argument("--allow-nvidia", action="store_true")
    sub.add_parser("unprepare", help="undo prepare (before upgrading)")
    fx = sub.add_parser("fix", help="list or apply fixes for v3 incompatibilities")
    fx.add_argument("--apply", nargs="+", metavar="FIX",
                    help="hook-guard, launch-watchdog, hooks, hook-backups, xwayland-access, hook-unguard, or all")
    sub.add_parser("status")
    un = sub.add_parser("undo-step", help="put back what a cancelled or interrupted menu step changed")
    un.add_argument("--discard", action="store_true", help="keep the changes; just drop the undo record")
    la = sub.add_parser("launcher", help="add/remove 'V3 Migration' in ES's Ports list (controller menu)")
    la.add_argument("action", nargs="?", choices=["install", "remove", "status"], default="status")
    sub.add_parser("menu", help="the terminal menu (the launcher's fallback when the full-screen menu can't start)")
    gu = sub.add_parser("gui", help="the full-screen menu the Ports launcher opens")
    gu.add_argument("--windowed", action="store_true", help="1280x720 window instead of full screen")
    gu.add_argument("--script", help=argparse.SUPPRESS)   # tests: comma-separated keys to press
    gu.add_argument("--shots", help=argparse.SUPPRESS)    # tests: save screenshots here
    pl = sub.add_parser("init-plugin", help="create an integration template")
    pl.add_argument("name")
    pl.add_argument("--force", action="store_true")
    args = ap.parse_args(argv)
    ROOT = os.path.abspath(args.root)
    ASSUME_YES = args.yes
    read_only = args.cmd in ("status", "audit", "verify-backup", "undo-step", "menu", "gui", "init-plugin") or \
        (args.cmd == "launcher" and args.action == "status") or (args.cmd == "fix" and not args.apply) or \
        (args.cmd == "check" and not args.apply)
    if not read_only and journal_pending():
        say("A cancelled or interrupted step left changes behind; nothing else can change until they are dealt "
            "with.\nRun: undo-step   (or: undo-step --discard to keep them)")
        return 2
    if args.journal and args.cmd not in (None, "undo-step", "menu", "gui", "launcher"):
        journal_start(args.cmd)
        cancelled = False
        try:
            return dispatch(args)
        except SystemExit as e:
            if e.code != CANCEL_RC:
                raise
            cancelled = True
            say("\nCancelled. Putting back what this step changed...")
            return CANCEL_RC
        finally:
            journal_stop(keep=cancelled)
    return dispatch(args)


def dispatch(args):
    if not args.cmd:
        return cmd_auto(args)
    if args.cmd == "backup":
        if args.full:
            if not args.dest:
                say("--full needs --dest")
                return 2
            args.level, args.include, args.allow_same_disk = "full", None, False
            return cmd_backup(args)
        return cmd_backup_simple(args)
    return {"scan": cmd_scan, "update": cmd_update, "integrate": cmd_integrate_all,
            "audit": cmd_audit, "verify-backup": cmd_verify_backup,
            "migrate": cmd_migrate, "check": cmd_integrate, "rollback": cmd_rollback,
            "status": cmd_status, "fix": cmd_fix, "prepare": cmd_prepare, "unprepare": cmd_unprepare, "init-plugin": cmd_init_plugin,
            "launcher": cmd_launcher, "menu": cmd_menu, "gui": cmd_gui, "undo-step": cmd_undo_step}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
