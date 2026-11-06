#!/usr/bin/env python3
"""Root-manager section of the release notes.

The kernel and the BakaSU manager talk over the KernelSU UAPI. The manager
installs ksud, and ksud refuses the boot stages (module mounting among them)
when its UAPI is not the kernel's. Version numbers do not show this, so every
release names the newest manager whose UAPI matches the kernel and whose
signature the kernel's apk_sign.c accepts.

  manager_notes.py new KERNEL_TREE              print the section for a release
                                                built from KERNEL_TREE
  manager_notes.py refresh REPO [--dry-run]     rewrite the section in REPO's
                                                releases when a newer matching
                                                manager comes out

The section ends with a marker that keeps the kernel facts (UAPI, accepted
signing keys) and what was verified about the current pick, so a refresh needs
neither the kernel tree nor a second download of an APK it has already checked.

Builds come from the official releases of Baka-SU/BakaSU and from
zeroedx/BakaSU_CI, which republishes upstream CI builds. A mirrored APK is used
only if the upstream run it names was built from the commit it names, and its
bytes match that run's artifact (or the artifact can no longer be fetched).
"""

import glob
import hashlib
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
from dataclasses import dataclass

UPSTREAM = "Baka-SU/BakaSU"
MIRROR = "zeroedx/BakaSU_CI"
ARTIFACT = "Manager-release"   # upstream CI artifact holding the release APKs
FORMAT = "1"                   # bump when the marker's fields change meaning

# BakaSU_v4.2.0-rc3_35237-arm64-v8a-release.apk; releases from before the rename say ReSukiSU.
APK_NAME = re.compile(r"([A-Za-z]+)_v[0-9A-Za-z.-]+_(\d+)-arm64-v8a-release\.apk")
SECTION = re.compile(r"<!-- manager-notes -->\n.*?<!-- /manager-notes (.*?) -->", re.S)


def warn(msg):
    # stderr: in `new` mode stdout is the section itself.
    print(f"::warning::{msg}", file=sys.stderr)


def gh(*args, stdin=None):
    p = subprocess.run(["gh", *args], input=stdin, capture_output=True, text=True)
    if p.returncode:
        raise RuntimeError(f"gh {' '.join(args)}: {p.stderr.strip()}")
    return p.stdout


def api_list(path):
    return [json.loads(line) for line in gh("api", "--paginate", path, "--jq", ".[]").splitlines()]


def read(path):
    with open(path, encoding="utf-8", errors="replace") as f:
        return f.read()


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


# --- the kernel side ------------------------------------------------------------

def kernel_facts(tree):
    ksu = os.path.join(tree, "drivers/sukisu")
    uapi = re.search(r"KERNEL_SU_UAPI_VERSION\s*=\s*(\d+)", read(f"{ksu}/uapi/supercall.h"))
    apk_sign = glob.glob(f"{ksu}/kernel/**/apk_sign.c", recursive=True)
    manager_sign = glob.glob(f"{ksu}/kernel/**/manager_sign.h", recursive=True)
    if not uapi or len(apk_sign) != 1 or len(manager_sign) != 1:
        raise RuntimeError(f"{ksu}: cannot find the UAPI version or the signing key tables")
    return int(uapi[1]), accepted_keys(read(apk_sign[0]), read(manager_sign[0]))


def accepted_keys(apk_sign_c, manager_sign_h):
    """Entries of apk_sign_keys[] that are not behind a config option."""
    table = re.search(r"apk_sign_keys\[\]\s*=\s*\{(.*?)\};", apk_sign_c, re.S)
    defines = dict(re.findall(r"#define\s+(\w+)\s+(\S+)", manager_sign_h))
    keys, depth = [], 0
    for line in table[1].splitlines() if table else []:
        line = line.strip()
        if line.startswith("#if"):
            depth += 1
        elif line.startswith("#endif"):
            depth -= 1
        elif depth == 0 and (m := re.match(r"\{\s*EXPECTED_SIZE_(\w+)\s*,\s*EXPECTED_HASH_\1\s*\}", line)):
            keys.append((m[1], int(defines[f"EXPECTED_SIZE_{m[1]}"], 0),
                         defines[f"EXPECTED_HASH_{m[1]}"].strip('"').lower()))
    if not keys:
        raise RuntimeError("apk_sign_keys[] has no unconditional signing key")
    return keys


def apk_signer(path):
    """(size, sha256) of the certificate check_v2_signature() compares with the
    key table, or None if it rejects the APK before that: no or several v2
    blocks, any other block but verity padding, or a v1 MANIFEST.MF."""
    with open(path, "rb") as f:
        b = f.read()
    u16 = lambda o: struct.unpack_from("<H", b, o)[0]
    u32 = lambda o: struct.unpack_from("<I", b, o)[0]
    u64 = lambda o: struct.unpack_from("<Q", b, o)[0]
    n = len(b)
    try:
        for i in range(0x10000):    # EOCD, searched the way the kernel does
            if u16(n - i - 2) == i and u32(n - i - 22) == 0x06054b50:
                cd = u32(n - i - 6)
                break
        else:
            return None
        if cd < 0x20 or b[cd - 16:cd] != b"APK Sig Block 42":
            return None
        size, end = u64(cd - 24), cd - 24
        start = cd - size - 8
        if size < 0x18 or start < 0 or u64(start) != size:
            return None
        pos, v2, cert = start + 8, 0, None
        while pos < end:
            plen, pid = u64(pos), u32(pos + 8)
            if plen < 4 or pos + 8 + plen > end:
                return None
            if pid == 0x7109871A:
                v2 += 1
                q = pos + 24            # past the id and the signers, signer, signed data lengths
                q += 4 + u32(q)         # past the digests
                cert = b[q + 8:q + 8 + u32(q + 4)]
            elif pid != 0x42726577:
                return None
            pos += 8 + plen
        if v2 != 1 or len(cert) > 1024:
            return None
        q = 0                           # has_v1_signature_file(): local headers from the start
        while q + 30 <= n and u32(q) == 0x04034B50:
            if b[q + 30:q + 30 + u16(q + 26)] == b"META-INF/MANIFEST.MF":
                return None
            q += 30 + u16(q + 26) + u16(q + 28) + u32(q + 18)
    except (struct.error, IndexError):
        return None
    return len(cert), hashlib.sha256(cert).hexdigest()


# --- the manager side -----------------------------------------------------------

@dataclass
class Build:
    code: int       # versionCode, from the APK name
    repo: str       # repository whose release carries the APK
    tag: str
    asset: dict     # the arm64-v8a APK of that release
    commit: str     # upstream commit it was built from
    run: str = ""   # upstream CI run it came from (mirrored builds)

    @property
    def official(self):
        return self.repo == UPSTREAM


def builds():
    """Every arm64-v8a manager build on offer, newest first."""
    found = []
    code = lambda a: int(APK_NAME.fullmatch(a["name"])[2])
    for rel in api_list(f"repos/{UPSTREAM}/releases?per_page=100"):
        apks = [a for a in rel["assets"] if APK_NAME.fullmatch(a["name"])]
        if rel["draft"] or not apks or not re.fullmatch(r"[\w.-]+", rel["tag_name"]):
            continue
        commit = gh("api", f"repos/{UPSTREAM}/commits/{rel['tag_name']}", "--jq", ".sha").strip()
        found += [Build(code(a), UPSTREAM, rel["tag_name"], a, commit) for a in apks]
    mirrored = 0
    for rel in api_list(f"repos/{MIRROR}/releases?per_page=100"):
        apks = [a for a in rel["assets"] if APK_NAME.fullmatch(a["name"])]
        commit = re.search(r"Upstream commit \| `([0-9a-f]{40})`", rel["body"] or "")
        run = re.search(r"Actions run ID \| `(\d+)`", rel["body"] or "")
        if apks and not (commit and run):
            warn(f"{MIRROR} {rel['tag_name']}: no upstream commit and run in its notes, skipped")
        elif apks:
            found += [Build(code(a), MIRROR, rel["tag_name"], a, commit[1], run[1]) for a in apks]
            mirrored += 1
    if not mirrored:
        raise RuntimeError(f"no usable release in {MIRROR}; did its format change?")
    # An official release goes before a mirrored copy of the same build.
    return sorted(found, key=lambda b: (b.code, b.official), reverse=True)


_uapi = {}


def manager_uapi(commit):
    """KERNEL_SU_UAPI_VERSION the manager was built with (its cpp/uapi links to uapi/)."""
    if commit not in _uapi:
        try:
            src = gh("api", "-H", "Accept: application/vnd.github.raw",
                     f"repos/{UPSTREAM}/contents/uapi/supercall.h?ref={commit}")
        except RuntimeError as e:
            if "HTTP 404" not in str(e) and "HTTP 422" not in str(e):
                raise
            src = ""            # from before the UAPI, or not an upstream commit at all
        m = re.search(r"KERNEL_SU_UAPI_VERSION\s*=\s*(\d+)", src)
        _uapi[commit] = int(m[1]) if m else None
    return _uapi[commit]


_checked = {}


def check(build, keys, state):
    """(key, provenance, sha256) if a kernel with these keys can use the build, else None."""
    digest = (build.asset.get("digest") or "").removeprefix("sha256:")
    if digest and state.get("pick") == digest and \
            state.get("prov") == ("official" if build.official else "identical"):
        return state["cert"], state["prov"], digest
    memo = (build.asset["id"], tuple(keys))
    if memo not in _checked:
        _checked[memo] = verify(build, keys, digest)
    return _checked[memo]


def verify(build, keys, digest):
    name = build.asset["name"]
    with tempfile.TemporaryDirectory() as tmp:
        gh("release", "download", build.tag, "-R", build.repo, "-p", name, "-D", tmp)
        apk = os.path.join(tmp, name)
        sha = sha256(apk)
        if digest and sha != digest:
            raise RuntimeError(f"{name}: the download does not match its published sha256")
        signer = apk_signer(apk)
        key = next((k for k, size, h in keys if signer == (size, h)), None)
        if not key:
            warn(f"{name} from {build.repo} {build.tag}: not signed with a key this kernel accepts, skipped")
            return None
        if build.official:
            return key, "official", sha
        prov = provenance(build, sha, tmp)
        if prov == "differs":
            warn(f"{name} from {MIRROR} {build.tag}: not what upstream run {build.run} built, skipped")
            return None
        return key, prov, sha


def provenance(build, sha, tmp):
    """Compare a mirrored APK with the artifact of the upstream run it names."""
    try:
        run = json.loads(gh("api", f"repos/{UPSTREAM}/actions/runs/{build.run}"))
    except RuntimeError as e:
        if "HTTP 404" in str(e):
            return "differs"
        raise
    if run["head_sha"] != build.commit:
        return "differs"
    try:
        gh("run", "download", build.run, "-R", UPSTREAM, "-n", ARTIFACT, "-D", f"{tmp}/run")
    except RuntimeError as e:
        warn(f"{build.asset['name']}: cannot fetch {ARTIFACT} of upstream run {build.run}: {e}")
        return "unverified"
    original = os.path.join(tmp, "run", build.asset["name"])
    if not os.path.exists(original):
        return "unverified"
    return "identical" if sha256(original) == sha else "differs"


# --- the section ----------------------------------------------------------------

def section(uapi, keys, state, offered):
    pick = verdict = None
    other = []                  # newer builds with another UAPI
    for b in offered:
        if manager_uapi(b.commit) != uapi:
            other.append(b)
        elif verdict := check(b, keys, state):
            pick = b
            break
    official = next((b for b in offered if b.official), None)
    return render(uapi, keys, pick, verdict, other, official)


def render(uapi, keys, pick=None, verdict=None, other=(), official=None, pending=False):
    out = ["<!-- manager-notes -->", "### Root manager", "",
           f"This kernel has **UAPI {uapi}**. Use a manager with the same UAPI: the manager installs "
           "ksud, and ksud only runs the boot stages (module mounting included) when its UAPI "
           "matches the kernel's.", ""]
    if pending:
        out.append("The manager lookup failed during the build; the next scheduled run fills this in.")
    elif not pick:
        out.append(f"No published manager build has UAPI {uapi}.")
    else:
        key, prov, sha = verdict
        if pick.official:
            origin = f"official release [{pick.tag}](https://github.com/{UPSTREAM}/releases/tag/{pick.tag})"
        else:
            origin = (f"CI build of [{UPSTREAM}@{pick.commit[:8]}](https://github.com/{UPSTREAM}/commit/"
                      f"{pick.commit}), mirrored by [{MIRROR}](https://github.com/{MIRROR})")
        run = f"[upstream run {pick.run}](https://github.com/{UPSTREAM}/actions/runs/{pick.run})"
        name = APK_NAME.fullmatch(pick.asset["name"])[1]
        out += [f"Newest manager with UAPI {uapi}: **[{name} {pick.code} (arm64-v8a)]"
                f"({pick.asset['browser_download_url']})**, {origin}",
                f"- sha256 `{sha}`",
                f"- signed with a key this kernel accepts (`{key}` in manager_sign.h)"]
        if prov == "identical":
            out.append(f"- byte-identical to the APK in the `{ARTIFACT}` artifact of {run}")
        elif prov == "unverified":
            out.append(f"- not compared with {run}: its `{ARTIFACT}` artifact could not be fetched")
    by_uapi = {}
    for b in other:
        by_uapi.setdefault(manager_uapi(b.commit), set()).add(b.code)
    if by_uapi:
        out += ["", "Not for this kernel: " + ", ".join(
            (f"{min(c)}–{max(c)}" if len(c) > 1 else f"{min(c)}") + f" (UAPI {u if u is not None else '?'})"
            for u, c in by_uapi.items()) + "."]
    if official and official is not pick:
        out += ["", f"Newest official release: [{official.tag}](https://github.com/{UPSTREAM}/releases/tag/"
                    f"{official.tag}) ({official.code}), UAPI {manager_uapi(official.commit)}."]
    key, prov, sha = verdict or ("-", "-", "-")
    keys = ",".join(f"{k}:{s:#x}:{h}" for k, s, h in keys)
    out += ["", "<sub>Updated automatically when a newer manager comes out.</sub>",
            f"<!-- /manager-notes v={FORMAT} uapi={uapi} keys={keys} pick={sha} cert={key} prov={prov} -->"]
    return "\n".join(out)


def refresh(repo, dry_run):
    offered = builds()
    for rel in api_list(f"repos/{repo}/releases?per_page=100"):
        body = (rel["body"] or "").replace("\r\n", "\n")
        m = SECTION.search(body)
        if not m:
            continue
        state = dict(re.findall(r"(\w+)=(\S+)", m[1]))
        if state.get("v") != FORMAT:
            warn(f"{rel['tag_name']}: manager section has format {state.get('v')}, not {FORMAT}; left alone")
            continue
        keys = [(k, int(s, 0), h) for k, s, h in (e.split(":") for e in state["keys"].split(","))]
        try:
            new = section(int(state["uapi"]), keys, state, offered)
        except Exception as e:
            warn(f"{rel['tag_name']}: {e}")
            continue
        if new == m[0]:
            continue
        print(f"{rel['tag_name']}: manager section {'would change' if dry_run else 'updated'}")
        if dry_run:
            print(new + "\n")
        else:
            gh("release", "edit", rel["tag_name"], "-R", repo, "--notes-file", "-",
               stdin=body[:m.start()] + new + body[m.end():])


def main():
    args = sys.argv[1:]
    if len(args) == 2 and args[0] == "new":
        uapi, keys = kernel_facts(args[1])
        try:
            print(section(uapi, keys, {}, builds()))
        except Exception as e:
            warn(f"manager lookup failed: {e}")
            print(render(uapi, keys, pending=True))
    elif len(args) in (2, 3) and args[0] == "refresh" and args[2:] in ([], ["--dry-run"]):
        try:
            refresh(args[1], dry_run=len(args) == 3)
        except Exception as e:
            # Most likely the API having a bad moment; the next scheduled run tries again.
            warn(f"manager section refresh failed: {e}")
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
