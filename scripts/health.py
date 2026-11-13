#!/usr/bin/env python3
"""Static health check for the MoonBit sources in this repository.

Reports, per package:

* **dead code** — a `fn` whose name is never mentioned anywhere else in the
  repository (sources, white-box tests, benchmarks).  A `pub fn` that is
  part of the documented API is listed separately from a private one, so
  the two can be triaged differently.
* **duplicate bodies** — functions whose normalised body is identical to
  another's.  These are the deduplication candidates.
* **size** — line counts, so growth is visible.

Usage:  python3 scripts/health.py [--root .] [--json]

This is a *name-based* scanner, not a type checker: it is deliberately
conservative about what it calls dead, and every hit is meant to be read
by a human before deletion.  It exists so that the answer to "what is
unused?" is a command rather than an archaeology project.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path

# `fn name(`, `fn Type::name(`, optionally `pub`, `pub(all)`, `pub(open)`.
DEF = re.compile(
    r"^\s*(?P<pub>pub(?:\([^)]*\))?\s+)?fn\s+(?P<owner>[A-Za-z_][A-Za-z0-9_]*)?::?"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*(?:\[[^\]]*\])?\s*\(",
)
DEF_PLAIN = re.compile(
    r"^\s*(?P<pub>pub(?:\([^)]*\))?\s+)?fn\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*"
    r"(?:\[[^\]]*\])?\s*\(",
)
IMPL = re.compile(r"^\s*pub\s+(?:extend|impl)\b")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def strip_comments(text: str) -> str:
    text = re.sub(r"//[^\n]*", "", text)
    return text


def body_of(lines: list[str], start: int) -> str | None:
    """Return the brace-balanced body starting at the definition line."""
    depth = 0
    seen = False
    out: list[str] = []
    for i in range(start, len(lines)):
        line = lines[i]
        out.append(line)
        for ch in line:
            if ch == "{":
                depth += 1
                seen = True
            elif ch == "}":
                depth -= 1
        if seen and depth <= 0:
            break
    if not seen:
        return None
    body = "\n".join(out)
    body = body[body.find("{") :]
    return re.sub(r"\s+", " ", body).strip()


def scan(root: Path) -> dict:
    files = sorted(
        p
        for p in root.rglob("*.mbt")
        if not any(
            part in {"_build", "node_modules", ".moon", "target"} for part in p.parts
        )
    )
    defs: list[dict] = []
    impl_lines: set[tuple[Path, int]] = set()
    text_all: dict[Path, str] = {}

    for path in files:
        raw = path.read_text(encoding="utf-8")
        text_all[path] = strip_comments(raw)
        lines = text_all[path].split("\n")
        in_impl = False
        for n, line in enumerate(lines):
            if IMPL.match(line):
                in_impl = True
                impl_lines.add((path, n))
            if in_impl:
                if line.strip() == "}":
                    in_impl = False
                continue
            m = DEF.match(line)
            owner = None
            if m:
                owner = m.group("owner")
                name = m.group("name")
                pub = bool(m.group("pub"))
            else:
                m = DEF_PLAIN.match(line)
                if not m:
                    continue
                name = m.group("name")
                pub = bool(m.group("pub"))
            defs.append(
                {
                    "pkg": path.parent.name,
                    "file": str(path.relative_to(root)),
                    "line": n + 1,
                    "name": name,
                    "owner": owner,
                    "pub": pub,
                    "body": body_of(lines, n),
                    "test": path.name.endswith(("_wbtest.mbt", "_test.mbt")),
                }
            )

    # Count mentions of each identifier over the whole repository.
    mentions: dict[str, int] = defaultdict(int)
    for path, text in text_all.items():
        for tok in IDENT.findall(text):
            mentions[tok] += 1
    # A definition contributes exactly one mention of its own name.
    for d in defs:
        d["uses"] = mentions[d["name"]] - 1

    dead = [d for d in defs if d["uses"] <= 0 and not d["test"]]

    by_body: dict[str, list[dict]] = defaultdict(list)
    for d in defs:
        if d["body"] and len(d["body"]) > 40 and not d["test"]:
            by_body[d["body"]].append(d)
    dupes = [v for v in by_body.values() if len(v) > 1]

    sizes: dict[str, int] = defaultdict(int)
    for path, text in text_all.items():
        sizes[path.parent.name] += text.count("\n") + 1

    return {
        "files": len(files),
        "functions": len(defs),
        "dead": sorted(dead, key=lambda d: (d["pkg"], d["name"])),
        "duplicates": [
            sorted(g, key=lambda d: (d["pkg"], d["name"])) for g in dupes
        ],
        "sizes": dict(sorted(sizes.items())),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    root = Path(args.root).resolve()
    report = scan(root)

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
        return

    print(f"scanned {report['files']} files, {report['functions']} functions")
    print()
    print("== package sizes (lines) ==")
    for pkg, n in report["sizes"].items():
        print(f"  {pkg:14s} {n:6d}")
    print()
    print(f"== never referenced ({len(report['dead'])}) ==")
    for d in report["dead"]:
        kind = "pub " if d["pub"] else "priv"
        owner = f"{d['owner']}::" if d["owner"] else ""
        print(f"  {kind} {d['pkg']:12s} {owner}{d['name']:28s} {d['file']}:{d['line']}")
    print()
    print(f"== identical bodies ({len(report['duplicates'])} groups) ==")
    for g in report["duplicates"]:
        locs = ", ".join(f"{d['pkg']}/{d['name']} ({d['file']}:{d['line']})" for d in g)
        print(f"  {locs}")


if __name__ == "__main__":
    main()
