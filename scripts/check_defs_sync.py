#!/usr/bin/env python3
"""Check that SSGinP/Defs.lean is the verbatim copy of the definitions of Challenge.lean.

The Solution may not import the Challenge, so the proof library has its own copy of every definition the
advertised statements use. Comparator requires those declarations to be identical on both sides. This script
derives the expected text of SSGinP/Defs.lean from Challenge.lean and compares it byte for byte:

* the header (`module`, the `public import` lines, `@[expose] public section`) must be the same;
* from `namespace SSG` to `end SSG`, Defs must be Challenge with every `theorem` (docstring, statement and its
  `sorry` proof) removed, and with a `/-! ## ... -/` section comment removed when no declaration is left under it.

Usage: check_defs_sync.py            (check; exit status 1 on a difference)
       check_defs_sync.py --write    (regenerate SSGinP/Defs.lean from Challenge.lean)
Reads the two files only; runs no project code.
"""
import difflib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHALLENGE = ROOT / "Challenge.lean"
DEFS = ROOT / "SSGinP" / "Defs.lean"
SECTION = "@[expose] public section"
DEFS_DOC = '''/-!
# The definitions of `Challenge.lean`, for the proof library

A verbatim copy of the definitions of `Challenge.lean` (everything except the advertised theorems), so that the
declarations `Solution.lean` talks about are identical to the Challenge's. Do not edit by hand: change
`Challenge.lean` and run `python3 scripts/check_defs_sync.py --write`. CI runs the check.
-/
'''


def split(text: str):
    """header lines (up to and including the section line) and the body from `namespace SSG` on."""
    lines = text.split("\n")
    section = lines.index(SECTION)
    start = lines.index("namespace SSG")
    end = lines.index("end SSG")
    assert all(not line.strip() for line in lines[end + 1:]), "text after `end SSG`"
    return lines[: section + 1], lines[start: end + 1]


def blocks(body):
    """split the body into blocks separated by blank lines (blank lines inside `/-! -/` comments do not split)."""
    out, current, in_comment = [], [], False
    for line in body:
        if in_comment:
            current.append(line)
            if line.rstrip().endswith("-/"):
                in_comment = False
            continue
        if line.strip() == "":
            if current:
                out.append(current)
                current = []
            continue
        current.append(line)
        if line.startswith("/-") and not line.rstrip().endswith("-/"):
            in_comment = True
    if current:
        out.append(current)
    return out


def kind(block):
    if block[0].startswith("/-!"):
        return "section"
    index = 0
    if block[0].startswith("/--"):
        while not block[index].rstrip().endswith("-/"):
            index += 1
        index += 1
    head = block[index] if index < len(block) else ""
    return "theorem" if head.startswith("theorem ") else "other"


def expected_defs(challenge_text: str) -> str:
    header, body = split(challenge_text)
    kept = [b for b in blocks(body) if kind(b) != "theorem"]
    result = []
    for position, block in enumerate(kept):
        if kind(block) == "section":
            following = kept[position + 1] if position + 1 < len(kept) else None
            if following is None or kind(following) == "section" or following == ["end SSG"]:
                continue
        result.append(block)
    text = "\n".join(header) + "\n\n" + DEFS_DOC + "\n"
    text += "\n\n".join("\n".join(block) for block in result) + "\n"
    return text


def main() -> int:
    challenge = CHALLENGE.read_text(encoding="utf-8")
    expected = expected_defs(challenge)
    if "--write" in sys.argv[1:]:
        DEFS.write_text(expected, encoding="utf-8")
        print(f"wrote {DEFS.relative_to(ROOT)}")
        return 0
    actual = DEFS.read_text(encoding="utf-8")
    if actual == expected:
        count = sum(1 for b in blocks(split(challenge)[1]) if kind(b) == "theorem")
        print(f"SSGinP/Defs.lean is in sync with Challenge.lean ({count} theorems left out)")
        return 0
    sys.stdout.writelines(difflib.unified_diff(
        expected.splitlines(True), actual.splitlines(True), "expected (from Challenge.lean)", "SSGinP/Defs.lean"))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
