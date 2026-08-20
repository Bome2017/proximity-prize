#!/usr/bin/env python3
"""Guard the one invariant that generalizes across challenges: a served version
lives only in challenges.json.

A verifier-side change is a new immutable version name. No file but
challenges.json may name a version of a served series (a `<series>-v0`
negative-test fixture and comment mentions aside); everything else reads it back
through challenges.py, so a bump is a one-line edit and a partial one is loud.

Deliberately nothing challenge-specific -- no seed, score, radius or hardening
shape. Those differ per challenge and belong to each challenge's own checks.
Multi-challenge by construction: a new challenge is a new challenges.json entry.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import challenges  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
SCAN_SUFFIXES = {".yml", ".yaml", ".py", ".sh"}


def main() -> int:
    try:
        entries = challenges.load()
    except challenges.ConfigError as exc:
        print(f"invalid challenges.json: {exc}", file=sys.stderr)
        return 1

    print(f"== challenges: {len(entries)} ==")
    for c in entries:
        print(f"  {c['slug']}  {c['version']}  (series: {challenges.series(c['version'])})")

    series = sorted({challenges.series(c["version"]) for c in entries})
    literal = re.compile("(?:" + "|".join(re.escape(s) for s in series) + r")-v[0-9]+")
    source = (ROOT / "challenges.json").resolve()

    fail = False
    for path in ROOT.rglob("*"):
        if (
            not path.is_file()
            or path.suffix not in SCAN_SUFFIXES
            or ".git" in path.parts
            or path.resolve() == source
        ):
            continue
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeError):
            continue
        for n, line in enumerate(lines, 1):
            for m in literal.finditer(line):
                if "#" in line[: m.start()] or m.group().endswith("-v0"):
                    continue  # a comment mention, or the -v0 negative fixture
                print(
                    f"stray version literal (read challenges.json instead): "
                    f"{path.relative_to(ROOT)}:{n}: {m.group()}",
                    file=sys.stderr,
                )
                fail = True

    if fail:
        return 1
    print("ok -- every served version is single-sourced in challenges.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
