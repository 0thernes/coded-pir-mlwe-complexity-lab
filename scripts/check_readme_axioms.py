#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""Verify verbatim parity between results/lean_axioms.txt and the README.md axiom block."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN_PATTERNS = [
    "sorryAx",
    "Lean.ofReduceBool",
    "Lean.trustCompiler",
    "_native",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def normalize(text: str) -> str:
    return "\n".join(line.rstrip() for line in text.replace("\r\n", "\n").strip().splitlines())


def main() -> int:
    axioms_path = ROOT / "results" / "lean_axioms.txt"
    readme_path = ROOT / "README.md"

    if not axioms_path.is_file():
        print(f"ERROR: missing {axioms_path}", file=sys.stderr)
        return 1
    if not readme_path.is_file():
        print(f"ERROR: missing {readme_path}", file=sys.stderr)
        return 1

    axioms_text = normalize(axioms_path.read_text(encoding="utf-8"))
    readme_text = readme_path.read_text(encoding="utf-8").replace("\r\n", "\n")

    for forbidden in FORBIDDEN_PATTERNS:
        if forbidden in axioms_text:
            print(f"ERROR: forbidden axiom/token {forbidden!r} found in lean_axioms.txt", file=sys.stderr)
            return 1

    # Check every listed axiom bracket strictly lies within ALLOWED_AXIOMS
    merged = re.sub(r"\n\s+", " ", axioms_text)
    decl_count = 0
    for line in merged.splitlines():
        m = re.search(r"depends on axioms:\s*\[([^\]]*)\]", line)
        if m:
            decl_count += 1
            used = {tok.strip() for tok in m.group(1).split(",") if tok.strip()}
            disallowed = used - ALLOWED_AXIOMS
            if disallowed:
                print(f"ERROR: disallowed axioms {sorted(disallowed)} in: {line}", file=sys.stderr)
                return 1

    if decl_count < 16:
        print(f"ERROR: expected >= 16 audited declarations, found {decl_count}", file=sys.stderr)
        return 1

    # Extract fenced ```text ... ``` block under the axiom audit section in README.md
    blocks = re.findall(r"```text\n(.*?)\n```", readme_text, flags=re.DOTALL)
    if not blocks:
        print("ERROR: no ```text``` axiom block found in README.md", file=sys.stderr)
        return 1

    matched = any(normalize(b) == axioms_text for b in blocks)
    if not matched:
        print("ERROR: README.md verbatim axiom block drifted from results/lean_axioms.txt!", file=sys.stderr)
        return 1

    print(
        f"OK: README.md axiom block matches results/lean_axioms.txt verbatim "
        f"({decl_count} audited declarations, strictly within {sorted(ALLOWED_AXIOMS)})."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
