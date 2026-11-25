#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "=== [1/5] Lean 4.35.0 Build, Axiom Audit & Kernel Checks ==="
(
  cd lean
  lake build
  lake env lean VerifyAxioms.lean
  lake env leanchecker Solution
  lake env leanchecker PalomarSolution
  lake env leanchecker-paranoid Solution
  lake env leanchecker-paranoid PalomarSolution
  if command -v bwrap >/dev/null 2>&1; then
    lake comparator --config comparator.json --paranoid
  fi
)

echo "=== [2/5] Native C11 Core ==="
make -C native clean all test

echo "=== [3/5] Eshkol v1.3.6 Forward-Mode Dual-Number AD ==="
node eshkol/run_eshkol_ad.mjs

echo "=== [4/5] Exact Python Suite, Pytest, Quickstart, Axioms & Citations ==="
PYTHONPATH=python python3 examples/quickstart_demo.py
PYTHONPATH=python pytest tests/test_all.py -v
python3 scripts/check_readme_axioms.py
python3 scripts/check_citations.py

echo "=== [5/5] Checksums ==="
(cd data && sha256sum -c MANIFEST.sha256)
sha256sum -c MANIFEST.sha256
echo "ALL CHECKS PASSED."
