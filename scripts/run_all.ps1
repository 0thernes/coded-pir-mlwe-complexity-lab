#!/usr/bin/env pwsh
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
# Bracket-safe full Windows verification runner for coded-pir-mlwe-complexity-lab.
$ErrorActionPreference = 'Stop'

$Root = Split-Path -Parent $PSScriptRoot
$Py = if ($env:TRIAD_PYTHON) { $env:TRIAD_PYTHON } else { 'python' }

Write-Host "=== [1/5] Lean 4.35.0 Build (--wfail), Axiom Audits & Kernel Checks ==="
Set-Location -LiteralPath (Join-Path $Root 'lean')
lake build --wfail
$axioms = lake env lean VerifyAxioms.lean
$axioms | Set-Content -LiteralPath (Join-Path $Root 'results\lean_axioms.txt') -Encoding UTF8
lake env lean AuditExhaustiveAxioms.lean
lake env leanchecker Solution
lake env leanchecker PalomarSolution
lake env leanchecker-paranoid Solution
lake env leanchecker-paranoid PalomarSolution

Write-Host "=== [2/5] Native C11 Core, CLI & 1024-Iter Fuzz ==="
Set-Location -LiteralPath $Root
$cc = if ($env:CC) { $env:CC } else { 'gcc' }
New-Item -ItemType Directory -Force -Path (Join-Path $Root 'native\build') | Out-Null
& $cc -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror -I native/include native/src/triad_core.c native/tests/test_triad_core.c -o native/build/test_triad_core.exe -lm
& $cc -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror -I native/include native/src/triad_core.c native/src/triad_cli.c -o native/build/triad_cli.exe -lm
& $cc -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror -DFUZZ_STANDALONE -I native/include native/src/triad_core.c native/tests/fuzz_triad.c -o native/build/fuzz_triad.exe -lm
& (Join-Path $Root 'native\build\test_triad_core.exe')
& (Join-Path $Root 'native\build\fuzz_triad.exe')

Write-Host "=== [3/5] Eshkol v1.3.6 Forward-Mode Dual-Number AD ==="
node eshkol/run_eshkol_ad.mjs

Write-Host "=== [4/5] Exact Python Suite, Pytest, Quickstart, Axioms, Citations & Timestamps ==="
$env:PYTHONPATH = 'python'
& $Py examples/quickstart_demo.py
& $Py -m pytest tests/test_all.py -v
& $Py scripts/check_readme_axioms.py
& $Py scripts/check_citations.py
& $Py scripts/stamp_timestamps.py --verify

Write-Host "=== [5/5] All Local Verification Layers PASSED ==="
