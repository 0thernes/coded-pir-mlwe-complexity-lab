<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Independent Replication Protocol (`REPLICATION.md`)

This document provides exact step-by-step commands to reproduce every theorem, computational table, vector PDF figure, and manuscript artifact from a clean clone on Linux (Ubuntu 24.04+) or Windows 11.

## 1. Pinned Toolchain Requirements

| Layer | Required Toolchain | Pinned Version / Config |
|---|---|---|
| Formal Proofs | Lean 4 + Elan + Lake | `leanprover/lean4:v4.35.0` (`lean/lean-toolchain`) |
| 6-Kernel Comparator (Linux) | `bubblewrap` (`bwrap`) | System package (`apt-get install -y bubblewrap`) |
| Native C11 Engine | GCC or Clang + GNU Make | C11 (`-std=c11 -Wall -Wextra -Wpedantic -Werror`) |
| Eshkol Dual-Number AD | Node.js | v20+ (verified on v25.8.2) |
| Exact Python & Figures | Python 3.12+ | `numpy`, `scipy`, `matplotlib`, `pytest` (`pyproject.toml`) |
| White Paper Compilation | Tectonic | 0.15+ (`tectonic -X compile main.tex`) |

## 2. Clean-Room Verification Procedure

### Step 1 — Clean-Room Lean 4.35.0 Multi-Kernel Build
```bash
cd lean
rm -rf .lake
lake build
lake env lean VerifyAxioms.lean
# Confirm zero sorryAx, zero native_decide/ofReduceBool, zero custom axioms:
diff -u --strip-trailing-cr ../results/lean_axioms.txt <(lake env lean VerifyAxioms.lean)
lake env leanchecker Solution
lake env leanchecker-paranoid Solution
lake env leanchecker PalomarSolution
lake env leanchecker-paranoid PalomarSolution
# On Ubuntu Linux with bubblewrap (replays Lean paranoid, lean4lean, nanoda, con-leche, con-ron):
lake comparator --config comparator.json --paranoid
```

### Step 2 — Native C11 Core & Memory Sanitizers
```bash
make -C native clean test
./native/build/triad_cli koszul 3 2 3
./native/build/triad_cli f11-byz
./native/build/triad_cli renyi 2
./native/build/triad_cli dyadic256
./native/build/triad_cli chen 7 3
./native/build/triad_cli twisted 4 5 1
./native/build/triad_cli qgtl 2 1.023 0.25
./native/build/triad_cli koszul-tensor
# On Linux:
make -C native sanitizers
```

### Step 3 — Eshkol v1.3.6 Forward-Mode Dual-Number AD
```bash
node eshkol/run_eshkol_ad.mjs
```

### Step 4 — Exact Python Suite, Differential Tests, Mutation Suite & Citations
```bash
PYTHONPATH=python python python/triad_verify/pir_koszul.py
PYTHONPATH=python python python/triad_verify/polymatroid_barrier.py
PYTHONPATH=python python python/triad_verify/mlwe_tightness.py
PYTHONPATH=python python python/triad_verify/complexity_triad.py
PYTHONPATH=python pytest tests/test_all.py -v
python scripts/check_readme_axioms.py
python scripts/check_citations.py --online
```

### Step 5 — Regenerate Figures, Recompile White Paper & Verify arXiv Tarball
```bash
PYTHONPATH=python python python/triad_verify/generate_figures.py
mkdir -p paper/build
(cd paper && tectonic -X compile main.tex --outdir build --keep-logs --keep-intermediates)
mkdir -p /tmp/arxiv_cleanroom
tar -xzf dist/arxiv_submission.tar.gz -C /tmp/arxiv_cleanroom
(cd /tmp/arxiv_cleanroom && tectonic -X compile main.tex)
```

### Step 6 — Cryptographic Checksum Verification
```bash
(cd data && sha256sum -c MANIFEST.sha256)
sha256sum -c MANIFEST.sha256
```

## 3. Replication Log

| Date | Replicator | Platform | Lean 4.35.0 Kernels | C11 / Eshkol / Python | White Paper & Tarball | Outcome |
|---|---|---|---|---|---|---|
| 2026-11-25 (v1.0.0) | Alexander S. Donahue | Windows 11 + Ubuntu CI (`run 45695797431`) | 6/6 kernels (14 theorems, 1,967 `con-leche`/`con-ron` decls) + `lake comparator --paranoid` | C11 40/40 + ASan/UBSan; Eshkol 3/3; pytest 14/14 (6/6 mutants); 23/23 HTTP 200 | 11 pp. PDF (0 overfull) + clean-room tarball + Sigstore Rekor `4111094089` | PASS |
| 2026-11-25 (v2.0.0) | Alexander S. Donahue | Windows 11 x86_64 (GCC 14.2.0, Node 25.8.2, Python 3.12, Tectonic 0.15) | 6/6 local kernels (19 theorems `T1a`–`T3f`, 21 audited decls, 2,418 `con-leche`/`con-ron` decls) | C11 49/49 + 512 fuzz; Eshkol 3/3 (`Dyadic-256` `-7.77e-9`); pytest 15/15 (8/8 mutants); 25/25 live HTTP 200 | 14 pp. PDF (0 overfull, 5 figs) + clean-room tarball + interactive Pages Blueprint | PASS |
