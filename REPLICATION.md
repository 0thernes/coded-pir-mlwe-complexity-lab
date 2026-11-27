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
lake build --wfail
lake env lean VerifyAxioms.lean
lake env lean AuditExhaustiveAxioms.lean
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
./native/build/triad_cli f101-t3k3
./native/build/triad_cli ret6-f2
./native/build/triad_cli renyi 2
./native/build/triad_cli dyadic256
./native/build/triad_cli dyadic512
./native/build/triad_cli dyadic1024a
./native/build/triad_cli dyadic1024b
./native/build/triad_cli dyadic16384a
./native/build/triad_cli dyadic16384b
./native/build/triad_cli chen 7 3
./native/build/triad_cli twisted 4 5 1
./native/build/triad_cli qgtl 2 1.023 0.25
./native/build/triad_cli koszul-tensor
./native/build/triad_cli strassen
./native/build/triad_cli koszul-allm 3
./native/build/triad_cli koszul-allm 4
./native/build/triad_cli lovasz-c5
./native/build/triad_cli c7-cap
./native/build/triad_cli paley-cap 13
./native/build/triad_cli paley-cap 17
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

### Step 6 — Cryptographic Checksum & Dual-Timestamp Verification
```bash
(cd data && sha256sum -c MANIFEST.sha256)
sha256sum -c MANIFEST.sha256
python scripts/stamp_timestamps.py --verify
```

## 3. Replication Log

> **Honesty Note (B44):** All entries below are **author-automated** clean-room / CI replications. Independent **external third-party human replication** remains open and is explicitly welcomed via GitHub Issues.

| Date | Replicator | Platform | Lean 4.35.0 Kernels | C11 / Eshkol / Python | White Paper & Tarball | Outcome |
|---|---|---|---|---|---|---|
| 2026-11-25 (v1.0.0) | Alexander S. Donahue | Windows 11 + Ubuntu CI (`run 45695797431`) | 6/6 kernels (14 theorems, 1,967 `con-leche`/`con-ron` decls) + `lake comparator --paranoid` | C11 40/40 + ASan/UBSan; Eshkol 3/3; pytest 14/14 (6/6 mutants); 23/23 HTTP 200 | 11 pp. PDF (0 overfull) + clean-room tarball + Sigstore Rekor `4111094089` | PASS |
| 2026-11-25 (v2.0.0) | Alexander S. Donahue | Windows 11 + Ubuntu CI (`run 45698684366`) | 6/6 kernels (19 theorems `T1a`–`T3f`, 21 audited decls, 2,418 `con-leche`/`con-ron` decls) + `lake comparator --paranoid` | C11 49/49 + ASan/UBSan; Eshkol 3/3 (`Dyadic-256` `-7.77e-9`); pytest 15/15 (8/8 mutants); 26/26 live HTTP 200 | 14 pp. PDF (0 overfull, 5 figs) + clean-room tarball + interactive Pages Blueprint | PASS |
| 2026-11-25 (v3.0.0) | Alexander S. Donahue | Windows 11 + Ubuntu CI (`run 45701164193`) | 6/6 kernels (23 theorems `T1a`–`T3h`, 25 audited decls, 2,995 `con-leche`/`con-ron` decls) + `lake comparator --paranoid` | C11 57/57 + ASan/UBSan; Eshkol 3/3 (`Dyadic-512` `-3.57e-6`); pytest 16/16 (10/10 mutants); 28/28 live HTTP 200 | 16 pp. PDF (0 overfull, 6 figs) + clean-room tarball + 23-theorem Pages Blueprint | PASS |
| 2026-11-25 (v4.0.0) | Alexander S. Donahue | Windows 11 x86_64 + Ubuntu CI | 6/6 kernels (27 theorems `T1a`–`T3j`, 29 audited decls, 3,589 `con-leche`/`con-ron` & 3,884 `nanoda` decls) | C11 65/65 + 512 fuzz; Eshkol 3/3 (`Dyadic-1024-A` `-3.79e-9`); pytest 17/17 (12/12 mutants); 33/33 live HTTP 200 | AMS-LaTeX PDF (0 overfull, 7 figs) + clean-room tarball + 27-theorem Pages Blueprint | PASS |
| 2026-11-26 (v5.0.0) | Alexander S. Donahue | Windows 11 x86_64 + Ubuntu CI (`run 45850785203`) | 6/6 kernels (31 theorems `T1a`–`T3l` + 7 adversarial refutations, 34 audited decls, 4,269 `con-leche`/`con-ron`, `lean4lean` 4,266, `nanoda`, live tamper gate) | C11 79/79 + 512 fuzz; Eshkol 3/3 (`Dyadic-16384-A` `-9.13e-10`); pytest 18/18 (14/14 mutants); strict `0 ruff / 0 mypy`; 36/36 live HTTP 200 | AMS-LaTeX PDF (0 overfull, 8 figs) + clean-room tarball + DigiCert TSA + Rekor `4128750161` | PASS |
| 2026-11-26 (v5.1.0) | Alexander S. Donahue *(author-automated zero-cache clean-clone + final L01/A01–A12 replay)* | Windows 11 x86_64 (`_tmp_cleanclone_v51`, zero `.lake`/C11/TeX caches; GCC 16.1, Node 25.8, Python 3.12/3.13, Tectonic 0.15) | Cold `lake build --wfail` (`103.99s`), `VerifyAxioms` (`1.52s`), `AuditExhaustiveAxioms` (`2.81s`, 1,330 `TriadFrontier.*` decls), 4× `leanchecker`/`leanchecker-paranoid` (`27.30s`), + local `con-leche`/`con-ron` (`4,337` decls after `L01`) & `nanoda_bin` + live negative tamper gate (`mlkemCompress1 (1665 + 832) = 1` rejected) | Cold C11 `-Werror` build + 87/87 unit + 1,024/1,024 fuzz (`11.00s`); Eshkol 3/3 + 7 negative guards (`0.15s`); 25/25 `pytest` (`0 ruff / 0 mypy`, Draft 2020-12 schema); 36/36 live HTTP 200 + 30/30 Crossref 0 retractions | Zero-warning AMS-LaTeX PDF (`A01`–`A12` fixed) + clean-room arXiv tarball + DigiCert RFC 3161 TSA + 3-calendar Bitcoin OTS + 100.0% `Audit-Repo.ps1` (69/69) | PASS |
| 2026-11-27 (v5.2.0) | Alexander S. Donahue *(author-automated 3-cycle hardening closing `L02`, `L06`, `L07`, `S01`/`A02`, `S02`, `H39`–`H45`)* | Windows 11 x86_64 (GCC 14.2, Node 25.8, Python 3.12/3.13, Tectonic 0.15) + Ubuntu CI | 6/6 kernels (32 theorems `T1a`–`T3l` & `T1k` + 10 adversarial refutations, 35 audited decls, 1,656 `TriadFrontier.*` decls swept under `module`, 4,745 `con-leche`/`con-ron` `--verified` decls, silent 0-error `nanoda_bin`, `leanchecker-paranoid`, live tamper gate) | C11 `-Werror` 88/88 unit (`f101-t3k3` 20/20 zero-error $(6,3,3)$) + 1,024/1,024 fuzz; Eshkol 3/3 + 7 negative guards; 25/25 `pytest` (16/16 killed mutants, 90-digit Kronecker coupled FIPS 203 DFR oracle matching NIST Table 1 ±0.04 b, `0 ruff / 0 mypy`, Draft 2020-12 schema); 36/36 HTTP 200 + 30/30 Crossref 0 retractions | Zero-warning AMS-LaTeX PDF (8 figs visually verified) + clean-room arXiv tarball + DigiCert RFC 3161 TSA + 3-calendar Bitcoin OTS + 100.0% `Audit-Repo.ps1` (69/69) | PASS |
