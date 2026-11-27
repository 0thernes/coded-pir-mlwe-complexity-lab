<!-- SPDX-License-Identifier: Apache-2.0 -->
# Agent Instructions (`AGENTS.md` — Canonical Entry Point)

This repository (`coded-pir-mlwe-complexity-lab`) is a formal verification and scientific computing artifact for Alexander S. Donahue's triad research preprint on `CS-053` (Coded/Byzantine PIR), `CS-026` (MLWE reduction tightness), and `CS-001`/`CS-051` (complexity-theoretic barriers).

## Hard Non-Negotiable Rules

1. **Zero Proof Cheating:** Never introduce `sorry`, `admit`, `native_decide`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or custom `axiom` declarations anywhere in `lean/TriadFrontier/`, `lean/Challenge.lean`, `lean/Solution.lean`, or `lean/PalomarSolution.lean`. (`lean/PalomarChallenge.lean` is the sole intentional challenge contract excluded from `defaultTargets`.)
2. **Permitted Axioms Only:** Every theorem in `lean/VerifyAxioms.lean` must remain strictly within `[propext, Classical.choice, Quot.sound]`, and `README.md` must stay verbatim-synced with `results/lean_axioms.txt` (`python scripts/check_readme_axioms.py`).
3. **Honest Epistemic Scope:** Never claim $\mathrm{P} \neq \mathrm{NP}$ (`CS-001`), non-linear $C(2,4,2,2)$, general $M \ge 3$ non-LFSR PIR capacity, or worst-case quantum MLWE lower bounds are solved.
4. **Build Standard v1.2.0 Rules (R1–R8):** No git hooks, no commit/tag signing, push straight to `main` (no PR ceremony), no branch protection, keep CI informational, no Dependabot/Renovate/Copilot files, and use the 10-class finding taxonomy in `HARDENING_LOG.md`.
5. **Author Identity:** Always use `Alexander S. Donahue` (`Independent Researcher, Spokane, WA, USA`, ORCID `0009-0006-8168-9648`, email `0_0@0thernes.art`). Do not introduce corporate/LLC entity affiliations into this repository.
6. **Single Version Source:** `VERSION` is the single source of truth; update `pyproject.toml`, `CITATION.cff`, `repo.yaml`, `lean/lakefile.toml`, and `lean/formalization.yaml` together when bumping versions.

## Essential Commands

```bash
# Verify Lean 4.35.0 proofs + strict axiom & kernel replay (incl. 1,656-decl module sweep)
(cd lean && lake build --wfail && lake env lean VerifyAxioms.lean && lake env lean AuditExhaustiveAxioms.lean && lake env leanchecker Solution && lake env leanchecker-paranoid Solution)

# Build and test native C11 core (-std=c11 -Wall -Wextra -Wpedantic -Werror)
make -C native clean test

# Run Eshkol v1.3.6 dual-number AD modules
node eshkol/run_eshkol_ad.mjs

# Run full pytest suite (25/25: claims, differential, property, negative, 16/16 mutants, schema, links, timestamps) & strict lint/type gates
PYTHONPATH=python pytest tests/test_all.py -v
ruff check python tests scripts examples
mypy python/triad_verify scripts --ignore-missing-imports

# Audit README axiom parity, dual timestamps & live citations (incl. Crossref retraction check)
python scripts/check_readme_axioms.py
python scripts/stamp_timestamps.py --verify
python scripts/check_citations.py --online

# Compile AMS-LaTeX white paper (must emit 0 overfull hboxes)
(cd paper && tectonic -X compile main.tex --outdir build --keep-logs --keep-intermediates)
```

## Key Architectural Paths

- `lean/TriadFrontier/` — Zero-Mathlib Lean 4.35.0 proof modules (`AlgebraCore`, `PIRCertificates`, `PIRLinearCerts`, `LinearRankSoundness`, `PIRProtocol`, `PIRKoszul`, `MLWETightness`, `KoszulTensor`, `StrassenWinograd`, `BrockettDobkin`, `ShannonCapacity`, `AlgebraicComplexity`, `PaleyCapacity`, `ComplexityTriad`, `NonVacuity`, `AdversarialTests`; 32 theorems `T1a`–`T3l` & `T1k` + 10 boundary refutations, 35 audited declarations + 1,656 `TriadFrontier.*` swept by `AuditExhaustiveAxioms.lean` under `module`).
- `native/` — Hardened C11 implementation, `strtol`/`strtod`-validated CLI (`f101-t3k3`, `dyadic16384a/b`, `ret6-f2`, `paley-cap`, etc.), and 88-test + 1,024-case fuzz harness.
- `eshkol/` — Forward-mode dual-number AD modules (`.esk`) and hardened Node.js runner (`Dyadic-256` through `Dyadic-16384-A/B`, plus 7 negative guards).
- `python/triad_verify/` — Exact finite-field rank & live $\mathbb{F}_{101}$ $(6,3,3)$ 20/20 zero-error PIR verifier, 12-variable polymatroid + $I_4$/5-obj/6-obj $\mathbb{F}_2^{64}$ linear realizability, 60-digit ML-KEM `Dyadic-256..16384-A/B` & Bai et al. (2018) optimizer + exact coupled FIPS 203 DFR convolution & 90-digit Kronecker exact interval oracle (matching NIST Table 1 within `0.04` bits), Koszul/Strassen/Brockett–Dobkin/Schwartz–Zippel/Lovász/Paley checks, and 8-figure vector PDF generation (`0 ruff`, `0 mypy`, 25/25 `pytest`, 16/16 killed mutants).
- `paper/main.tex` & `paper/refs.bib` — AMS-LaTeX manuscript (`v5.2.0`, 8 figures, 36 live HTTP-200 + 0-retraction Crossref citations).
- `docs/` & `ERRATA.md` — Architecture, ADRs, threat model, statement fidelity, 10-pass review, adversarial red-team review, literature search, Mega-Atlas crosswalk, submission packet, errata ledger, and CSP/WCAG-AA interactive GitHub Pages Blueprint (`docs/site/`).
