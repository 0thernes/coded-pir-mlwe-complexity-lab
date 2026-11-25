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
# Verify Lean 4.35.0 proofs + strict axiom & kernel replay
(cd lean && lake build && lake env lean VerifyAxioms.lean && lake env leanchecker Solution && lake env leanchecker-paranoid Solution)

# Build and test native C11 core (-std=c11 -Wall -Wextra -Wpedantic -Werror)
make -C native clean test

# Run Eshkol v1.3.6 dual-number AD modules
node eshkol/run_eshkol_ad.mjs

# Run full pytest suite (claims, differential, property, negative, mutation, version consistency)
PYTHONPATH=python pytest tests/test_all.py -v

# Audit README axiom parity & live citations
python scripts/check_readme_axioms.py
python scripts/check_citations.py

# Compile AMS-LaTeX white paper (must emit 0 overfull hboxes)
(cd paper && tectonic -X compile main.tex --outdir build --keep-logs --keep-intermediates)
```

## Key Architectural Paths

- `lean/TriadFrontier/` — Zero-Mathlib Lean 4.35.0 proof modules (`AlgebraCore`, `PIRCertificates`, `PIRKoszul`, `MLWETightness`, `ComplexityTriad`, `NonVacuity`).
- `native/` — C11 implementation, CLI, and 40-test + 500-case fuzz harness.
- `eshkol/` — Forward-mode dual-number AD modules (`.esk`) and Node.js runner.
- `python/triad_verify/` — Exact finite-field rank, 12-variable polymatroid, 60-digit ML-KEM Rényi-2, complexity checks, and vector figure generation.
- `paper/main.tex` & `paper/refs.bib` — 11-page AMS-LaTeX manuscript.
- `docs/` — Architecture, ADRs, threat model, statement fidelity, 10-pass review, and adversarial red-team review.
