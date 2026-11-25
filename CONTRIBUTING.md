<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Contributing to `coded-pir-mlwe-complexity-lab`

## Workflow Policy (Direct-to-Main, No Gates)

This repository follows Build Standard v1.2.0:
- **Direct-to-main workflow:** Work commits and pushes straight to `main`. There are no mandatory PR merge gates, branch protection rules, or commit/tag signing requirements.
- **Informational CI:** GitHub Actions reports build, test, Lean 6-kernel, C11 sanitizer, and LaTeX compilation results on every push to `main`.
- **Issues for discussion & findings:** Use GitHub Issues (tagged with the 10 finding classes in `.github/labels.yml`: `bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot`) to report counterexamples, proof simplifications, or reproduction results.

## Local Setup & Verification

```bash
# 1. Verify zero-Mathlib Lean 4.35.0 proofs and strict axiom allowlist
cd lean && lake build && lake env lean VerifyAxioms.lean

# 2. Build and test native C11 core (-Wall -Wextra -Wpedantic -Werror)
make -C native test

# 3. Run Eshkol v1.3.6 forward-mode AD checks
node eshkol/run_eshkol_ad.mjs

# 4. Run full Python exact audit, pytest (14/14), and citation check
PYTHONPATH=python pytest tests/test_all.py -v
python scripts/check_citations.py
```

## Standards for Formal Contributions
- Zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom` declarations, zero Mathlib imports.
- Every new theorem must include a concrete non-vacuity witness in `lean/TriadFrontier/NonVacuity.lean` and an independent falsifiable test in `tests/test_all.py`.
- All code files carry `SPDX-License-Identifier: Apache-2.0`; all docs/manuscripts carry `SPDX-License-Identifier: CC-BY-4.0`.
