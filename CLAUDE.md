<!-- SPDX-License-Identifier: Apache-2.0 -->
# Claude Agent Instructions (`CLAUDE.md`)

@AGENTS.md

Additional Claude-specific reminders:
- Verify every Lean change with `cd lean && lake build && lake env lean VerifyAxioms.lean && lake env leanchecker-paranoid Solution`.
- Verify every C11/Python/Eshkol change with `make -C native clean test`, `node eshkol/run_eshkol_ad.mjs`, and `PYTHONPATH=python pytest tests/test_all.py -v`.
- Never alter `results/lean_axioms.txt` manually; regenerate it from `lake env lean VerifyAxioms.lean` and run `python scripts/check_readme_axioms.py`.
