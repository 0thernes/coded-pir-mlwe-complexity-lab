<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Verification & Engineering Run Log (`docs/run-log.md`)

Chronological audit trail of major verification runs (Build Standard B40).

| Date | Phase | Command / Action | Outcome | Evidence Artifact |
|---|---|---|---|---|
| 2026-11-25 | Discovery & LP/Exact Verification | Exterior-power Koszul–Veronese rank checks, $\mathbb{F}_{11}$ Byzantine rate-$2/5$ search, 12-variable Shannon+Ingleton LP (`h_uncond`), 60-digit ML-KEM Rényi-2 optimization, Chen Step-9 & QGTL checks | PASS | `data/f11_byz_witness.json`, `data/h_uncond_certified.json` |
| 2026-11-25 | Lean 4.35.0 Formalization | `lake build`, `VerifyAxioms.lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin` | PASS | `results/lean_axioms.txt`, `results/six_kernel_audit.txt` |
| 2026-11-25 | C11 & Eshkol AD Cross-Audit | `GCC 14.2.0 -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror` (40/40 unit + 500 fuzz) & `node eshkol/run_eshkol_ad.mjs` (3/3 `< 2e-13`) | PASS | `native/tests/test_triad_core.c`, `eshkol/run_eshkol_ad.mjs` |
| 2026-11-25 | Python Differential & Mutation Suite | `PYTHONPATH=python pytest tests/test_all.py -v` (14/14 incl. 6/6 core mutants killed) + 3,814,209 6-atom Ingletons | PASS | `tests/test_all.py`, `results/exact_audit_summary.json` |
| 2026-11-25 | Live Citation & Figure Audit | `python scripts/check_citations.py --online` (23/23 HTTP 200) + visual inspection of `fig1`–`fig4` PDFs | PASS | `paper/refs.bib`, `paper/figures/*.pdf` |
| 2026-11-25 | AMS-LaTeX Paper & Clean-Room Tarball | `tectonic -X compile main.tex` (11 pp., 0 overfull hboxes) + clean-room unpack/compile of `dist/arxiv_submission.tar.gz` | PASS | `dist/Donahue_2026_coded_pir_mlwe_complexity_frontier.pdf`, `dist/arxiv_submission.tar.gz` |
| 2026-11-25 | Clean-Room Rebuild, Comparator & Build Standard Audit (v1.0.0) | Fresh `rm -rf lean/.lake && lake build`, `lake comparator --paranoid`, `scripts/check_readme_axioms.py`, `scripts/Audit-Repo.ps1` | PASS | `MANIFEST.sha256`, CI `45695797431`, Rekor `4111094089` |
| 2026-11-25 | v2.0.0 Lean 4.35.0 Expansion (`T1g`, `T2e`, `T2f`, `T3e`, `T3f`) | 19 theorems / 21 audited decls; `lake build` (16/16 jobs, 0 warnings); 6 local kernels (`con-leche --verified` 2,418 decls, `con-ron --verified` 2,418 decls, `nanoda_bin`) | PASS | `results/lean_axioms.txt`, `lean/TriadFrontier/KoszulTensor.lean` |
| 2026-11-25 | v2.0.0 C11, Eshkol AD, Python, Figures, 14-pp PDF & Pages Blueprint | C11 49/49 + 512 fuzz; Eshkol 3/3 (`Dyadic-256` `-7.77e-9`); pytest 15/15 (8/8 mutants); 25/25 live HTTP 200 citations; 0-overfull 14-pp PDF + clean-room tarball; `docs/site/` Blueprint | PASS | `dist/Donahue_2026_coded_pir_mlwe_complexity_frontier.pdf`, `docs/site/blueprint.html` |
