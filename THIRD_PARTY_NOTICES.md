<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Third-Party Notices & Attribution

This repository is authored cleanly from first principles by Alexander S. Donahue and ships under dual licensing (`Apache-2.0` for all code, Lean 4 proofs, C11, Python, Eshkol, and scripts; `CC-BY-4.0` for all manuscripts, figures, data tables, and documentation).

## Architectural Inspiration & Toolstack Attribution

1. **Tsotchke Open-Source Toolstack** (`https://github.com/tsotchke`, MIT / Apache-2.0):
   - **`tsotchke/eshkol`** (MIT): Forward-mode dual-number automatic differentiation syntax (`(derivative fn x)`) used in `eshkol/*.esk` and executed via our clean-room portable JavaScript evaluator `eshkol/run_eshkol_ad.mjs`.
   - **`tsotchke/quantum_geometric_tensor`** (MIT): Quantum Geometric Tensor (Fubini–Study metric & Berry curvature) mathematical framing inspiring Theorem `T2d` and `native/src/triad_core.c` (`triad_qgtl_shifted_lwe`).
   - **`tsotchke/moonlab`** (MIT): Zero-dependency C11 FIPS 203 ML-KEM architectural pattern inspiring `native/src/triad_core.c`.
   - **`tsotchke/rosette-wire`** (MIT): Deterministic SHA-256 verification receipt concept used in `results/rosette_receipt.json`.
   No third-party source files are vendored verbatim; all code in this repository is clean-room original.

2. **Lean 4.35.0 & Independent External Proof Kernels** (Apache-2.0 / MIT):
   - Lean 4 (`leanprover/lean4:v4.35.0`), `leanchecker`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`. Zero Mathlib dependencies are used.

3. **Academic Literature**:
   - No third-party copyrighted papers or arXiv PDFs are redistributed in this repository. All primary literature is cited cleanly in `paper/refs.bib` with live-verified DOIs and arXiv identifiers.
