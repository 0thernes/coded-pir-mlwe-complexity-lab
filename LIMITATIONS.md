<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Limitations, Epistemic Boundaries, and Real vs. Metaphor (`LIMITATIONS.md`)

This document states precisely what `coded-pir-mlwe-complexity-lab` **does not prove**, where its formal verification boundary stops, and how conceptual inspirations relate to actual implemented code.

## 1. Open Problems Explicitly NOT Solved

1. **$\mathrm{P} \neq \mathrm{NP}$ (`CS-001`):** Nothing in this repository proves or disproves $\mathrm{P} = \mathrm{NP}$. Theorems `T3a` and `T3b` formalize well-defined algebraic and cryptographic barrier cores (multilinear-extension uniqueness underlying Algebrization, and PRF indistinguishability blocking Natural Proofs).
2. **Non-Linear $C(2,4,2,2) \in [3/5, 8/13]$ (`CS-053`):** Theorem `T1e` establishes that no Shannon or Ingleton inequality on the 12-variable unconditioned system can tighten the upper bound below $8/13$, while Theorem `T1f` establishes the projective $\mathbb{P}^3$ obstruction for linear 2-subspaces over arbitrary fields. Whether a $5+$-variable non-Shannon information inequality (e.g., Zhang–Yeung, Dougherty–Freiling–Zeger) lowers the upper bound to $3/5$, or a genuinely non-linear scheme exceeds $3/5$, remains completely open.
3. **General $M \ge 3$ Non-LFSR PIR & Arbitrary $T \ge 4$ Zero-Error Schemes (`CS-053`):** Our Koszul–Veronese construction (`T1a`–`T1b`) strictly dominates the Sun–Zhang (2026) LFSR ceiling for all $K,T \ge 2$ and matches the Sun–Jafar unrestricted ceiling at $E = K+1$ (`T1c`), while our zero-error Byzantine witnesses cover $(N=6,K=2,T=2,B=1)$ over $\mathbb{F}_{11}$ (kernel-certified) and $(N=8,K=3,T=3,B=1)$ over $\mathbb{F}_{1009}$ (computational exact rank). General $M \ge 3$ non-LFSR capacity and deterministic zero-error constructions for arbitrary $T \ge 4$ remain open.
4. **Worst-Case Quantum Hardness of MLWE (`CS-026`):** Refuting Luo (2026) (`T2a`) and explaining the Step 9 anti-periodic cancellation in Chen (2024) (`T2b`) does not prove that MLWE is immune to all quantum algorithms. Lattice hardness remains an unproven cryptographic assumption.

## 2. Formal Verification vs. Computational Boundaries

- **Zero-Mathlib Lean 4.35.0 Scope:** Lean machine-checks exact algebraic identities over arbitrary `CommRing`/`SimpleField` structures (`T1a`, `T1f`, `T2a`, `T2b`, `T2c`, `T3a`), exact integer/natural-number inequalities (`T1b`, `T1c`, `T1d`, `T2c`, `T2d`, `T3b`, `T3c`, `T3d`), and finite computational certificates (`T1c` $\mathbb{F}_{11}$ 90-matrix inverse certificate, `T1e` 330-orbit scale-128 polymatroid certificate).
- **Transcendental & Floating-Point Layer (Tier 2):** Transcendental exponentials and logarithms (60-digit Rényi-2 divergence minimization in Table 2, continuous DFT magnitude plots, and continuous QGTL Berry curvature curves) are verified outside Lean using 60-digit Python `Decimal`, C11 `double`, and Eshkol v1.3.6 dual-number automatic differentiation (`< 2e-13` agreement). Lean does not construct $\mathbb{R}$ or $\exp/\log$; instead it certifies the exact underlying discrete moments, cleared-denominator rational bounds, and symmetry/non-vanishing theorems.
- **Concrete Non-Vacuity vs. Cryptographic Concrete Security:** `TriadFrontier/NonVacuity.lean` inhabits every algebraic typeclass (`SimpleField (Fin 5)`, `SimpleField (Fin 11)`, `CommRing Int`) so no universal theorem is vacuously true. This does **not** certify side-channel resistance, timing constancy, or FIPS 140-3 validation of the C11 test utilities.

## 3. Real vs. Metaphor (Tsotchke Toolstack Alignment)

Several architectural ideas were inspired by Tsotchke's public open-source toolstack (`eshkol`, `quantum-geometric-tensor-learning`, `moonlab`, `rosette-wire`), so we explicitly separate **what is literally executed** from **what is a clean-room conceptual adaptation**:

| Component | Literal / Real | Metaphorical / Clean-Room Adaptation |
|---|---|---|
| **Eshkol v1.3.6 Dual-Number AD (`eshkol/*.esk`)** | Literal Scheme/Eshkol-syntax source files (`renyi_cbd_ad.esk`, `koszul_pir_ad.esk`, `qgtl_lwe_berry_ad.esk`) evaluated deterministically by our standalone Node.js dual-number evaluator (`eshkol/run_eshkol_ad.mjs`) and differentially tested against 60-digit Python to `< 2e-13`. | We do **not** vendor or link the native LLVM Eshkol compiler binary; our clean-room runner executes the exact forward-mode dual-number calculus on the `.esk` definitions so CI runs zero-dependency on both Linux and Windows. |
| **QGTL Shifted-LWE Berry Curvature (`T2d`)** | Literally computes the exact discrete Quantum Geometric Tensor antisymmetric Berry-curvature / covariance functional on shifted ML-KEM $\mathrm{CBD}_2$ noise states (`T2d`, C11, Python, Eshkol). | This is a clean-room mathematical adaptation of QGTL geometry to discrete LWE error distributions, **not** a physical quantum hardware experiment or a quantum speedup over lattice sieving. |
| **Moonlab C11 Style (`native/`)** | Literally compiled zero-warning `-std=c11 -Wall -Wextra -Wpedantic -Werror` C11 code with 40/40 unit + 500-case fuzz tests and ASan/UBSan. | Clean-room C11 implementation written from scratch for this paper; does not vendor Moonlab source files. |
| **Rosette-Wire Receipts (`results/rosette_receipt.json`)** | Real deterministic SHA-256 JSON provenance receipt generated by `scripts/make_manifest.py` binding Lean axiom logs, witness JSONs, PDFs, and test digests. | Conceptual receipt format inspired by Rosette-Wire provenance envelopes; not tied to an external network service. |

## 4. Review & AI-Assistance Status

This preprint has **not** undergone external journal or conference peer review and claims no external DOI. It was conceived, directed, audited, and verified by **Alexander S. Donahue** with assistance from Antigravity (Gemini-based AI agent) for proof engineering, multi-language testing, figure rendering, and manuscript drafting. All scientific claims stand exclusively on independently reproducible machine-checked proofs and deterministic code.
