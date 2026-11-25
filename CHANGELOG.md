<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changelog

All notable changes to `coded-pir-mlwe-complexity-lab` are documented in this file.
The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [1.0.0] - 2026-11-25

### Added
- **Zero-Mathlib Lean 4.35.0 Formalization (`lean/`):** 14 headline theorems (`T1a`–`T3d`), master conjunction `prove_all_triad_theorems`, and concrete non-vacuity witnesses (`NonVacuity.lean`), with zero `sorry`, zero `native_decide`, zero warnings, and strict standard axioms `[propext, Classical.choice, Quot.sound]`, verified across independent proof kernels (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin`, and Ubuntu CI `lake check --paranoid`).
- **Pillar I (`CS-053`):** Exact Koszul–Veronese Schur-product rank theorem (`T1a`), universal symmetric rate strictly dominating Sun–Zhang (`arXiv:2610.37412`) LFSR capacity for all $K,T \ge 2$ (`T1b`), zero-error exterior-power flag-private Byzantine schemes settling exact linear capacity at $(2,N,2,2,U,B)$ (with kernel-checked $\F_{11}$ rate-$2/5$ certificate, `T1c`) and exact unrestricted capacity at $E=K+1$ (`T1c`–`T1d`), zero-error $T=3, K=3$ schemes ($10/17$ at $N=6, B=0$ and $15/34$ at $N=8, B=1$), 330-orbit pure-integer unconditioned Shannon+Ingleton polymatroid barrier `h_uncond` at $8/13 > 3/5$ (`T1e`), and field-universal projective $\mathbb{P}^3$ linear impossibility (`T1f`).
- **Pillar II (`CS-026`):** Commutative-ring determinant-ideal secret independence refuting Luo 2026 (`T2a`), ring-universal anti-periodic DFT cancellation explaining Chen 2024/555 Step 9 (`T2b`), exact FIPS 203 $\mathrm{CBD}_2/\mathrm{CBD}_3$ moments & 60-digit $4.96\times$ ML-KEM Rényi-2 tightness cliff (`T2c`), and QGTL shifted-LWE Berry curvature identity (`T2d`).
- **Pillar III (`CS-001` / `CS-051`):** Constructive existence and global uniqueness of multilinear extensions for Algebrization (`T3a`), LWE PRF $\to$ Natural Proofs obstruction (`T3b`), Katz–Trevisan Byzantine PIR $\leftrightarrow$ LDC minimum distance $\ge 2B+1$ (`T3c`), and sharp FIPS 203 `Compress_1` margin $|e| \le 831$ (`T3d`).
- **Multi-Language Cross-Verification:** Zero-warning C11 core (`native/`, 40/40 tests + 500-case fuzz), 3 Eshkol v1.3.6 forward-mode dual-number AD modules (`eshkol/`), exact Python verification & 14-test `pytest` suite (`python/`, `tests/`), 4 vector PDF figures (`paper/figures/`), zero-overfull AMS-LaTeX white paper (`paper/main.tex`), clean-room `dist/arxiv_submission.tar.gz`, and 10-pass adversarial audit (`docs/10-pass-review.md`, `HARDENING_LOG.md`).

### Fixed
- Corrected off-by-one rounding offset (`+1664` $\to$ `+1665`) in `Compress_1` (`T3d`, C11, Python) caught during differential testing against FIPS 203 round-half-up semantics (logged in `HARDENING_LOG.md`).
- Fixed sub-$KT$ generic pure-selector verification in `pir_koszul.py` and odd-mode Gauss sum legend ($2\sqrt{D}$) in `fig4_chen_step9_and_triad.pdf` caught during visual figure inspection.
