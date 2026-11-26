<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Errata and Post-Publication Corrections (`ERRATA.md`)

This document tracks any post-release mathematical, formalization, computational, or bibliographic errata identified in `coded-pir-mlwe-complexity-lab` across all tagged releases (`v1.0.0`–`v5.0.0`). Pre-release defects caught during internal 10-pass adversarial reviews are documented separately in [`HARDENING_LOG.md`](HARDENING_LOG.md).

## Current Status (as of `v5.0.0`, November 26, 2026)

**No open mathematical or kernel-verification errata.** All 31 headline Lean 4.35.0 theorems (`T1a`–`T3l`), `prove_all_triad_theorems`, `nonvac_all_hypotheses`, and 7 machine-checked adversarial boundary refutations (`adv_all_boundary_refutations` — 34 audited declarations total) replay cleanly across all 6 independent proof kernels with zero `sorry`, zero `native_decide`, and axioms strictly within `[propext, Classical.choice, Quot.sound]`.

## Release-to-Release Clarifications & Tightened Results

| ID | Affected Release(s) | Scope | Clarification / Resolution | Fixed In |
|---|---|---|---|---|
| **E01** | `v1.0.0`–`v4.0.0` | Converse barrier localization (`CS-053`) | `v4.0.0` (`T1i`) proved all 510 four-marginals lie in $I_4$ and all 6 five-object retrieval marginals are $\mathbb{F}_2$-linear, leaving open whether a 6-variable inequality on `{W1, W2, A1..A4}` could separate `h_uncond`. Theorem `T1j` in `v5.0.0` resolves this completely via a single explicit $\mathbb{Z}_4$-cyclic $\mathbb{F}_2^{64}$ 6-subspace realization matching all 64 subsets at scale 4, tightening the lower bound on converse arity from $\ge 6$ variables to genuinely **$\ge 7$-variable storage-coupled** inequalities. | `v5.0.0` (`T1j`) |
| **E02** | `v3.0.0`–`v4.0.0` | ML-KEM-1024 Gaussian limit assumption (`CS-026`) | Earlier tables treated the ideal discrete Gaussian $D_{\sigma=1}$ as a feasible zero-overhead target for ML-KEM-1024. Exact non-negative discrete-convolution auditing in `v5.0.0` uncovered the **ML-KEM-1024 Discrete Gaussian DFR Paradox**: true unit-variance $D_{\sigma=1.000000105616}$ yields DFR $2^{-173.42} > 2^{-174}$ (strictly violating NIST's target!), proving that sub-Gaussian truncation is *mathematically required* at ML-KEM-1024 and locating the Pareto wall ridden by 14-bit `Dyadic-16384-A` (`6.013` b, DFR $2^{-174.03}$). | `v5.0.0` (`T2i`) |
| **E03** | `v4.0.0` | Linting & type-checking hygiene (`CI`) | `v4.0.0` CI executed `ruff` and `mypy` in non-blocking mode (`|| true`), leaving 52 style warnings and 15 minor type annotations unresolved. `v5.0.0` resolves all 52 `ruff` and 15 `mypy` diagnostics to strict `0 / 0` and promotes both checks to strict CI gates. | `v5.0.0` |

## Reporting New Errata

If you identify any mathematical error, statement-fidelity discrepancy, kernel mismatch, or reproducibility issue, please open an issue at `https://github.com/0thernes/coded-pir-mlwe-complexity-lab/issues` or email `0_0@0thernes.art` with the release tag, file/line reference, and minimal reproducing command.
