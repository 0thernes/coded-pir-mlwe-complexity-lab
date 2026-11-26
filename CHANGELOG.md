<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changelog

All notable changes to `coded-pir-mlwe-complexity-lab` are documented in this file.
The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [3.0.0] - 2026-11-25

### Added
- **4 New Zero-Mathlib Lean 4.35.0 Breakthrough Theorems (`T1h`, `T2g`, `T3g`, `T3h`) — 23 Headline Theorems / 25 Audited Declarations Total (2,995 `con-leche`/`con-ron` decls, 0 `sorry`, 0 `native_decide`, 0 warnings):**
  - **`T1h` (`PIRKoszul.lean`):** Universal 7-parameter non-Shannon cone reduction + infinite Matúš (2007) family $M_s$ ($\forall s \in \mathbb{N}$, equal to Zhang–Yeung 1998 at $s=1$) proving `h_uncond` simultaneously defeats ALL $M_s$ ($s \in \mathbb{N}$), plus exact all-$M$ multi-file Koszul contraction $\rho_{\mathrm{KV}}^j < \rho_{\mathrm{LFSR}}^j$ ($\forall j \ge 1$).
  - **`T2g` (`MLWETightness.lean`):** Universal non-asymptotic Pearson $\chi^2$/Hermite-4 QGTL variational Rényi-2 bridge (analytically capturing $75.5\%$ of $R_2-1$ for $\mathrm{CBD}_2$ and $89.5\%$ for `Dyadic-256` at $\sigma=1$) + 9-bit constant-time **`Dyadic-512`** noise $(1,8,44,120,166,120,44,8,1)/512$ ($\mathrm{Var}=3/2$, $\mu_4=27/4$, exact zero excess kurtosis $\kappa_{\mathrm{ex}} = 0$, exact Gaussian QGTL metric determinant $\det(g) = 1/2$, collapsing ML-KEM-512 keygen loss $12.89\times$ from $7.630$ to $0.592$ bits while passing exact FIPS 203 DFR $2^{-139.26} < 2^{-138.8}$).
  - **`T3g` (`KoszulTensor.lean`):** Symbolic ALL-$m$ 1-nnz/row monomial left-inverse proving $\mathrm{rank}_F(\langle m,m,m\rangle) \ge m^2 + 2$ for EVERY $m \ge 2$ and EVERY `SimpleField F` (incl. $\mathrm{char}\,2$) + degree-$(m-1)$ Koszul flattening ceiling $m^2 + m$.
  - **`T3h` (`StrassenWinograd.lean`, NEW):** Complete characteristic-free proof of **Exact Strassen–Winograd $\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$** over EVERY `SimpleField F` (including $\mathbb{F}_2$!): explicit 7-product upper bound plus direct substitution/rank-drop lower bound refuting every rank-$\le 6$ decomposition.
- **Native C11 (`native/`):** Branchless 9-bit `triad_dyadic512_sample_ct`, `triad_mlkem_dyadic512_opt`, `triad_verify_strassen_7prod`, `triad_verify_all_m_koszul_monomial(m)`, 3 new CLI commands (`dyadic512`, `strassen`, `koszul-allm`), and 8 new unit tests (**57/57 tests** + 512 fuzz).
- **Eshkol AD & Exact Python (`eshkol/`, `python/`, `tests/`):** Forward-mode AD optimization of `Dyadic-512` (`|dR2/dsigma| = 3.57e-6`), exact non-negative FIPS 203 discrete-convolution DFR suite passing all three parameter sets (`512`: $2^{-139.26}$, `768`: $2^{-166.12}$, `1024`: $2^{-174.26}$), 14,850 singleton Matúš $s \in \{1..5\}$ checks (0 violations), exact $\mathrm{rank}_F(\Phi_2(\langle 3,3,3\rangle)) = 324$ over $\mathbb{F}_2$ & $\mathbb{F}_{101}$ ($\implies \ge 12$), and expanded `pytest` suite (**16/16 tests, 10/10 killed mutants**).
- **16-Page Preprint, Figure 6, Citations & Interactive Blueprint:** Added Crossref-verified `Matus2007` and `Winograd1971` (28/28 live HTTP 200 citations), **`fig6_mlkem_dfr_variational_and_allm_koszul.pdf`**, updated `paper/main.tex` to 16 pages (0 overfull hboxes), and upgraded `docs/site/` interactive 23-theorem Proof Blueprint DAG & ML-KEM DFR explorer.

### Fixed
- **H16 (`bug`/`issue`):** Removed duplicate `triad_dyadic512` edit in `triad_core.c`; fixed `Matus2007` nested BibTeX brace syntax for `check_citations.py`; aligned Matúš ordered pair-of-pairs singleton count (`14,850`); eliminated 4 Overfull `\hbox`es in `paper/main.tex` and polished `fig6` annotation clearances via visual inspection.

## [2.0.0] - 2026-11-25

### Added
- **5 New Zero-Mathlib Lean 4.35.0 Theorems (`T1g`, `T2e`, `T2f`, `T3e`, `T3f`) — 19 Headline Theorems / 21 Audited Declarations Total (2,418 `con-leche`/`con-ron` decls, 0 `sorry`, 0 `native_decide`, 0 warnings):**
  - **`T1g` (`PIRKoszul.lean`):** Exact algebraic Zhang–Yeung (1998) reduction $\mathrm{ZY98}(A,B;C,D) = \mathrm{Ing}(C,D;A,B) + I(A;C\mid D) + I(A;D\mid C) + I(C;D\mid A)$ proving `h_uncond` unconditionally defeats Zhang–Yeung (1998) too + symmetric $M \ge 3$ 1-flag Koszul denominator breaking Sun–Zhang's $E \ge KT$ wall for all $M \ge 3$ (and zero-error $(6,3,3)$ rate $10/17$ verified over $\mathbb{F}_7$).
  - **`T2e` (`MLWETightness.lean`):** Pure-integer Cauchy–Schwarz finite-support Rényi-2 floor $(1-\tau_S(\sigma))^{-1}$; 4–8 bit $\mathrm{Var}=1$ phase transition & optimal 1-byte constant-time **`Dyadic-256`** distribution $(1,14,63,100,63,14,1)/256$ ($\mathrm{Var}=1$, identical to FIPS 203 $\mathrm{CBD}_2$) collapsing ML-KEM-1024 loss $17.7\times$ ($37.842 \to 2.138$ bits; ML-KEM-768 $28.382 \to 1.604$ bits); universal QGTL Provost–Vallée PSD $4\det(g) \ge \Omega_{\theta\sigma}^2$ (`CM-048`) and exact symmetric Metric–Kurtosis ordering $3/8 < 15/32 < 1/2$.
  - **`T2f` (`MLWETightness.lean`):** Universal $m$-twisted DFT selection rule over ANY `CommRing R` (`[propext]` alone; `QC-042`), generalizing Chen Step 9 ($m=2$) to arbitrary twist order $m \ge 1$.
  - **`T3e` (`KoszulTensor.lean`, NEW):** Field-universal Landsberg–Ottaviani Koszul flattening bridge unifying exterior wedges $u \wedge \cdot$ from PIR (`T1a`) with matrix multiplication (`CS-004`) and algebraic complexity (`CS-012`): Steinitz/Gauss matrix rank bound + 18-nnz $\{-1,0,+1\}$ left-inverse $L_2 \in \mathbb{Z}^{16\times 24}$ certifying $\mathrm{rank}_F(\langle 2,2,2\rangle) \ge 6$ and $L_3 \in \mathbb{Z}^{9\times 9}$ certifying $\mathrm{rank}_F(T_3) \ge 5$ over **every** field $F$ including characteristic 2!
  - **`T3f` (`ComplexityTriad.lean`):** Constructive Shannon (1949) finite circuit-counting non-surjectivity (`CS-001`/`CS-010`) + Katz–Trevisan $q$-query LDC smoothness averaging bound (`CS-051`).
- **Native C11 (`native/`):** Constant-time 6-comparison byte sampler `triad_dyadic256_sample_ct`, `triad_mlkem_dyadic256_opt`, `triad_verify_twisted_dft`, `triad_verify_koszul_flattening_certs`, QGTL PSD fuzz guard, 3 new CLI commands (`dyadic256`, `twisted`, `koszul-tensor`), and 9 new unit tests (**49/49 tests**).
- **Eshkol AD & Exact Python (`eshkol/`, `python/`, `tests/`):** Live forward-mode AD optimization of `Dyadic-256` ($|dR_2/d\sigma| = 7.77 \times 10^{-9}$), 60-digit `Dyadic-256` + QGTL Metric–Kurtosis + $m$-twisted DFT + Koszul tensor verifiers, and expanded `pytest` suite (**15/15 tests, 8/8 killed mutants**).
- **Publication Figures, 14-Page Preprint & Interactive Proof Blueprint:** Upgraded `fig3`, `fig4` (5-node Mega Atlas V2 architecture), added **`fig5_dyadic256_and_koszul_tensor.pdf`**, updated `paper/main.tex` to 14 pages (0 overfull hboxes, 26/26 live HTTP-200 citations), and added zero-CDN interactive GitHub Pages Proof Blueprint DAG & Triad Explorer (`docs/site/index.html`, `docs/site/blueprint.html`, `.github/workflows/pages.yml`), advancing Build Standard `A27` to `PASS`.

### Fixed
- **H14 (`dilemma`/`hole`):** Rejected an asymmetric 3-round $M=3$ flag-split scheme at $(4,2,2)$ after privacy audit exposed pair-coupling leakage, replacing it with the 100% symmetric 1-flag sum scheme proved in `T1g`.
- **H15 (`issue`):** Verified DOIs for Landsberg–Ottaviani (2013) (`10.1007/s10231-011-0238-6`), Strassen (1969) (`10.1007/BF02165411`), and Shannon (1949) (`10.1002/j.1538-7305.1949.tb03624.x`) via Crossref API before adding to `paper/refs.bib`, and eliminated visual label overlaps in `fig4`/`fig5` via screenshot inspection.

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
