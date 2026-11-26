# `coded-pir-mlwe-complexity-lab`

[![License: Apache-2.0](https://img.shields.io/badge/Code%20License-Apache--2.0-blue.svg)](LICENSE)
[![Docs License: CC-BY-4.0](https://img.shields.io/badge/Docs%20%26%20Paper-CC--BY--4.0-lightgrey.svg)](LICENSE-DOCS)
[![Project Status: Active](https://www.repostatus.org/badges/latest/active.svg)](https://www.repostatus.org/#active)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0%20Zero--Mathlib%20(31%20Theorems)-purple.svg)](lean/lean-toolchain)
[![CI](https://github.com/0thernes/coded-pir-mlwe-complexity-lab/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/coded-pir-mlwe-complexity-lab/actions/workflows/ci.yml)
[![Pages](https://img.shields.io/badge/Interactive-Proof%20Blueprint-0284c7.svg)](https://0thernes.github.io/coded-pir-mlwe-complexity-lab/)

Machine-checked zero-Mathlib **Lean 4.35.0** proofs (**31 theorems `T1a`–`T3l`** + **7 adversarial boundary refutations** = **34 audited declarations** across **6 independent proof kernels**, **4,300 `con-leche`/`con-ron` verified declarations**, silent 0-error `nanoda_bin`, plus a **live negative kernel-rejection gate**), multi-language verification engines (**C11** `79/79` tests, **Python 3.12** `0 ruff / 0 mypy`, **Eshkol v1.3.6** forward-mode dual-number AD), an interactive **Proof Blueprint DAG**, and an AMS-LaTeX preprint (`v5.0.0`, 8 vector PDF figures, 36/36 live HTTP-200 citations) establishing sharp algebraic, information-theoretic, and cryptanalytic results across **Coded/Byzantine PIR & Single $\mathbb{F}_2^{64}$ 6-Obj Realization (`CS-053`)**, **Module-LWE Tightness, ML-KEM-1024 Gaussian DFR Paradox & 14-Bit `Dyadic-16384-A/B` (`CS-026`/`QC-042`/`CM-048`)**, **Schwartz–Zippel & Two-Sided Strassen–Brockett–Dobkin Sandwich (`CS-001`/`CS-004`/`CS-010`/`CS-012`/`CS-051`)**, and **Infinite-Family Zero-Reals Paley/Conference Capacity $\Theta(G)=\sqrt{4k+1}$ (`CS-CMP-012`)**.

![Project Social Preview](docs/media/social-preview.svg)

**Author:** Alexander S. Donahue (Independent Researcher, Spokane, WA, USA; ORCID [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648))  
**Status:** active (`repostatus.org/#active`) · Research preprint `v5.0.0` (not externally peer-reviewed; AI-assisted under human direction; see [LIMITATIONS.md](LIMITATIONS.md) & [ERRATA.md](ERRATA.md))  
**Interactive Proof Blueprint:** [`https://0thernes.github.io/coded-pir-mlwe-complexity-lab/`](https://0thernes.github.io/coded-pir-mlwe-complexity-lab/) ([DAG Blueprint](https://0thernes.github.io/coded-pir-mlwe-complexity-lab/blueprint.html))  
**White Paper PDF:** [`dist/Donahue_2026_coded_pir_mlwe_complexity_frontier.pdf`](dist/Donahue_2026_coded_pir_mlwe_complexity_frontier.pdf) · **arXiv Source Tarball:** [`dist/arxiv_submission.tar.gz`](dist/arxiv_submission.tar.gz)

---

## Core Machine-Checked Results (`T1a`–`T3l`)

Every theorem below is formally proved in zero-Mathlib **Lean 4.35.0** with **zero `sorry`**, **zero `native_decide`**, **zero custom axioms**, concrete non-vacuity witnesses (`lean/TriadFrontier/NonVacuity.lean`), and 7 machine-checked negative boundary refutations (`lean/TriadFrontier/AdversarialTests.lean`), and independently cross-checked in **C11** (`-std=c11 -Wall -Wextra -Wpedantic -Werror`, 79/79 tests), **60-digit exact Python** (0 `ruff`, 0 `mypy`), and **Eshkol v1.3.6 dual-number AD**:

| ID | Frontier | Headline Result | Lean Entry Point |
|---|---|---|---|
| **T1a** | `CS-053` | Exterior-power Koszul–Veronese PIR rank identity over any `CommRing`, exact Pascal interference savings $K\binom{T}{T'} = \lambda^\star + (K-T')\binom{T-1}{T'}$, and flagship $(E,K,T)=(6,3,3)$ rate $10/17 > 4/7$ (valid over $\mathbb{F}_7$) | `TriadFrontier.Solution.t1a_koszul_veronese_rank_identity` |
| **T1b** | `CS-053` | Exact $K \leftrightarrow T$ symmetry and universal strict domination over the Sun–Zhang (2026) LFSR coded-colluding capacity in both single-file and multi-file $P$-out-of-$M$ regimes via surplus $(K-1)(T-1)E^2 > 0$ | `TriadFrontier.Solution.t1b_universal_koszul_domination_over_lfsr` |
| **T1c** | `CS-053` | Non-vacuous Byzantine-robust double-counting converse reduction, sub-$KT$ match at $E = K+1$ to the Sun–Jafar unrestricted ceiling, and kernel-certified zero-error $\mathbb{F}_{11}$ Byzantine rate-$2/5$ scheme at $(M=2,N=6,K=2,T=2,B=1,E=4)$ (all 90 exact matrix inverses verified inside the Lean kernel) | `TriadFrontier.Solution.t1c_byzantine_robust_capacity_and_f11_certificate` |
| **T1d** | `CS-053` | Sharp flag-privacy dimension thresholds ($K=2,T=2 \iff E \ge 4$; $T=3,K=2$ zero-error $\iff E \ge 6$) and universal overlap feasibility $Ew \le K\delta\sigma$ (tight iff $E=K+1$) | `TriadFrontier.Solution.t1d_flag_privacy_and_feasibility_dimensions` |
| **T1e** | `CS-053` | Exact unconditioned 12-variable pure-integer (scale-128) polymatroid `h_uncond` proving ALL 270,336 elemental Shannon inequalities (via 330 canonical $S_4$ orbits), all 99 PIR equalities, and all 1,485 singleton Ingleton inequalities at $C = 8/13 > 3/5$ (`[propext]` only!) | `TriadFrontier.Solution.t1e_unconditioned_shannon_ingleton_barrier` |
| **T1f** | `CS-053` | Projective $\mathbb{P}^3$ linear impossibility over ANY `SimpleField F`: four pairwise-intersecting 2-subspaces of $F^4$ are either concurrent or coplanar | `TriadFrontier.Solution.t1f_projective_p3_linear_impossibility` |
| **T1g** | `CS-053` | Exact algebraic Zhang–Yeung (1998) reduction $\mathrm{ZY98}(A,B;C,D) = \mathrm{Ing}(C,D;A,B) + I(A;C\mid D) + I(A;D\mid C) + I(C;D\mid A)$ (proving `h_uncond` defeats Zhang–Yeung too!) + symmetric $M \ge 3$ 1-flag Koszul denominator breaking $E \ge KT$ for all $M \ge 3$ | `TriadFrontier.Solution.t1g_zhang_yeung_reduction_and_mfile_koszul` |
| **T1h** | `CS-053` | Universal 7-parameter non-Shannon cone reduction + infinite Matúš (2007) family $M_s$ ($\forall s \in \mathbb{N}$, equal to `ZY98` at $s=1$) proving `h_uncond` defeats ALL $M_s$ simultaneously + exact all-$M$ multi-file Koszul contraction $\rho_{\mathrm{KV}}^j < \rho_{\mathrm{LFSR}}^j$ | `TriadFrontier.Solution.t1h_infinite_nonshannon_cone_barrier_and_contraction` |
| **T1i** | `CS-053` | **Total 4-Variable Entropic & 5-Object $\mathbb{F}_2$-Linear Subspace Barrier:** ALL 495 singleton + 15 retrieval 4-marginals of `h_uncond` (510 total) decompose at denominator 3 into 23 explicit $\mathbb{F}_2/\mathbb{F}_3$ linear-subspace rays (defeating **every** 4-variable linear information inequality!) AND ALL $\binom{6}{5}=6$ five-object retrieval marginals decompose into explicit $\mathbb{F}_2$-linear subspace arrangements | `TriadFrontier.Solution.t1i_total_4var_entropic_and_5obj_linear_barrier` |
| **T1j** | `CS-053` | **Single $\mathbb{F}_2^{64}$ Total 6-Object Retrieval Realization:** One explicit $\mathbb{Z}_4$-cyclic 6-subspace arrangement in $\mathbb{F}_2^{64}$ (generated by 3 sparse weight-3 rows `[8,17,19]`, `[11,12,18]`, `[5,11,18]`) realizes ALL 64 subset entropies of `{W1, W2, A1, A2, A3, A4}` at exact scale 4—defeating every 6-object retrieval inequality (linear or non-linear!) and pushing the converse barrier to **$\ge 7$-variable storage-coupled** inequalities | `TriadFrontier.Solution.t1j_total_6obj_f2_entropic_realizability_barrier` |
| **T2a** | `CS-026` | Commutative-ring determinant-ideal secret independence ($\det(B) = q^m$, unimodularly invariant), refuting Luo (`arXiv:2604.15858`) | `TriadFrontier.Solution.t2a_determinant_ideal_secret_independence` |
| **T2b** | `CS-026` | Ring-universal anti-periodic DFT even-mode cancellation ($\hat{f}(2k) \equiv 0$) + odd $c,D$ quadratic Gauss parity witness explaining Chen (`ePrint 2024/555`) Step 9 | `TriadFrontier.Solution.t2b_chen_step9_antiperiodic_dft_cancellation` |
| **T2c** | `CS-026` | Exact FIPS 203 $\mathrm{CBD}_2$ ($\mathrm{Var}=1, \mu_4=5/2$) vs. $\mathrm{CBD}_3$ ($\mathrm{Var}=3/2, \mu_4=6$) moments, cyclotomic trace-orthogonality over any `SimpleField F`, and cleared-denominator $4.96\times$ Rényi-2 tightness cliff (60-digit $\mathrm{CBD}_2$: $37.84$ bits at ML-KEM-1024 vs. $\mathrm{CBD}_3$: $7.63$ bits at ML-KEM-512) | `TriadFrontier.Solution.t2c_mlkem_cbd_renyi_cliff` |
| **T2d** | `CS-026` | QGTL shifted-LWE Berry curvature normalization invariance, exact symmetry vanishing at $e_0 = 0$, and strict bias witness ($-512 \neq 0$ at $e_0 = 1$) | `TriadFrontier.Solution.t2d_qgtl_shifted_lwe_berry_curvature` |
| **T2e** | `CS-026 / CM-048` | Pure-integer Cauchy–Schwarz finite-support Rényi-2 floor $(1-\tau_S)^{-1}$, optimal 1-byte constant-time **`Dyadic-256`** noise $(1,14,63,100,63,14,1)/256$ ($\mathrm{Var}=1$, $17.7\times$ collapse to $2.14$ bits at ML-KEM-1024), universal QGTL Provost–Vallée PSD $4\det(g) \ge \Omega_{\theta\sigma}^2$, and exact Metric–Kurtosis ordering $3/8 < 15/32 < 1/2$ | `TriadFrontier.Solution.t2e_dyadic256_renyi_floor_and_qgtl_psd` |
| **T2f** | `CS-026 / QC-042` | Universal $m$-twisted DFT selection rule over ANY `CommRing R` ($\omega^D = \zeta, f(qD+x) = \zeta^{qr}f(x), \sum \zeta^{q(r+k)} = 0 \implies \hat{f}_{mD}(k) = 0$; `[propext]` alone!) | `TriadFrontier.Solution.t2f_universal_twisted_dft_selection_rule` |
| **T2g** | `CS-026 / CM-048` | Universal non-asymptotic Pearson $\chi^2$/Hermite-4 QGTL variational Rényi-2 bridge + 9-bit constant-time **`Dyadic-512`** noise $(1,8,44,120,166,120,44,8,1)/512$ ($\mathrm{Var}=3/2, \mu_4=27/4, \kappa_{\mathrm{ex}}=0, \det(g)=1/2$, $12.9\times$ ML-KEM-512 drop to $0.592$ bits) + exact FIPS 203 DFR audit passing ML-KEM-512/768/1024 | `TriadFrontier.Solution.t2g_qgtl_renyi_variational_bridge_and_dyadic512` |
| **T2h** | `CS-026 / CM-048` | **All-Order Rényi-$(m+1)$ Hölder Floor, Exact TV–$\chi^2$ Bridge ($4\mathrm{TV}^2 \le R_2-1$), & 10-Bit Bai-Optimal `Dyadic-1024-A/B`:** Collapses Bai et al. (2018) end-to-end security overhead $9.19\times$ at ML-KEM-1024 ($67.14 \to 7.31$ bits, saving $59.8$ bits!) and $4.83\times$ at ML-KEM-512 ($24.77 \to 5.13$ bits), while passing all three FIPS 203 DFR targets | `TriadFrontier.Solution.t2h_all_order_renyi_holder_tv_and_dyadic1024` |
| **T2i** | `CS-026 / CM-048` | **Formalized Bai Engine (DPI, All-Order Tensorization, $R_\infty$ Floor), ML-KEM-1024 Gaussian DFR Paradox, & 14-Bit `Dyadic-16384-A/B`:** Proves Rényi-2 DPI, exact all-order tensorization, & $R_\infty$ monotonicity/floor in pure `Nat`; uncovers that true unit-variance discrete Gaussian $D_{\sigma=1.0000001}$ *fails* ML-KEM-1024 DFR ($2^{-173.42} > 2^{-174}$!); delivers 14-bit CT `Dyadic-16384-A` ($11.17\times$ drop: $67.14 \to 6.013$ b, DFR $2^{-174.03}$) & `Dyadic-16384-B` ($41.9\times$ **sub-1-bit** ML-KEM-512 drop: $24.77 \to 0.5916$ b, DFR $2^{-139.31}$) | `TriadFrontier.Solution.t2i_bai_engine_dpi_tensorization_and_dyadic16384` |
| **T3a** | `CS-001` | Constructive existence and global uniqueness of the multilinear extension $\tilde{f} : F^n \to F$ over any `SimpleField F` (Algebrization algebraic core) | `TriadFrontier.Solution.t3a_algebrization_multilinear_extension_uniqueness` |
| **T3b** | `CS-026 → CS-001` | LWE/LWR pseudorandom function $\varepsilon$-indistinguishability blocks $\delta$-large constructive Natural Proofs | `TriadFrontier.Solution.t3b_lwe_to_natural_proofs_obstruction` |
| **T3c** | `CS-053 ↔ CS-051` | Katz–Trevisan $B$-Byzantine zero-error PIR / Locally Decodable Code minimum Hamming distance $d_{\min} \ge 2B + 1$ | `TriadFrontier.Solution.t3c_katz_trevisan_byzantine_pir_ldc_distance` |
| **T3d** | `CS-026 ↔ CS-053` | Sharp FIPS 203 `Compress_1` margin $|e| \le 831$ (round-half-up $+1665$, failing sharply at $+832$ for $b \in \{0,1\}$) and additive single-server MLWE-PIR noise depth ceiling $M \le \lfloor 831 / b_{\mathrm{step}} \rfloor$ | `TriadFrontier.Solution.t3d_mlwe_single_server_pir_noise_ceiling` |
| **T3e** | `CS-053 ↔ CS-004 / CS-012` | Field-universal Landsberg–Ottaviani Koszul flattening tensor rank bridge unifying PIR wedge $u \wedge \cdot$ with matrix multiplication tensor rank via pure-integer $\{-1,0,+1\}$ left-inverses: $\mathrm{rank}_F(\langle 2,2,2\rangle) \ge 6$ and $\mathrm{rank}_F(T_3) \ge 5$ over **every** `SimpleField F` (incl. $\mathrm{char}\,2$!) | `TriadFrontier.Solution.t3e_koszul_flattening_tensor_rank_bridge` |
| **T3f** | `CS-001 / CS-010 / CS-051` | Shannon (1949) finite circuit-counting non-surjectivity ($C < M \implies \exists f$ uncomputed) + Katz–Trevisan $q$-query LDC smoothness averaging bound | `TriadFrontier.Solution.t3f_shannon_counting_and_ldc_smoothness` |
| **T3g** | `CS-004 / CS-012` | Symbolic ALL-$m$ 1-nnz/row monomial left-inverse proving $\mathrm{rank}_F(\langle m,m,m\rangle) \ge m^2 + 2$ for EVERY $m \ge 2$ and EVERY `SimpleField F` (incl. $\mathrm{char}\,2$) + degree-$(m-1)$ Koszul flattening ceiling $m^2 + m$ | `TriadFrontier.Solution.t3g_all_m_koszul_matmul_lower_bound` |
| **T3h** | `CS-004 / CS-012` | Complete characteristic-free proof of **Exact Strassen–Winograd $\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$** over EVERY `SimpleField F` (including $\mathbb{F}_2$!): explicit 7-product upper bound + direct substitution/rank-drop lower bound refuting rank $\le 6$ | `TriadFrontier.Solution.t3h_strassen_winograd_exact_rank_seven` |
| **T3i** | `CS-004 / CS-012` | **Field-Universal Brockett–Dobkin (1978) Rectangular & Quadratic MatMul Bound:** $\mathrm{rank}_F(\langle m,k,p\rangle) \ge \max(mk+mp-m, mk+kp-k, mp+kp-p)$, quadratic $\mathrm{rank}_F(\langle m,m,m\rangle) \ge 2m^2 - m$ (shattering Koszul ceiling $m^2+m$ for all $m \ge 3$!), & Strassen lift $\mathrm{rank}_F(\langle m,2,p\rangle) \ge mp+3$ over EVERY `SimpleField F` | `TriadFrontier.Solution.t3i_brockett_dobkin_rectangular_and_quadratic_matmul_bound` |
| **T3j** | `CS-CMP-012 ↔ CS-053/004` | **Zero-Error Shannon Capacity (Zero Reals!):** Field-universal Haemers (1979) rank bound $|S| \le r^t$ ($\forall F$), **exact Lovász (1979) Pentagon Theorem $\Theta(C_5)=\sqrt{5}$** via exact 3-term $\mathbb{Z}[\sqrt{5}]$ SOS of $80 M_6$ ($k^2 \le 5^t$ & $\alpha(C_5^{\boxtimes 2m})=5^m$), & **exact $C_7$ minimum Haemers rank $= 4$** over EVERY field $F$ ($\alpha(C_7^{\boxtimes 2m}) \ge 10^m$) | `TriadFrontier.Solution.t3j_shannon_capacity_lovasz_c5_and_haemers` |
| **T3k** | `CS-001 / CS-004 / CS-053` | **Multivariate Schwartz–Zippel & Two-Sided Strassen–Brockett–Dobkin Sandwich:** Field-universal Schwartz–Zippel root bound $|\{a \in S^n : P(a)=0\}| \le d s^{n-1}$ ($\forall F$ incl. $\mathbb{F}_2$), $S_3$ transposition symmetry, Kronecker submultiplicativity, & exact two-sided sandwich $2\cdot 4^k - 2^k \le \mathrm{rank}_F(\langle 2^k,2^k,2^k\rangle) \le 7^k$ ($\forall k, F$) | `TriadFrontier.Solution.t3k_schwartz_zippel_and_strassen_sandwich` |
| **T3l** | `CS-CMP-012` | **Infinite-Family Zero-Reals Paley/Conference Capacity $\Theta(G)=\sqrt{4k+1}$:** Universal symbolic 2-block $\mathbb{Z}[\sqrt{p}]$ SOS identity $R^\top R = 2p\sqrt{p}\,R$ + self-complement lift proving exact $\alpha(G^{\boxtimes 2m}) = (4k+1)^m$ and $s^2 \le (4k+1)^t$ for EVERY $k \ge 1$, concretely instantiated in Lean for $P_5 = C_5$, $P_{13}$, and $P_{17}$ (and C11/Python for $P_5..P_{41}$) | `TriadFrontier.Solution.t3l_infinite_paley_conference_shannon_capacity` |

---

## 5-Second Lean 4.35.0 Axiom Audit (Verbatim)

Exact verbatim output of `cd lean && lake env lean VerifyAxioms.lean` (checked for zero drift in CI by `scripts/check_readme_axioms.py` against [`results/lean_axioms.txt`](results/lean_axioms.txt) — 34 audited declarations, 4,300 `con-leche`/`con-ron` verified declarations, silent 0-error `nanoda_bin`, plus a live negative kernel-rejection gate):

```text
'TriadFrontier.Solution.t1a_koszul_veronese_rank_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'TriadFrontier.Solution.t1b_universal_koszul_domination_over_lfsr' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t1c_byzantine_robust_capacity_and_f11_certificate' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t1d_flag_privacy_and_feasibility_dimensions' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t1e_unconditioned_shannon_ingleton_barrier' depends on axioms: [propext]
'TriadFrontier.Solution.t1f_projective_p3_linear_impossibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TriadFrontier.Solution.t1g_zhang_yeung_reduction_and_mfile_koszul' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t1h_infinite_nonshannon_cone_barrier_and_contraction' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t1i_total_4var_entropic_and_5obj_linear_barrier' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t1j_total_6obj_f2_entropic_realizability_barrier' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t2a_determinant_ideal_secret_independence' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t2b_chen_step9_antiperiodic_dft_cancellation' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t2c_mlkem_cbd_renyi_cliff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TriadFrontier.Solution.t2d_qgtl_shifted_lwe_berry_curvature' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t2e_dyadic256_renyi_floor_and_qgtl_psd' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t2f_universal_twisted_dft_selection_rule' depends on axioms: [propext]
'TriadFrontier.Solution.t2g_qgtl_renyi_variational_bridge_and_dyadic512' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TriadFrontier.Solution.t2h_all_order_renyi_holder_tv_and_dyadic1024' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t2i_bai_engine_dpi_tensorization_and_dyadic16384' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t3a_algebrization_multilinear_extension_uniqueness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TriadFrontier.Solution.t3b_lwe_to_natural_proofs_obstruction' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t3c_katz_trevisan_byzantine_pir_ldc_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TriadFrontier.Solution.t3d_mlwe_single_server_pir_noise_ceiling' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t3e_koszul_flattening_tensor_rank_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TriadFrontier.Solution.t3f_shannon_counting_and_ldc_smoothness' depends on axioms: [propext, Quot.sound]
'TriadFrontier.Solution.t3g_all_m_koszul_matmul_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TriadFrontier.Solution.t3h_strassen_winograd_exact_rank_seven' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TriadFrontier.Solution.t3i_brockett_dobkin_rectangular_and_quadratic_matmul_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TriadFrontier.Solution.t3j_shannon_capacity_lovasz_c5_and_haemers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TriadFrontier.Solution.t3k_schwartz_zippel_and_strassen_sandwich' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TriadFrontier.Solution.t3l_infinite_paley_conference_shannon_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TriadFrontier.Solution.prove_all_triad_theorems' depends on axioms: [propext, Classical.choice, Quot.sound]
'TriadFrontier.NonVacuity.nonvac_all_hypotheses' depends on axioms: [propext, Quot.sound]
'TriadFrontier.AdversarialTests.adv_all_boundary_refutations' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Zero `sorryAx` · Zero `Lean.ofReduceBool` / `native_decide` · Zero `Lean.trustCompiler` · Zero custom axioms.**

---

## Quickstart

Clone and verify all four independent layers (Lean 4.35.0, C11, Eshkol dual-number AD, and exact Python + pytest):

```bash
git clone https://github.com/0thernes/coded-pir-mlwe-complexity-lab.git
cd coded-pir-mlwe-complexity-lab

# 1. Zero-Mathlib Lean 4.35.0 proofs + strict axiom & kernel audit (31 theorems + 7 refutations, 6 kernels)
(cd lean && lake build && lake env lean VerifyAxioms.lean && lake env leanchecker Solution && lake env leanchecker-paranoid Solution)

# 2. Native C11 core (-std=c11 -Wall -Wextra -Wpedantic -Werror, 79/79 tests + 512+ fuzz)
make -C native clean test

# 3. Eshkol v1.3.6 forward-mode dual-number AD modules (3/3, incl. Dyadic-256/512/1024/16384-A/B)
node eshkol/run_eshkol_ad.mjs

# 4. Exact Python verification suite, differential/mutation tests (14/14 mutants), lint, axiom drift & citations
pip install numpy scipy matplotlib pytest ruff mypy
PYTHONPATH=python pytest tests/test_all.py -v
ruff check python tests scripts examples
mypy python/triad_verify scripts --ignore-missing-imports
python scripts/check_readme_axioms.py
python scripts/check_citations.py
```

Or run everything via `just reproduce`, `./scripts/run_all.sh`, or `pwsh -File scripts/run_all.ps1`.

---

## Usage & Examples

Run the standalone quickstart demonstration or individual computational verification engines:

```bash
# Quickstart interactive summary across Pillars I, II, and III
PYTHONPATH=python python examples/quickstart_demo.py

# C11 CLI audit commands
./native/build/triad_cli koszul 3 2 3
./native/build/triad_cli f11-byz
./native/build/triad_cli ret6-f2
./native/build/triad_cli renyi 2
./native/build/triad_cli dyadic256
./native/build/triad_cli dyadic512
./native/build/triad_cli dyadic1024a
./native/build/triad_cli dyadic1024b
./native/build/triad_cli dyadic16384a
./native/build/triad_cli dyadic16384b
./native/build/triad_cli chen 7 3
./native/build/triad_cli twisted 4 5 1
./native/build/triad_cli qgtl 2 1.023 0.25
./native/build/triad_cli koszul-tensor
./native/build/triad_cli strassen
./native/build/triad_cli koszul-allm 3
./native/build/triad_cli koszul-allm 4
./native/build/triad_cli lovasz-c5
./native/build/triad_cli c7-cap
./native/build/triad_cli paley-cap 13
./native/build/triad_cli paley-cap 17

# Exact Python verification modules
PYTHONPATH=python python python/triad_verify/pir_koszul.py
PYTHONPATH=python python python/triad_verify/polymatroid_barrier.py
PYTHONPATH=python python python/triad_verify/mlwe_tightness.py
PYTHONPATH=python python python/triad_verify/complexity_triad.py
```

See [`examples/README.md`](examples/README.md) for annotated outputs and [`REPLICATION.md`](REPLICATION.md) for the clean-room replication protocol.

---

## Honest Scope & Explicit Non-Claims

This work **does NOT solve** and explicitly affirms as **OPEN**:
1. **$\mathrm{P} \neq \mathrm{NP}$ and super-linear explicit Boolean circuit lower bounds (`CS-001` / `CS-010`)** — `T3a`, `T3b`, and `T3f` formalize Algebrization uniqueness, conditional Natural Proofs obstructions, and non-constructive Shannon counting.
2. **Matrix multiplication exponent $\omega = 2$ (`CS-004`) and Valiant's $\mathrm{VP} \neq \mathrm{VNP}$ (`CS-012`)** — `T3e`, `T3g`, `T3h`, `T3i`, and `T3k` establish exact characteristic-free tensor rank bounds ($\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$, $\mathrm{rank}_F(\langle m,m,m\rangle) \ge 2m^2 - m$, $2\cdot 4^k - 2^k \le \mathrm{rank}_F(\langle 2^k,2^k,2^k\rangle) \le 7^k$ over every field including $\mathbb{F}_2$), not asymptotic $\omega$ or $\mathrm{VP} \neq \mathrm{VNP}$.
3. **Non-linear $C(2,4,2,2) \in [3/5, 8/13]$ and general $M \ge 3$ non-LFSR PIR above LFSR when $E \ge KT$ (`CS-053`)** — `T1e` and `T1g`–`T1j` narrow the converse barrier beyond every 4-, 5-, and 6-object retrieval inequality (all 64 subsets of `{W1, W2, A1..A4}` are realized by a single explicit $\mathbb{F}_2^{64}$ arrangement!), confining any converse to genuinely **$\ge 7$-variable storage-coupled** inequalities.
4. **Exact Shannon capacity $\Theta(C_7) \in [\sqrt{10}, \vartheta(C_7) \approx 3.317667]$ (`CS-CMP-012`)** — `T3j` and `T3l` prove exact $\Theta(G) = \sqrt{4k+1}$ for EVERY self-complementary conference graph (including $P_5 = C_5, P_{13}, P_{17}$) and exact minimum Haemers rank $4$ for $C_7$ over every field $F$, leaving exact $\Theta(C_7)$ open.
5. **Worst-case quantum hardness of MLWE (`CS-026` / `QC-042`)** — Refuting Luo (2026) (`T2a`), proving the $m$-twisted DFT rule (`T2b`, `T2f`), formalizing Bai et al. (2018) DPI/tensorization/$R_\infty$, exposing the ML-KEM-1024 Gaussian DFR Paradox, and collapsing Bai loss via `Dyadic-256`/`512`/`1024`/`16384-A/B` (`T2e`, `T2g`–`T2i`) do not prove MLWE is quantum-hard.

Full boundaries, real-vs-metaphor notes on Tsotchke-inspired components, errata, and falsification protocols are documented in [`CLAIMS.md`](CLAIMS.md), [`LIMITATIONS.md`](LIMITATIONS.md), [`ERRATA.md`](ERRATA.md), and [`docs/statement-fidelity.md`](docs/statement-fidelity.md).

---

## Repository Map

- `lean/` — Zero-Mathlib Lean 4.35.0 proof library (`TriadFrontier/*` incl. `PIRLinearCerts.lean`, `KoszulTensor.lean`, `StrassenWinograd.lean`, `BrockettDobkin.lean`, `ShannonCapacity.lean`, `AlgebraicComplexity.lean`, `PaleyCapacity.lean`, `AdversarialTests.lean`), Palomar comparator contract (`PalomarChallenge.lean`, `PalomarSolution.lean`, `comparator.json`), `VerifyAxioms.lean` (34 decls), and `formalization.yaml`.
- `native/` — Zero-warning C11 library (incl. constant-time `Dyadic-256`/`512`/`1024`/`16384-A/B` samplers, $\mathbb{F}_2^{64}$ 6-obj realization, $m$-twisted DFT, Koszul flattening, Strassen 7-product, all-$m$ monomial, and exact $\mathbb{Z}[\sqrt{p}]$ Paley/conference SOS certs for $P_5..P_{41}$), CLI, 79-test unit + 512-iteration fuzz suite, and ASan/UBSan Makefile target.
- `eshkol/` — Runnable Eshkol v1.3.6 forward-mode dual-number AD modules (`.esk`) and Node.js runner.
- `python/triad_verify/` — Exact finite-field rank verifier, 12-variable polymatroid + $I_4$/5-obj/6-obj $\mathbb{F}_2^{64}$ realizability verifier, 60-digit `Decimal` ML-KEM `Dyadic-256`/`512`/`1024`/`16384-A/B` & Bai optimizer + zero-trimmed exact FIPS 203 DFR convolution suite (Gaussian DFR Paradox), Koszul/Strassen/Brockett–Dobkin/Schwartz–Zippel/Paley verifier, and 8-figure vector PDF generator (strict 0 `ruff` / 0 `mypy`).
- `paper/` & `dist/` — AMS-LaTeX preprint (`main.tex`, `refs.bib`, 8 vector PDF figures, 36 live HTTP-200 citations), frozen PDF, clean-room verified `arxiv_submission.tar.gz`, and RFC 3161 TSA timestamp (`data/MANIFEST.sha256.tsr`).
- `docs/site/` — Self-contained interactive GitHub Pages 31-theorem Proof Blueprint DAG & live PIR/MLWE/Bai/DFR/QGTL explorer.
- `docs/` — Architecture, ADRs, statement fidelity, 10-pass review, adversarial red-team review, threat model, operations, FAQ, glossary, and run log.

---

## Citation & License

- **Code, Lean 4 proofs, scripts, and build tooling:** [`Apache-2.0`](LICENSE)
- **White paper, figures, documentation, and verified data tables:** [`CC-BY-4.0`](LICENSE-DOCS)
- Machine-readable citation metadata: [`CITATION.cff`](CITATION.cff)
