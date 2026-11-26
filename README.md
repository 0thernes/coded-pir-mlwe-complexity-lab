# `coded-pir-mlwe-complexity-lab`

[![License: Apache-2.0](https://img.shields.io/badge/Code%20License-Apache--2.0-blue.svg)](LICENSE)
[![Docs License: CC-BY-4.0](https://img.shields.io/badge/Docs%20%26%20Paper-CC--BY--4.0-lightgrey.svg)](LICENSE-DOCS)
[![Project Status: Active](https://www.repostatus.org/badges/latest/active.svg)](https://www.repostatus.org/#active)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0%20Zero--Mathlib%20(31%20Theorems)-purple.svg)](lean/lean-toolchain)
[![CI](https://github.com/0thernes/coded-pir-mlwe-complexity-lab/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/coded-pir-mlwe-complexity-lab/actions/workflows/ci.yml)
[![Pages](https://img.shields.io/badge/Interactive-Proof%20Blueprint-0284c7.svg)](https://0thernes.github.io/coded-pir-mlwe-complexity-lab/)

Zero-Mathlib **Lean 4.35.0** proofs (31 theorems `T1a`–`T3l` plus 7 adversarial tests, 34 audited declarations, replayed by 6 proof kernels in CI; 4,300 declarations checked by `con-leche`/`con-ron` on the standalone `Solution` export), cross-checks in C11 (79/79 tests), Python 3.12 and Eshkol v1.3.6 dual-number AD, an interactive Proof Blueprint, and an AMS-LaTeX preprint (`v5.0.0`).

**What this repository is.** A suite of elementary algebraic identities, finite certificates and formalisations of classical results, used as building blocks in three areas: coded and Byzantine private information retrieval (`CS-053`), noise analysis for Module-LWE and FIPS 203 ML-KEM (`CS-026`/`QC-042`/`CM-048`), and tensor rank, Schwartz–Zippel and zero-error graph capacity (`CS-001`/`CS-004`/`CS-010`/`CS-012`/`CS-051`/`CS-CMP-012`). It resolves no published open problem in Lean and refutes no published claim. Scheme rates, divergence values and decryption-failure rates are numerical results outside Lean. The classical formalisations (rank of the 2×2 matrix-multiplication tensor is 7 over every field, Schwartz–Zippel, the integer form of $\Theta(C_5)=\sqrt{5}$) are known results. An independent statement audit (2026-11-26) is recorded in [ERRATA.md](ERRATA.md) and in the [archive audit log](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md).

![Project Social Preview](docs/media/social-preview.svg)

**Author:** Alexander S. Donahue (Independent Researcher, Spokane, WA, USA; ORCID [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648))  
**Status:** active (`repostatus.org/#active`) · Research preprint `v5.0.0` (not externally peer-reviewed; AI-assisted under human direction; see [LIMITATIONS.md](LIMITATIONS.md) & [ERRATA.md](ERRATA.md))  
**Interactive Proof Blueprint:** [`https://0thernes.github.io/coded-pir-mlwe-complexity-lab/`](https://0thernes.github.io/coded-pir-mlwe-complexity-lab/) ([DAG Blueprint](https://0thernes.github.io/coded-pir-mlwe-complexity-lab/blueprint.html))  
**White Paper PDF:** [`dist/Donahue_2026_coded_pir_mlwe_complexity_frontier.pdf`](dist/Donahue_2026_coded_pir_mlwe_complexity_frontier.pdf) · **arXiv Source Tarball:** [`dist/arxiv_submission.tar.gz`](dist/arxiv_submission.tar.gz)

---

## Results (`T1a`–`T3l`): What Lean Proves and What It Does Not

Every theorem below is proved in zero-Mathlib Lean 4.35.0 with no `sorry`, no `native_decide` and no custom axioms. The second column states the Lean content in plain terms. The third column lists what is outside Lean: numerical computations (Python, C11, Eshkol), readings given only in prose or in identifier names, and prior work. Kernel agreement across six checkers certifies the proofs; it does not certify that the Lean definitions model the PIR, lattice or cryptographic objects their names refer to. `lean/TriadFrontier/NonVacuity.lean` gives spot-check witnesses for selected hypotheses, not for every hypothesis bundle. Of the 7 adversarial tests in `lean/TriadFrontier/AdversarialTests.lean`, two are closed arithmetic facts and one encodes a `Compress_1` value that disagrees with FIPS 203 (see [ERRATA.md](ERRATA.md)).

| ID | What the Lean statement says | Outside Lean, readings and prior work | Lean entry point |
|---|---|---|---|
| **T1a** | Over any commutative ring, the moment vector $(1,a,\dots,a^{T-1})$ is orthogonal to $e_{r+1}-a\,e_r$ for $r+1<T$; the binomial identity $K\binom{T}{T'} = (K+T-T')\binom{T-1}{T'-1} + (K-T')\binom{T-1}{T'}$; and the numeral facts $3\cdot5+3\cdot8+3=42$, $60\cdot7>4\cdot102$, $10\cdot102=17\cdot60$. | Numerical (not machine-checked) rank computations over $\mathbb{F}_7$ and $\mathbb{F}_{101}$ give interference dimension 42 and rate $10/17$ for one GRS-aligned design at $(N,K,T)=(6,3,3)$, against $4/7$ in Sun, Tao, Xu and Zhang (`arXiv:2603.10769`, Sec. VII, Example VII-A). Privacy and zero-error decoding of this design are not verified. That source asks how to design the queried vectors for maximum redundancy; this repository does not answer that question, and optimality over designs is not addressed. The general min-formula rests on a prose sketch in the paper. | `TriadFrontier.Solution.t1a_koszul_veronese_rank_identity` |
| **T1b** | For naturals $E\ge1$, $K,T\ge2$: $E^2(E^2+(K+T-2)E-KT) < E^2(E-1)(E+K+T-1)$, with difference $(K-1)(T-1)E^2$; the first denominator is symmetric in $K$ and $T$; a multi-file analogue for $1\le P<M$; two specialisations. | Lean compares two closed-form expressions. That a scheme attains the first expression for $T\ge3$ is a paper claim, not in Lean. The second expression is the Sun–Zhang capacity (`arXiv:2610.37412`) only for linear, full-support-rank schemes with $N-U-2B\ge KT$, so exceeding it is meaningful only for that class. At $T=2$ the first expression is the rate of Theorem IV.4 of `arXiv:2603.10769`, and Remark IV.5 there already states that it exceeds $N/(N+K+1)$. | `TriadFrontier.Solution.t1b_universal_koszul_domination_over_lfsr` |
| **T1c** | An arithmetic (double-counting) implication; for $K\ge2$, $K+1<2K$ and an identity for the rate denominator at $E=K+1$; a Boolean checker confirms that 90 tabulated $\mathbb{F}_{11}$ matrices have the tabulated inverses; $42>40$. | That these matrices form a zero-error Byzantine rate-$2/5$ PIR scheme, and the capacity match at $E=K+1$, are readings in comments and the paper. Privacy, robustness, decodability and rate are not defined in Lean, and no converse bound is proved in Lean. | `TriadFrontier.Solution.t1c_byzantine_robust_capacity_and_f11_certificate` |
| **T1d** | Three threshold statements over `Nat`: $(3E-4)+E\le E(E-1)$ iff $E\ge4$ (truncated subtraction at $E=1$); for $K\ge1$, $E\ge K+1$: $(K+1)\mu\le E\mu$, with equality iff $\mu=0$ or $E=K+1$; for $E\ge3$: $(4E-6)+2E\le E(E-1)$ iff $E\ge6$. | Their reading as flag-privacy dimension counts is prose; flag privacy is not defined in Lean. | `TriadFrontier.Solution.t1d_flag_privacy_and_feasibility_dimensions` |
| **T1e** | Boolean checks are true for a tabulated integer set function `h_uncond` on 12 elements (scale 128): monotonicity, submodularity on 330 orbit representatives, a fixed list of 99 equalities, and 1,485 singleton Ingleton instances; $4\cdot h(256)\cdot 8 = 13\cdot128$ (value ratio $8/13$). | That the 330 representatives cover all 67,584 elemental submodularity inequalities ($\binom{12}{2}\cdot2^{10}$, plus 12 monotonicity) uses the permutation invariance of `h_uncond`, a meta-argument checked in Python, not a Lean theorem. That the 99 equalities encode every constraint of the $(2,4,2,2)$ PIR problem is not proved against a formal model. Ingleton is checked on singleton 4-tuples only. | `TriadFrontier.Solution.t1e_unconditioned_shannon_ingleton_barrier` |
| **T1f** | Over any field $F$: if four 2-dimensional spans in $F^4$ pairwise share a nonzero vector, then either one nonzero vector lies in all four, or all four lie in the span of three vectors. | The classical fact that pairwise-meeting lines in projective 3-space are concurrent or coplanar. The PIR reading ("linear impossibility") is prose. | `TriadFrontier.Solution.t1f_projective_p3_linear_impossibility` |
| **T1g** | For any $H:\mathbb{N}\to\mathbb{Z}$, the Zhang–Yeung (1998) expression satisfies $\mathrm{ZY}(a,b;c,d)=\mathrm{Ing}(c,d;a,b)+I(a;c\mid d)+I(a;d\mid c)+I(c;d\mid a)$, hence is non-negative when the four terms are; a multi-file denominator is $K$–$T$ symmetric, equals the `T1b` denominator at $M=2$, and is positive at $E=K+1$. | No $M$-file scheme is defined in Lean. That `h_uncond` satisfies Zhang–Yeung follows only where Ingleton was checked (singleton 4-tuples). | `TriadFrontier.Solution.t1g_zhang_yeung_reduction_and_mfile_koszul` |
| **T1h** | A non-negative integer combination of an Ingleton term and six conditional mutual-information terms is non-negative when each term is; `matusFamilyQ s` equals the Zhang–Yeung expression at $s=1$ and is such a combination for every $s$; a strict inequality between $j$-th powers of two integer expressions. | That `matusFamilyQ` is the Matúš (2007) family is by definition in this repository and is not compared with the source in Lean. Satisfaction on `h_uncond` follows only for the checked singleton instances. | `TriadFrontier.Solution.t1h_infinite_nonshannon_cone_barrier_and_contraction` |
| **T1i** | Any integer functional non-negative on 23 listed outputs of the repository's mod-$p$ rank routine `matRankModP` is non-negative on 24 canonical 4-profiles; Boolean checks show these profiles cover the 495 singleton and 15 retrieval-object 4-marginals of `h_uncond`, and that the six 5-object retrieval marginals decompose into outputs of the same routine. | No Lean theorem shows that `matRankModP` computes linear-algebraic rank; it is cross-checked in C and Python. Entropy is not defined in Lean. The coverage is 4-tuples of single variables and of the six retrieval objects, not every 4-variable linear inequality on arbitrary groupings. | `TriadFrontier.Solution.t1i_total_4var_entropic_and_5obj_linear_barrier` |
| **T1j** | For masks 1..63, the 6-object retrieval marginal of `h_uncond` equals 4 times the output of a sparse GF(2) rank routine `gf2RankSparse` on one explicit arrangement in $\mathbb{F}_2^{64}$; hence any functional non-negative on all outputs of that routine is non-negative on this marginal. | No Lean theorem shows that `gf2RankSparse` computes span dimension; it is cross-checked in C and Python. With the routine assumed correct and the standard fact that linear rank functions are entropic (both outside Lean), no information inequality on these six retrieval objects alone separates `h_uncond`. Inequalities in 5 or more variables that involve individual storage symbols are not excluded. | `TriadFrontier.Solution.t1j_total_6obj_f2_entropic_realizability_barrier` |
| **T2a** | In any commutative ring, the product of the first $m+k$ (and $m+k+1$) values of $i\mapsto(q \text{ if } i<m \text{ else } 1)$ equals $q^m$; and $u^{-1}(u\,q^m)=q^m$ when $u\,u^{-1}=1$. No matrix, lattice or determinant function is defined. | Records that the $q$-ary MLWE basis has determinant $q^m$ (elementary). No published claim is refuted. `arXiv:2604.15858` (Luo, Part I) verifies Weber's class-number conjecture for $k\le12$ and contains no determinant-ideal argument; the determinant-ideal step appears in Part IV (`arXiv:2605.17412`), which this repository does not formalise. | `TriadFrontier.Solution.t2a_determinant_ideal_secret_independence` |
| **T2b** | In any commutative ring, if $w^D=-1$ and $f(D+x)=-f(x)$ for $x<D$, then $\sum_{x<2D} f(x)\,w^{2kx}=0$; for odd $c$ and $D$, $c(x+D)^2 = cx^2 + D\,c(2x+D)$ with $c(2x+D)$ odd. | A DFT identity that the author proposes as an explanation of the Step 9 failure in Chen (IACR ePrint 2024/555); nothing from that preprint is formalised. The Step 9 bug was found by Hongxun Wu and, independently, Thomas Vidick, as stated in the author's note on the ePrint page. | `TriadFrontier.Solution.t2b_chen_step9_antiperiodic_dft_cancellation` |
| **T2c** | Moment sums of the weight tables $(1,4,6,4,1)$ and $(1,6,15,20,15,6,1)$ ($\mathrm{CBD}_2$, $\mathrm{CBD}_3$); in a field, $z^n=-1$ and $z^{2k}\ne1$ give $\sum_{j<n} z^{2kj}=0$; three comparisons between hard-coded integers. | No Rényi divergence is defined in Lean. The $4.96\times$ Rényi-2 ratio and the 37.84 / 7.63 bit figures are 60-digit Python computations that enter Lean only as numerals. | `TriadFrontier.Solution.t2c_mlkem_cbd_renyi_cliff` |
| **T2d** | Covariance-numerator identities for integer weight tables: shifting $(x-e_0)^2$ by a constant leaves the covariance unchanged; for symmetric weights on $\{-M,\dots,M\}$, $\mathrm{cov}(x,x^2)=0$; for weights $(1,4,6,4,1)$ and shift 1 the numerator is $-512$. | "Berry curvature" and "quantum geometric tensor" are names attached in prose; no quantum state or curvature is defined in Lean. | `TriadFrontier.Solution.t2d_qgtl_shifted_lwe_berry_curvature` |
| **T2e** | If $w_iq_i=M$, $w_i\ge0$, $M>0$, then $M(\sum p)^2\le(\sum q)(\sum p^2w)$ (an integer Cauchy–Schwarz form); the table $(1,14,63,100,63,14,1)$ sums to 256 with second moment 256 and fourth moment 736; $\mathrm{cov}^2\le\mathrm{var}\cdot\mathrm{var}$ for non-negative weights; three numeral comparisons. | The $17.7\times$ reduction to 2.14 bits is a Python computation. "Optimal" and "constant-time" are not Lean content; the sampler is C code with branchless masks. | `TriadFrontier.Solution.t2e_dyadic256_renyi_floor_and_qgtl_psd` |
| **T2f** | In any commutative ring: if $w^D=z$, $f(qD+x)=z^{qr}f(x)$ for $q<m$, $x<D$, and $\sum_{q<m} z^{q(r+k)}=0$, then $\sum_{x<mD} f(x)\,w^{kx}=0$. | Elementary factorisation of a finite sum. | `TriadFrontier.Solution.t2f_universal_twisted_dft_selection_rule` |
| **T2g** | A cleared-denominator inequality bounding $MQ(QS_{\varphi p}-PS_{\varphi q})^2$ by a weighted variance of $\varphi$ times $(Q\sum p^2w-MP^2)$; the table $(1,8,44,120,166,120,44,8,1)$ sums to 512 with second moment 768 and fourth moment 3456; numeral comparisons. | The Hermite-4 and QGTL readings, the $12.9\times$ figure and "constant-time" are not Lean content. DFR values come from the float64 model described under `T2i`. | `TriadFrontier.Solution.t2g_qgtl_renyi_variational_bridge_and_dyadic512` |
| **T2h** | For naturals with $w_iq_i=M$: $M^m(\sum p)^{m+1}\le(\sum q)^m\sum p^{m+1}w^m$; $M(\sum\lvert Qp_i-Pq_i\rvert)^2\le Q^2(Q\sum p^2w-MP^2)$; moment sums of two tables summing to 1024; numeral comparisons. | The Bai et al. (2018) overhead figures ($67.14\to7.31$ bits, $9.19\times$; $24.77\to5.13$ bits, $4.83\times$) are Python computations that enter Lean only as numerals. DFR values come from the float64 model described under `T2i`. | `TriadFrontier.Solution.t2h_all_order_renyi_holder_tv_and_dyadic1024` |
| **T2i** | Cleared-denominator forms of: a $\chi^2$-type sum grows by at most a factor $D$ under a kernel with column sums $D$; exact multiplicativity of $\sum p^{r+1}w^r$ over $m$-fold products; a bound from $p_iD\le R_{\max}q_i$; moment sums of two tables summing to 16384; numeral comparisons. | Decryption-failure rates come from a float64 numpy convolution model (`python/triad_verify/mlwe_tightness.py`), not an exact computation. In that model a unit-variance discrete Gaussian gives DFR about $2^{-173.4}$ for ML-KEM-1024, `Dyadic-16384-A` about $2^{-174.0}$, and the standard $\mathrm{CBD}$ noise about $2^{-176.6}$; FIPS 203 Table 1 lists $2^{-174.8}$ for the standard parameters. FIPS 203 states no $2^{-174}$ pass/fail threshold, so the earlier "Gaussian DFR paradox" and "FAIL/PASS" wording is withdrawn. The $11.17\times$ and $41.9\times$ Bai figures are Python computations. | `TriadFrontier.Solution.t2i_bai_engine_dpi_tensorization_and_dyadic16384` |
| **T3a** | Over any field, for $f:\{0,1\}^n\to F$, the recursively defined multilinear extension is multilinear, agrees with $f$ on Boolean points, and every multilinear $g$ agreeing with $f$ there equals it everywhere. | A standard fact. "Algebrization" is context; no oracle or complexity class is defined. | `TriadFrontier.Solution.t3a_algebrization_multilinear_extension_uniqueness` |
| **T3b** | For naturals with $A_{\mathrm{prf}}=0$, $A_{\mathrm{rand}}\cdot den\ge U\cdot num$ and $\varepsilon_{num}\cdot den\le num\cdot\varepsilon_{den}$: $K A_{\mathrm{rand}}\,den\ge K U\,num$ and not $(K A_{\mathrm{rand}}\,\varepsilon_{den}<K U\,\varepsilon_{num})$. This is the counting inequality of the natural-proofs argument (Razborov–Rudich). | No pseudorandom function, LWE instance, circuit class or natural property is defined in Lean. | `TriadFrontier.Solution.t3b_lwe_to_natural_proofs_obstruction` |
| **T3c** | If all codewords have length $N$ and a decoder returns $m$ for every word within Hamming distance $B$ of $\mathrm{Enc}(m)$, then distinct messages have codewords at distance $\ge 2B+1$. | A $B$-error-correcting code has minimum distance $\ge 2B+1$. No locality, queries or PIR are defined; the Katz–Trevisan and Byzantine-PIR names are context. | `TriadFrontier.Solution.t3c_katz_trevisan_byzantine_pir_ldc_distance` |
| **T3d** | For $x\mapsto\lfloor(2(x \bmod 3329)+1665)/3329\rfloor \bmod 2$: the value at $1665b+e$ is $b$ for $b\in\{0,1\}$, $\lvert e\rvert\le831$; the value at 832 is 1 and at 2497 is 0; and $\lfloor 831/b_{\mathrm{step}}\rfloor<M$ implies $832\le M\,b_{\mathrm{step}}$. | This function differs from FIPS 203 $\mathrm{Compress}_1$ (eq. 4.7, rounding over the rationals) at exactly one point, $x=832$, where the standard gives 0. The $\lvert e\rvert\le831$ guarantee also holds for the standard. For the standard the exact margins are $\lvert e\rvert\le832$ for $b=0$ and $-832\le e\le831$ for $b=1$, so failure at $e=+832$ holds for $b=1$ only. See ERRATA. | `TriadFrontier.Solution.t3d_mlwe_single_server_pir_noise_ceiling` |
| **T3e** | Over any field: every rank-$r$ decomposition of the $2\times2$ matrix-multiplication tensor has $r\ge6$; every rank-$r$ decomposition of a fixed $3\times3\times3$ 0/1 tensor has $r\ge5$. | Known; the first bound is superseded by `T3h`. The link to PIR is an interpretation. | `TriadFrontier.Solution.t3e_koszul_flattening_tensor_rank_bridge` |
| **T3f** | If $C<M$, every map $\mathrm{Fin}\,C\to\mathrm{Fin}\,M$ misses a value; if $\sum_i \mathrm{cnt}(i)\le qS$ and heavy indices have $\mathrm{cnt}\ge\tau$, then $\#\text{heavy}\cdot\tau\le qS$. | Pigeonhole and Markov-type counting; no circuits or codes are defined. | `TriadFrontier.Solution.t3f_shannon_counting_and_ldc_smoothness` |
| **T3g** | Over any field and $m\ge2$, every rank-$r$ decomposition of $\langle m,m,m\rangle$ has $r\ge m^2+2$; and $(m^2-m+1)(m^2+m-1)<m^4$. | Weaker than `T3i` and than published bounds. | `TriadFrontier.Solution.t3g_all_m_koszul_matmul_lower_bound` |
| **T3h** | Over every field, the $2\times2$ matrix-multiplication tensor has a decomposition into 7 rank-one terms, and every decomposition into $r$ rank-one terms has $r\ge7$. | A formalisation of a known result: the upper bound is Strassen's algorithm (1969); the lower bound is classical (Brockett and Dobkin, 1978, give $2n^2-1$ over any field, which is 7 at $n=2$, as reported by Shpilka, `arXiv:cs/0201001`). | `TriadFrontier.Solution.t3h_strassen_winograd_exact_rank_seven` |
| **T3i** | Over any field and $m,k,p\ge1$: every rank-$r$ decomposition of $\langle m,k,p\rangle$ has $r\ge mk+mp-m$, $mk+kp-k$ and $mp+kp-p$; in the square case $r\ge2m^2-m$; for $m,p\ge2$, $\langle m,2,p\rangle$ needs $r\ge mp+3$. | A substitution-method bound, weaker for $m\ge2$ than the bound $2m^2-1$ that Brockett and Dobkin (1978) proved over any field, and than Bläser's $2.5m^2-3m$ (both as reported by Shpilka, `arXiv:cs/0201001`). | `TriadFrontier.Solution.t3i_brockett_dobkin_rectangular_and_quadratic_matmul_bound` |
| **T3j** | Over any field and for any graph, a rank-$r$ fitting matrix bounds independent sets of the $t$-th strong power by $r^t$. For $C_5$: independent sets of size $k$ in the $t$-th power satisfy $k^2\le5^t$, and size $5^m$ exists in power $2m$. For $C_7$: size $10^m$ exists in power $2m$; fitting matrices need rank $\ge4$, and rank 4 is attained. | The $C_5$ statements are the integer form of $\Theta(C_5)=\sqrt5$ (Lovász, 1979); the rank bound is Haemers (1979). Shannon capacity itself is not defined in Lean. $\Theta(C_7)$ is not determined. | `TriadFrontier.Solution.t3j_shannon_capacity_lovasz_c5_and_haemers` |
| **T3k** | Over any field: a nonzero $n$-variate polynomial of total degree $\le d$ has at most $d\lvert S\rvert^{n-1}$ roots on $S^n$, and a non-root when $d<\lvert S\rvert$; a transpose symmetry of matrix-multiplication rank; and the two-sided bound $2\cdot4^k-2^k\le\mathrm{rank}(\langle 2^k,2^k,2^k\rangle)\le7^k$. | Schwartz–Zippel is a known result. The two-sided bound is two one-sided bounds (Strassen's recursion and `T3i` at $m=2^k$), not an exact value. | `TriadFrontier.Solution.t3k_schwartz_zippel_and_strassen_sandwich` |
| **T3l** | For every graph on $4k+1$ vertices that satisfies the conference-graph equations, independent sets of size $s$ in its $t$-th strong power satisfy $s^2\le(4k+1)^t$; for every graph with a complement-swapping bijection, an independent set of size $n^m$ exists in its $2m$-th strong power. Both hypotheses are proved in Lean for $P_5=C_5$, $P_{13}$ and $P_{17}$. | A conditional theorem. There is no Lean theorem that every Paley graph satisfies the hypotheses, and conference graphs do not exist for every $k$, so the result holds for every self-complementary conference graph on $4k+1$ vertices, not "for every $k$". Capacity $\sqrt n$ for self-complementary vertex-transitive graphs, which covers Paley graphs, is Lovász (1979). Checks for further Paley graphs up to $P_{41}$ are numerical (C11, Python). | `TriadFrontier.Solution.t3l_infinite_paley_conference_shannon_capacity` |

### Prior Work and Attribution

- Sun, Tao, Xu and Zhang, *A Disguise-and-Squeeze PIR Scheme for the MDS-TPIR Setting and Beyond* (`arXiv:2603.10769`): source of the $4/7$ benchmark (Example VII-A), of the maximum-redundancy design question (Sec. VII-B.2) and of the $T=2$ rate that `T1b` reproduces (Theorem IV.4, Remark IV.5). It lists zero-error schemes for $T\ge3$ as open (Sec. VIII). Its wording never uses "syzygy"; "Schur-product syzygy rank" is this repository's own name.
- Sun and Zhang (`arXiv:2610.37412`): capacity among linear, full-support-rank schemes when $N-U-2B\ge KT$.
- Luo, *Module Lattice Security (Part I): Unconditional Verification of Weber's Conjecture for k ≤ 12* (`arXiv:2604.15858`): contains no determinant-ideal claim. The determinant-ideal step is in Part IV (`arXiv:2605.17412`).
- Chen, *Quantum Algorithms for Lattice Problems* (IACR ePrint 2024/555): the Step 9 bug was found by Hongxun Wu and, independently, Thomas Vidick (author's note on the ePrint page).
- Brockett and Dobkin (1978) proved $2n^2-1$ for $n\times n$ matrix multiplication over any field; Bläser later proved $2.5n^2-3n$ (both as reported by Shpilka, `arXiv:cs/0201001`).
- Lovász (1979), *On the Shannon capacity of a graph*: $\Theta(C_5)=\sqrt5$ and capacity $\sqrt n$ for self-complementary vertex-transitive graphs on $n$ vertices.

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

Clone and run the four layers (Lean 4.35.0, C11, Eshkol dual-number AD, and Python + pytest):

```bash
git clone https://github.com/0thernes/coded-pir-mlwe-complexity-lab.git
cd coded-pir-mlwe-complexity-lab

# 1. Zero-Mathlib Lean 4.35.0 proofs + axiom & kernel audit (31 theorems + 7 adversarial tests)
(cd lean && lake build && lake env lean VerifyAxioms.lean && lake env leanchecker Solution && lake env leanchecker-paranoid Solution)

# 2. Native C11 core (-std=c11 -Wall -Wextra -Wpedantic -Werror, 79/79 tests + 512+ fuzz)
make -C native clean test

# 3. Eshkol v1.3.6 forward-mode dual-number AD modules (3/3, incl. Dyadic-256/512/1024/16384-A/B)
node eshkol/run_eshkol_ad.mjs

# 4. Python verification suite, differential/mutation tests, lint, axiom drift & citations
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

# Python verification modules
PYTHONPATH=python python python/triad_verify/pir_koszul.py
PYTHONPATH=python python python/triad_verify/polymatroid_barrier.py
PYTHONPATH=python python python/triad_verify/mlwe_tightness.py
PYTHONPATH=python python python/triad_verify/complexity_triad.py
```

See [`examples/README.md`](examples/README.md) for annotated outputs and [`REPLICATION.md`](REPLICATION.md) for the clean-room replication protocol.

---

## Honest Scope & Explicit Non-Claims

This work resolves no published open problem in Lean and refutes no published claim. The following remain **open**:
1. **$\mathrm{P} \neq \mathrm{NP}$ and super-linear explicit Boolean circuit lower bounds (`CS-001` / `CS-010`).** `T3a`, `T3b` and `T3f` formalise multilinear-extension uniqueness, the counting inequality of the natural-proofs argument, and pigeonhole counting; no complexity class, circuit or pseudorandom function is defined in Lean.
2. **Matrix multiplication exponent $\omega = 2$ (`CS-004`) and Valiant's $\mathrm{VP} \neq \mathrm{VNP}$ (`CS-012`).** `T3e`, `T3g`, `T3h`, `T3i` and `T3k` give characteristic-free tensor-rank bounds ($\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$; $\mathrm{rank}_F(\langle m,m,m\rangle) \ge 2m^2 - m$, weaker than the published $2m^2-1$; the two-sided bound $2\cdot 4^k - 2^k \le \mathrm{rank}_F(\langle 2^k,2^k,2^k\rangle) \le 7^k$), not asymptotic $\omega$ or $\mathrm{VP} \neq \mathrm{VNP}$.
3. **$C(2,4,2,2) \in [3/5, 8/13]$ and general $M \ge 3$ coded-colluding PIR when $E \ge KT$ (`CS-053`).** With the rank routines assumed correct, `T1e`, `T1i` and `T1j` show that no information inequality on (a) any 4 single variables, (b) any 5 of the retrieval objects, or (c) the 6 retrieval objects `{W1, W2, A1..A4}` separates `h_uncond`. Inequalities in 5 or more variables that involve individual storage symbols are not excluded.
4. **The Sun–Tao–Xu–Zhang maximum-redundancy design question and zero-error schemes for $T \ge 3$ (`arXiv:2603.10769`, Sec. VII-B.2 and Sec. VIII).** The $(6,3,3)$ design behind the rate $10/17$ is not verified to be private or zero-error.
5. **Exact Shannon capacity $\Theta(C_7) \in [\sqrt{10}, \vartheta(C_7) \approx 3.317667]$ (`CS-CMP-012`).** `T3j` gives the integer form of $\Theta(C_5)=\sqrt5$ and minimum fitting-matrix rank 4 for $C_7$. `T3l` gives, for every self-complementary conference graph on $4k+1$ vertices, $\alpha(G^{\boxtimes t})^2 \le (4k+1)^t$ and $\alpha(G^{\boxtimes 2m}) \ge (4k+1)^m$, with the hypotheses checked in Lean for $P_5$, $P_{13}$ and $P_{17}$; the general capacity result is Lovász (1979).
6. **Worst-case quantum hardness of MLWE (`CS-026` / `QC-042`).** `T2a`–`T2i` are ring identities, integer inequalities and moment tables; Rényi values, Bai overheads and DFRs are numerical (float64 for DFRs). None of this bears on the hardness of MLWE.

Boundaries, notes on Tsotchke-inspired components, errata and falsification tests are in [`CLAIMS.md`](CLAIMS.md), [`LIMITATIONS.md`](LIMITATIONS.md), [`ERRATA.md`](ERRATA.md), and [`docs/statement-fidelity.md`](docs/statement-fidelity.md).

---

## Repository Map

- `lean/` — Zero-Mathlib Lean 4.35.0 proof library (`TriadFrontier/*` incl. `PIRLinearCerts.lean`, `KoszulTensor.lean`, `StrassenWinograd.lean`, `BrockettDobkin.lean`, `ShannonCapacity.lean`, `AlgebraicComplexity.lean`, `PaleyCapacity.lean`, `AdversarialTests.lean`), Palomar comparator contract (`PalomarChallenge.lean`, `PalomarSolution.lean`, `comparator.json`), `VerifyAxioms.lean` (34 decls), and `formalization.yaml`.
- `native/` — Zero-warning C11 library (incl. branchless `Dyadic-256`/`512`/`1024`/`16384-A/B` samplers, not verified constant-time at the binary level; $\mathbb{F}_2^{64}$ 6-obj realization, $m$-twisted DFT, Koszul flattening, Strassen 7-product, all-$m$ monomial, and exact $\mathbb{Z}[\sqrt{p}]$ Paley/conference SOS certs for $P_5..P_{41}$), CLI, 79-test unit + 512-iteration fuzz suite, and ASan/UBSan Makefile target.
- `eshkol/` — Runnable Eshkol v1.3.6 forward-mode dual-number AD modules (`.esk`) and Node.js runner.
- `python/triad_verify/` — Finite-field rank verifier, 12-variable polymatroid and 4-/5-/6-object $\mathbb{F}_2$ realisability checks, 60-digit `Decimal` Rényi and Bai computations for `Dyadic-256`/`512`/`1024`/`16384-A/B`, a float64 FIPS 203 DFR convolution model, Koszul/Strassen/Brockett–Dobkin/Schwartz–Zippel/Paley verifier, and 8-figure vector PDF generator (strict 0 `ruff` / 0 `mypy`).
- `paper/` & `dist/` — AMS-LaTeX preprint (`main.tex`, `refs.bib`, 8 vector PDF figures, 36 live HTTP-200 citations), frozen PDF, clean-room verified `arxiv_submission.tar.gz`, and RFC 3161 TSA timestamp (`data/MANIFEST.sha256.tsr`).
- `docs/site/` — Self-contained interactive GitHub Pages 31-theorem Proof Blueprint DAG & live PIR/MLWE/Bai/DFR/QGTL explorer.
- `docs/` — Architecture, ADRs, statement fidelity, 10-pass review, adversarial red-team review, threat model, operations, FAQ, glossary, and run log.

---

## Citation & License

- **Code, Lean 4 proofs, scripts, and build tooling:** [`Apache-2.0`](LICENSE)
- **White paper, figures, documentation, and verified data tables:** [`CC-BY-4.0`](LICENSE-DOCS)
- Machine-readable citation metadata: [`CITATION.cff`](CITATION.cff)
