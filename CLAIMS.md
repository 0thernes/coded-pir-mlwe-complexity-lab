<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Claims Ledger & Falsification Protocol (`CLAIMS.md`)

Every mathematical and computational claim in `coded-pir-mlwe-complexity-lab` (`v2.0.0`) is assigned a unique ID, an explicit verification tier, exact artifact paths, and a concrete falsification test ("what would prove us wrong").

## Verification Tiers

- **Tier 1 (Machine-Checked Formal Proof):** Zero-Mathlib Lean 4.35.0 proof depending strictly on a subset of `[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero `native_decide`, independently replayed across all six Lean 4.35.0 kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche --verified` 2,418 decls, `con-ron --verified` 2,418 decls).
- **Tier 2 (Exact / Arbitrary-Precision Computation):** Deterministic integer, rational, finite-field, or 60-digit `Decimal` computation cross-checked differentially across Python, C11, and Eshkol v1.3.6 dual-number AD.
- **Open (Explicitly Unproved):** Conjectures and open frontiers intentionally separated from claimed results.

## Verified Claims (`C1`–`C19`)

| ID | Pillar | Statement Summary | Tier | Formal / Code Artifacts | Falsifying Condition ("What Would Prove Us Wrong") |
|---|---|---|---|---|---|
| **C1** | `CS-053` | Exterior-power Koszul–Veronese moment annihilation $\langle u(\alpha), e_{r+1}-\alpha e_r\rangle = 0$ over any `CommRing`, Pascal interference savings $K\binom{T}{T'} = \lambda^\star + (K-T')\binom{T-1}{T'}$, and flagship $(6,3,3)$ rate $10/17 > 4/7$ (valid over $\mathbb{F}_7$) | Tier 1 + Tier 2 | `lean/TriadFrontier/PIRKoszul.lean` (`t1a`), `python/triad_verify/pir_koszul.py`, `native/src/triad_core.c` | Any `CommRing` counterexample where $\langle u(\alpha), e_{r+1}-\alpha e_r\rangle \neq 0$, any $(T,T',K)$ violating Pascal savings, or any rank deficit in the 46 Koszul blocks at $(6,3,3)$ |
| **C2** | `CS-053` | Exact $K \leftrightarrow T$ symmetry and universal strict domination $R_{\mathrm{KV}} > R_{\mathrm{LFSR}}$ for all $K \ge 2, T \ge 2, E \ge 2$ in single-file and multi-file $P$-out-of-$M$ regimes via surplus $(K-1)(T-1)E^2 > 0$ | Tier 1 + Tier 2 | `lean/TriadFrontier/PIRKoszul.lean` (`t1b`), `eshkol/koszul_pir_ad.esk`, `tests/test_all.py` | Any integer tuple $(P,M,E,K,T)$ with $1 \le P < M, E,K,T \ge 2$ where $R_{\mathrm{KV}} \le R_{\mathrm{LFSR}}$ |
| **C3** | `CS-053` | Non-vacuous Byzantine-robust double-counting converse reduction; exact $E=K+1$ match to Sun–Jafar unrestricted capacity (breaking $E \ge KT$); kernel-certified zero-error $\mathbb{F}_{11}$ Byzantine rate-$2/5$ scheme at $(M=2,N=6,K=2,T=2,B=1,E=4)$ | Tier 1 + Tier 2 | `lean/TriadFrontier/PIRCertificates.lean`, `lean/TriadFrontier/PIRKoszul.lean` (`t1c`), `data/f11_byz_witness.json`, `native/src/triad_core.c` | Any of the 15 desired $12 \times 12$ matrices, 15 interference $8 \times 8$ matrices, or 60 flag-privacy $5 \times 5$ matrices over $\mathbb{F}_{11}$ failing full rank |
| **C4** | `CS-053` | Exact flag-privacy dimension thresholds ($K=2,T=2 \iff E \ge 4$; zero-error $T=3,K=2 \iff E \ge 6$) and universal overlap feasibility $E w \le K\delta\sigma$ (equality iff $E=K+1$) | Tier 1 + Tier 2 | `lean/TriadFrontier/PIRKoszul.lean` (`t1d`), `python/triad_verify/pir_koszul.py` | Any valid flag-private basis violating $(3E-4)+E \le E(E-1) \iff E \ge 4$ or $E w \le K\delta\sigma$ |
| **C5** | `CS-053` | Pure-integer scale-128 12-variable polymatroid `h_uncond` satisfies all 12 monotonicity inequalities, all 270,336 elemental Shannon submodularity inequalities (via 330 $S_4$ orbits + direct full enumeration of 67,584 triples), all 99 PIR equalities, all 1,485 singleton Ingletons, and 3,814,209 6-atom Ingletons at $C = 8/13 > 3/5$ | Tier 1 + Tier 2 | `lean/TriadFrontier/PIRCertificates.lean`, `lean/TriadFrontier/PIRKoszul.lean` (`t1e`), `data/h_uncond_certified.json`, `python/triad_verify/polymatroid_barrier.py` | Any subset pair $(A,B) \subseteq [12]$ with $h(A)+h(B) < h(A\cup B)+h(A\cap B)$, any violated $T=2$ privacy equality, or any negative Ingleton quantity |
| **C6** | `CS-053` | Projective $\mathbb{P}^3$ linear impossibility over any `SimpleField F`: four pairwise-intersecting 2-subspaces of $F^4$ are either concurrent or coplanar | Tier 1 | `lean/TriadFrontier/PIRKoszul.lean` (`t1f`), `lean/TriadFrontier/NonVacuity.lean` | Four 2-subspaces in $F^4$ pairwise intersecting non-trivially with zero common vector and spanning all of $F^4$ |
| **C7** | `CS-053` | Exact algebraic Zhang–Yeung (1998) reduction $\mathrm{ZY98}(A,B;C,D) = \mathrm{Ing}(C,D;A,B) + I(A;C\mid D) + I(A;D\mid C) + I(C;D\mid A)$ proving `h_uncond` defeats Zhang–Yeung too + symmetric $M \ge 3$ 1-flag Koszul denominator breaking $E \ge KT$ for all $M \ge 3$ | Tier 1 + Tier 2 | `lean/TriadFrontier/PIRKoszul.lean` (`t1g`), `tests/test_all.py` | Any 4-tuple on any Shannon+Ingleton polymatroid violating Zhang–Yeung (1998), or any $M \ge 3, K,T \ge 2$ where $E=K+1$ fails symmetry or $E < KT$ |
| **C8** | `CS-026` | Determinant-ideal secret independence ($\det(B) = q^m$ invariant under unimodular operations over any `CommRing`), refuting Luo (`arXiv:2604.15858`) | Tier 1 + Tier 2 | `lean/TriadFrontier/MLWETightness.lean` (`t2a`), `python/triad_verify/mlwe_tightness.py` | Any Kannan-embedded MLWE lattice whose determinant ideal depends on the secret vector $s$ or error $e$ |
| **C9** | `CS-026` | Ring-universal anti-periodic DFT even-mode cancellation $\hat{f}(2k) \equiv 0$ and odd $c,D$ quadratic Gauss parity witness explaining Chen (`ePrint 2024/555`) Step 9 | Tier 1 + Tier 2 | `lean/TriadFrontier/MLWETightness.lean` (`t2b`), `python/triad_verify/mlwe_tightness.py`, `native/src/triad_core.c` | Any odd $c,D$ quadratic Gauss sequence with non-zero even DFT coefficient $\hat{f}(2k)$ |
| **C10** | `CS-026` | Exact FIPS 203 $\mathrm{CBD}_2$ ($\mathrm{Var}=1, \mu_4=5/2$) vs. $\mathrm{CBD}_3$ ($\mathrm{Var}=3/2, \mu_4=6$) moments, cyclotomic trace-orthogonality over any `SimpleField F`, and $4.96\times$ Rényi-2 tightness cliff (60-digit $\mathrm{CBD}_2$: $37.84$ bits at ML-KEM-1024 vs. $\mathrm{CBD}_3$: $7.63$ bits at ML-KEM-512) | Tier 1 + Tier 2 | `lean/TriadFrontier/MLWETightness.lean` (`t2c`), `python/triad_verify/mlwe_tightness.py`, `eshkol/renyi_cbd_ad.esk`, `native/src/triad_core.c` | Any disagreement $> 10^{-12}$ among 60-digit Python, C11, and Eshkol AD, or any discrete Gaussian $\sigma > 0$ achieving $R_2(\mathrm{CBD}_2 \| D_\sigma) < 1.012890040837$ |
| **C11** | `CS-026` | QGTL shifted-LWE Berry curvature is normalization-invariant, vanishes identically by parity symmetry at $e_0 = 0$, and is strictly non-zero ($-512 \neq 0$) at $e_0 = 1$ | Tier 1 + Tier 2 | `lean/TriadFrontier/MLWETightness.lean` (`t2d`), `eshkol/qgtl_lwe_berry_ad.esk`, `native/src/triad_core.c` | Non-zero Berry curvature at $e_0 = 0$ for any symmetric noise distribution, or zero curvature at $e_0 = 1$ for $\mathrm{CBD}_2$ |
| **C12** | `CS-026 / CM-048` | Pure-integer Cauchy–Schwarz finite-support Rényi-2 floor $(1-\tau_S)^{-1}$, constant-time 1-byte `Dyadic-256` ($\mathrm{Var}=1, \mu_4=23/8$, $17.7\times$ collapse from $37.84$ to $2.14$ bits), universal QGTL Provost–Vallée PSD $4\det(g) \ge \Omega_{\theta\sigma}^2$, and exact Metric–Kurtosis ordering $3/8 < 15/32 < 1/2$ | Tier 1 + Tier 2 | `lean/TriadFrontier/MLWETightness.lean` (`t2e`), `native/src/triad_core.c`, `eshkol/renyi_cbd_ad.esk`, `python/triad_verify/mlwe_tightness.py` | Any $\{-2,\dots,2\}$ distribution beating $(1-\tau_2)^{-1}$, any byte $u \in [0,255]$ whose CT sample differs from weights $(1,14,63,100,63,14,1)$, or any state violating $4\det(g) \ge \Omega_{\theta\sigma}^2$ |
| **C13** | `CS-026 / QC-042` | Universal $m$-twisted DFT selection rule over ANY `CommRing R` (`[propext]` alone): $\omega^D = \zeta, f(qD+x)=\zeta^{qr}f(x), \sum \zeta^{q(r+k)} = 0 \implies \hat{f}_{mD}(k) = 0$ identically | Tier 1 + Tier 2 | `lean/TriadFrontier/MLWETightness.lean` (`t2f`), `native/src/triad_core.c`, `python/triad_verify/mlwe_tightness.py` | Any $m \ge 1, D \ge 1$ twisted sequence with nonzero DFT coefficient at a mode $k \not\equiv -r \pmod m$ |
| **C14** | `CS-001` | Constructive existence and global uniqueness of the multilinear extension $\tilde{f} : F^n \to F$ over any `SimpleField F` (Algebrization algebraic core) | Tier 1 + Tier 2 | `lean/TriadFrontier/ComplexityTriad.lean` (`t3a`), `python/triad_verify/complexity_triad.py` | Two distinct multilinear polynomials over a field agreeing on $\{0,1\}^n$ |
| **C15** | `CS-026 → CS-001` | Any $\varepsilon$-secure PRF family blocks $\delta$-large constructive Natural Proofs whenever $\varepsilon \le \delta$ | Tier 1 | `lean/TriadFrontier/ComplexityTriad.lean` (`t3b`) | A Natural Proof simultaneously distinguishing all PRFs ($A_{\mathrm{prf}}=0$) and accepting $\ge \delta$ of random functions while $\varepsilon \le \delta$ |
| **C16** | `CS-053 ↔ CS-051` | Any $B$-Byzantine zero-error PIR / LDC encoder-decoder pair requires minimum codeword Hamming distance $d_{\min} \ge 2B + 1$ | Tier 1 + Tier 2 | `lean/TriadFrontier/ComplexityTriad.lean` (`t3c`), `python/triad_verify/complexity_triad.py` | Two distinct messages at Hamming distance $\le 2B$ unambiguously decodable under up to $B$ corruptions |
| **C17** | `CS-026 ↔ CS-053` | Exact FIPS 203 `Compress_1` margin $|e| \le 831$ (round-half-up $+1665$, failing sharply at $+832$ for $b \in \{0,1\}$) and additive single-server MLWE-PIR depth ceiling $M \le \lfloor 831 / b_{\mathrm{step}} \rfloor$ | Tier 1 + Tier 2 | `lean/TriadFrontier/ComplexityTriad.lean` (`t3d`), `native/src/triad_core.c`, `python/triad_verify/complexity_triad.py` | Any $|e| \le 831$ decoding wrongly under `Compress_1(1665*b + e)`, or $e = +832$ decoding correctly |
| **C18** | `CS-053 ↔ CS-004 / CS-012` | Field-universal Koszul flattening tensor rank bridge: Steinitz/Gauss rank bound + 18-nnz $\{-1,0,+1\}$ left-inverse $L_2 \in \mathbb{Z}^{16\times 24}$ certifying $\mathrm{rank}_F(\langle 2,2,2\rangle) \ge 6$ and $L_3 \in \mathbb{Z}^{9\times 9}$ certifying $\mathrm{rank}_F(T_3) \ge 5$ over **every** field $F$ (incl. $\mathrm{char}\,2$) | Tier 1 + Tier 2 | `lean/TriadFrontier/KoszulTensor.lean` (`t3e`), `native/src/triad_core.c`, `python/triad_verify/complexity_triad.py` | Any rank-5 decomposition of $\langle 2,2,2\rangle$ or rank-4 decomposition of $T_3$ over any field $F$, or any entry of $L_2 \Phi_1(M_2) - I_{16}$ or $L_3 \Phi_1(T_3) - I_9$ nonzero over $\mathbb{Z}$ |
| **C19** | `CS-001 / CS-010 / CS-051` | Shannon (1949) finite circuit-counting non-surjectivity ($C < M \implies \exists f \in \mathrm{Fin}\, M$ uncomputed) + Katz–Trevisan $q$-query LDC smoothness averaging bound $|\{j : \mathrm{load}(j) \ge \tau\}|\cdot\tau \le q S$ | Tier 1 + Tier 2 | `lean/TriadFrontier/ComplexityTriad.lean` (`t3f`), `tests/test_all.py` | A surjection from $\mathrm{Fin}\, C$ onto $\mathrm{Fin}\, M$ with $C < M$, or a $q$-query set family violating the load averaging inequality |

## Explicitly Open Problems (`O1`–`O5` — NOT Claimed Solved)

| ID | Frontier | Open Statement |
|---|---|---|
| **O1** | `CS-001 / CS-010` | $\mathrm{P} \neq \mathrm{NP}$ and super-linear explicit Boolean circuit lower bounds remain completely open. |
| **O2** | `CS-004 / CS-012` | Matrix multiplication exponent $\omega = 2$ and Valiant's algebraic separation $\mathrm{VP} \neq \mathrm{VNP}$ remain completely open. |
| **O3** | `CS-053` | Closing $C(2,4,2,2) \in [3/5, 8/13]$ via $5+$-variable non-Shannon inequalities or non-linear PIR remains open (Shannon, Ingleton, and Zhang–Yeung 1998 are all defeated by `h_uncond`). |
| **O4** | `CS-053` | General $M \ge 3$ non-LFSR coded-colluding capacity above Sun–Zhang when $E \ge KT$ and deterministic arbitrary-$T \ge 4$ zero-error schemes remain open. |
| **O5** | `CS-026 / QC-042` | Worst-case quantum hardness lower bounds for MLWE/RLWE remain open cryptographic assumptions. |

## What Would Prove Us Wrong (Falsification Protocol)

Any independent reviewer can attempt to refute every claim in one command sequence from a clean clone:

```bash
# 1. Attempt to break Lean 4 proofs, find hidden axioms, or trigger kernel mismatch (19 theorems)
cd lean
lake build
lake env lean VerifyAxioms.lean
lake env leanchecker Solution
lake env leanchecker-paranoid Solution
lake comparator --config comparator.json --paranoid   # Ubuntu/Linux with bubblewrap

# 2. Attempt to falsify C11 arithmetic, Dyadic-256 CT sampler, twisted DFT, Koszul certs, or 512+ fuzz
cd ..
make -C native clean test
make -C native sanitizers   # Ubuntu/Linux ASan + UBSan

# 3. Attempt to falsify differential agreement across Python (60-digit), Eshkol AD, C11, and 8/8 mutation suite
node eshkol/run_eshkol_ad.mjs
PYTHONPATH=python pytest tests/test_all.py -v
python scripts/check_readme_axioms.py
python scripts/check_citations.py --online
```

Any single failing kernel check, unpermitted axiom, matrix rank deficit, polymatroid violation, differential mismatch $> 10^{-11}$, or unkilled core mutant refutes the corresponding claim in the ledger above.
