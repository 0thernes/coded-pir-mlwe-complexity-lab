<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Claims Ledger & Falsification Protocol (`CLAIMS.md`)

Every mathematical and computational claim in `coded-pir-mlwe-complexity-lab` is assigned a unique ID, an explicit verification tier, exact artifact paths, and a concrete falsification test ("what would prove us wrong").

## Verification Tiers

- **Tier 1 (Machine-Checked Formal Proof):** Zero-Mathlib Lean 4.35.0 proof depending strictly on a subset of `[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero `native_decide`, independently replayed across all six Lean 4.35.0 kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche --verified`, `con-ron --verified`).
- **Tier 2 (Exact / Arbitrary-Precision Computation):** Deterministic integer, rational, finite-field, or 60-digit `Decimal` computation cross-checked differentially across Python, C11, and Eshkol v1.3.6 dual-number AD.
- **Open (Explicitly Unproved):** Conjectures and open frontiers intentionally separated from claimed results.

## Verified Claims (`C1`–`C14`)

| ID | Pillar | Statement Summary | Tier | Formal / Code Artifacts | Falsifying Condition ("What Would Prove Us Wrong") |
|---|---|---|---|---|---|
| **C1** | `CS-053` | Exterior-power Koszul–Veronese moment annihilation $\langle u(\alpha), e_{r+1}-\alpha e_r\rangle = 0$ over any `CommRing`, Pascal interference savings $K\binom{T}{T'} = \lambda^\star + (K-T')\binom{T-1}{T'}$, and flagship $(6,3,3)$ rate $10/17 > 4/7$ | Tier 1 + Tier 2 | `lean/TriadFrontier/PIRKoszul.lean` (`t1a`), `python/triad_verify/pir_koszul.py`, `native/src/triad_core.c` | Any `CommRing` counterexample where $\langle u(\alpha), e_{r+1}-\alpha e_r\rangle \neq 0$, any $(T,T',K)$ violating Pascal savings, or any rank deficit in the 46 Koszul blocks at $(6,3,3)$ |
| **C2** | `CS-053` | Exact $K \leftrightarrow T$ symmetry and universal strict domination $R_{\mathrm{KV}} > R_{\mathrm{LFSR}}$ for all $K \ge 2, T \ge 2, E \ge 2$ in single-file and multi-file $P$-out-of-$M$ regimes via surplus $(K-1)(T-1)E^2 > 0$ | Tier 1 + Tier 2 | `lean/TriadFrontier/PIRKoszul.lean` (`t1b`), `eshkol/koszul_pir_ad.esk`, `tests/test_all.py` | Any integer tuple $(P,M,E,K,T)$ with $1 \le P < M, E,K,T \ge 2$ where $R_{\mathrm{KV}} \le R_{\mathrm{LFSR}}$ |
| **C3** | `CS-053` | Non-vacuous Byzantine-robust double-counting converse reduction; exact $E=K+1$ match to Sun–Jafar unrestricted capacity (breaking $E \ge KT$); kernel-certified zero-error $\mathbb{F}_{11}$ Byzantine rate-$2/5$ scheme at $(M=2,N=6,K=2,T=2,B=1,E=4)$ | Tier 1 + Tier 2 | `lean/TriadFrontier/PIRCertificates.lean`, `lean/TriadFrontier/PIRKoszul.lean` (`t1c`), `data/f11_byz_witness.json`, `native/src/triad_core.c` | Any of the 15 desired $12 \times 12$ matrices, 15 interference $8 \times 8$ matrices, or 60 flag-privacy $5 \times 5$ matrices over $\mathbb{F}_{11}$ failing full rank |
| **C4** | `CS-053` | Exact flag-privacy dimension thresholds ($K=2,T=2 \iff E \ge 4$; zero-error $T=3,K=2 \iff E \ge 6$) and universal overlap feasibility $E w \le K\delta\sigma$ (equality iff $E=K+1$) | Tier 1 + Tier 2 | `lean/TriadFrontier/PIRKoszul.lean` (`t1d`), `python/triad_verify/pir_koszul.py` | Any valid flag-private basis violating $(3E-4)+E \le E(E-1) \iff E \ge 4$ or $E w \le K\delta\sigma$ |
| **C5** | `CS-053` | Pure-integer scale-128 12-variable polymatroid `h_uncond` satisfies all 12 monotonicity inequalities, all 270,336 elemental Shannon submodularity inequalities (via 330 $S_4$ orbits + direct full enumeration of 67,584 triples), all 99 PIR equalities, all 1,485 singleton Ingletons, and 3,814,209 6-atom Ingletons at $C = 8/13 > 3/5$ | Tier 1 + Tier 2 | `lean/TriadFrontier/PIRCertificates.lean`, `lean/TriadFrontier/PIRKoszul.lean` (`t1e`), `data/h_uncond_certified.json`, `python/triad_verify/polymatroid_barrier.py` | Any subset pair $(A,B) \subseteq [12]$ with $h(A)+h(B) < h(A\cup B)+h(A\cap B)$, any violated $T=2$ privacy equality, or any negative Ingleton quantity |
| **C6** | `CS-053` | Projective $\mathbb{P}^3$ linear impossibility over any `SimpleField F`: four pairwise-intersecting 2-subspaces of $F^4$ are either concurrent or coplanar | Tier 1 | `lean/TriadFrontier/PIRKoszul.lean` (`t1f`), `lean/TriadFrontier/NonVacuity.lean` | Four 2-subspaces in $F^4$ pairwise intersecting non-trivially with zero common vector and spanning all of $F^4$ |
| **C7** | `CS-026` | Determinant-ideal secret independence ($\det(B) = q^m$ invariant under unimodular operations over any `CommRing`), refuting Luo (`arXiv:2604.15858`) | Tier 1 + Tier 2 | `lean/TriadFrontier/MLWETightness.lean` (`t2a`), `python/triad_verify/mlwe_tightness.py` | Any Kannan-embedded MLWE lattice whose determinant ideal depends on the secret vector $s$ or error $e$ |
| **C8** | `CS-026` | Ring-universal anti-periodic DFT even-mode cancellation $\hat{f}(2k) \equiv 0$ and odd $c,D$ quadratic Gauss parity witness explaining Chen (`ePrint 2024/555`) Step 9 | Tier 1 + Tier 2 | `lean/TriadFrontier/MLWETightness.lean` (`t2b`), `python/triad_verify/mlwe_tightness.py`, `native/src/triad_core.c` | Any odd $c,D$ quadratic Gauss sequence with non-zero even DFT coefficient $\hat{f}(2k)$ |
| **C9** | `CS-026` | Exact FIPS 203 $\mathrm{CBD}_2$ ($\mathrm{Var}=1, \mu_4=5/2$) vs. $\mathrm{CBD}_3$ ($\mathrm{Var}=3/2, \mu_4=6$) moments, cyclotomic trace-orthogonality over any `SimpleField F`, and $4.96\times$ Rényi-2 tightness cliff (60-digit $\mathrm{CBD}_2$: $\min R_2 = 1.012890040837456$, 37.84 bits at ML-KEM-1024 vs. $\mathrm{CBD}_3$: $\min R_2 = 1.005177975971433$, 7.63 bits at ML-KEM-512) | Tier 1 + Tier 2 | `lean/TriadFrontier/MLWETightness.lean` (`t2c`), `python/triad_verify/mlwe_tightness.py`, `eshkol/renyi_cbd_ad.esk`, `native/src/triad_core.c` | Any disagreement $> 10^{-12}$ among 60-digit Python, C11, and Eshkol AD, or any discrete Gaussian $\sigma > 0$ achieving $R_2(\mathrm{CBD}_2 \| D_\sigma) < 1.012890040837$ |
| **C10** | `CS-026` | QGTL shifted-LWE Berry curvature is normalization-invariant, vanishes identically by parity symmetry at $e_0 = 0$, and is strictly non-zero ($-512 \neq 0$) at $e_0 = 1$ | Tier 1 + Tier 2 | `lean/TriadFrontier/MLWETightness.lean` (`t2d`), `eshkol/qgtl_lwe_berry_ad.esk`, `native/src/triad_core.c` | Non-zero Berry curvature at $e_0 = 0$ for any symmetric noise distribution, or zero curvature at $e_0 = 1$ for $\mathrm{CBD}_2$ |
| **C11** | `CS-001` | Constructive existence and global uniqueness of the multilinear extension $\tilde{f} : F^n \to F$ over any `SimpleField F` (Algebrization algebraic core) | Tier 1 + Tier 2 | `lean/TriadFrontier/ComplexityTriad.lean` (`t3a`), `python/triad_verify/complexity_triad.py` | Two distinct multilinear polynomials over a field agreeing on $\{0,1\}^n$ |
| **C12** | `CS-026 → CS-001` | Any $\varepsilon$-secure PRF family blocks $\delta$-large constructive Natural Proofs whenever $\varepsilon \le \delta$ | Tier 1 | `lean/TriadFrontier/ComplexityTriad.lean` (`t3b`) | A Natural Proof simultaneously distinguishing all PRFs ($A_{\mathrm{prf}}=0$) and accepting $\ge \delta$ of random functions while $\varepsilon \le \delta$ |
| **C13** | `CS-053 ↔ CS-051` | Any $B$-Byzantine zero-error PIR / LDC encoder-decoder pair requires minimum codeword Hamming distance $d_{\min} \ge 2B + 1$ | Tier 1 + Tier 2 | `lean/TriadFrontier/ComplexityTriad.lean` (`t3c`), `python/triad_verify/complexity_triad.py` | Two distinct messages at Hamming distance $\le 2B$ unambiguously decodable under up to $B$ corruptions |
| **C14** | `CS-026 ↔ CS-053` | Exact FIPS 203 `Compress_1` margin $|e| \le 831$ (round-half-up $+1665$, failing sharply at $+832$ for $b \in \{0,1\}$) and additive single-server MLWE-PIR depth ceiling $M \le \lfloor 831 / b_{\mathrm{step}} \rfloor$ | Tier 1 + Tier 2 | `lean/TriadFrontier/ComplexityTriad.lean` (`t3d`), `native/src/triad_core.c`, `python/triad_verify/complexity_triad.py` | Any $|e| \le 831$ decoding wrongly under `Compress_1(1665*b + e)`, or $e = +832$ decoding correctly |

## Explicitly Open Problems (`O1`–`O4` — NOT Claimed Solved)

| ID | Frontier | Open Statement |
|---|---|---|
| **O1** | `CS-001` | $\mathrm{P} \neq \mathrm{NP}$ and super-polynomial circuit lower bounds remain completely open. |
| **O2** | `CS-053` | Closing $C(2,4,2,2) \in [3/5, 8/13]$ via $5+$-variable non-Shannon inequalities or non-linear PIR remains open. |
| **O3** | `CS-053` | General $M \ge 3$ non-LFSR coded-colluding capacity and deterministic arbitrary-$T \ge 4$ zero-error schemes remain open. |
| **O4** | `CS-026` | Worst-case quantum hardness lower bounds for MLWE/RLWE remain open cryptographic assumptions. |

## What Would Prove Us Wrong (Falsification Protocol)

Any independent reviewer can attempt to refute every claim in one command sequence from a clean clone:

```bash
# 1. Attempt to break Lean 4 proofs, find hidden axioms, or trigger kernel mismatch
cd lean
lake build
lake env lean VerifyAxioms.lean
lake env leanchecker Solution
lake env leanchecker-paranoid Solution
lake comparator --config comparator.json --paranoid   # Ubuntu/Linux with bubblewrap

# 2. Attempt to falsify C11 arithmetic, F_11 Byzantine witness, Chen Step 9, or 500-case QGTL fuzz
cd ..
make -C native clean test
make -C native sanitizers   # Ubuntu/Linux ASan + UBSan

# 3. Attempt to falsify differential agreement across Python (60-digit), Eshkol AD, C11, and mutation suite
node eshkol/run_eshkol_ad.mjs
PYTHONPATH=python pytest tests/test_all.py -v
python scripts/check_readme_axioms.py
python scripts/check_citations.py --online
```

Any single failing kernel check, unpermitted axiom, matrix rank deficit, polymatroid violation, differential mismatch $> 10^{-11}$, or unkilled core mutant refutes the corresponding claim in the ledger above.
