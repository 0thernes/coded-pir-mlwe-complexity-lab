<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# System & Mathematical Architecture (`docs/architecture.md`)

`coded-pir-mlwe-complexity-lab` (`v5.0.0`) is structured as a four-layer verification stack: **31 Lean 4.35.0 proofs (`T1a`–`T3l`) + 7 adversarial tests (`AdversarialTests.lean`, 34 audited declarations)** of identities, inequalities and finite certificates, cross-checked by C11, Eshkol dual-number AD and Python computations (which also produce the numerical results that are not in Lean: rates, Rényi values, Bai overheads and float64 DFRs), and upward into the AMS-LaTeX preprint and interactive GitHub Pages Proof Blueprint.

```text
                        +----------------------------------------------+
                        |  paper/main.tex (AMS-LaTeX Preprint v5.0.0)  |
                        |  + 8 Vector PDF Figures + refs.bib (36 HTTP) |
                        |  + docs/site/ Interactive Proof Blueprint    |
                        +----------------------+-----------------------+
                                               |
             +---------------------------------+---------------------------------+
             |                                 |                                 |
+------------v-------------+     +-------------v--------------+     +------------v-------------+
| Tier 1: Lean 4.35.0      |     | Tier 2: Multi-Language     |     | Tier 3: Governance &     |
| Zero-Mathlib TCB (31+7)  |     | Computational Cross-Audit  |     | Provenance Layer         |
|  - AlgebraCore.lean      |     |  - native/ (C11 79 tests)  |     |  - CLAIMS.md (C1-C31)    |
|  - PIRCertificates/Lin.  |     |  - eshkol/ (Dual-Num AD)   |     |  - LIMITATIONS/ERRATA.md |
|  - PIRKoszul.lean (T1a-j)|     |  - python/triad_verify/    |     |  - HARDENING_LOG.md      |
|  - MLWETightness (T2a-i) |     |    (strict 0 ruff, 0 mypy) |     |  - MANIFEST.sha256 + TSR |
|  - Koszul/Strass/Brockett|     |  - tests/test_all.py       |     |  - rosette_receipt.json  |
|  - Shannon/Paley (T3j,l) |     |    (18 tests, 14/14 muts)  |     |  - SLSA + Rekor + CI Gate|
|  - AlgComplexity (T3k)   |     +----------------------------+     +--------------------------+
|  - NonVacuity & AdvTests |
+--------------------------+
```

## Pillar Dependency Architecture

1. **Pillar I (`CS-053` — Coded, Colluding, Robust & Byzantine PIR):**
   - `TriadFrontier/AlgebraCore.lean` defines zero-Mathlib `CommRing`, `SimpleField`, `rPow`, `chooseNat`, and `PairwiseNeq`.
   - `TriadFrontier/PIRCertificates.lean` stores $O(\log N)$ balanced binary-tree lookup certificates for the $\mathbb{F}_{11}$ rate-$2/5$ Byzantine witness (90 exact matrix inverses) and the 330-orbit pure-integer scale-128 polymatroid `h_uncond` (submodularity on 330 orbit representatives, which by permutation invariance covers the 67,584 elemental submodularity inequalities, + 99 listed equalities + 1,485 singleton Ingletons).
   - `TriadFrontier/PIRLinearCerts.lean` certifies, via rank routines that have no Lean correctness proof, 23 $\mathbb{F}_2/\mathbb{F}_3$ linear-subspace 4-variable rays, denominator-3 decompositions of all 24 canonical profiles covering ALL 510 four-marginals of `h_uncond`, exact $\mathbb{F}_2$-linear subspace realizations of ALL 6 five-object retrieval marginals (`T1i`), AND the exact 6-subspace realization in $\mathbb{F}_2^{64}$ (`4 * rank` scaling) of the entire 6-object retrieval marginal $(W_1, W_2, A_1, A_2, A_3, A_4)$ across all 64 subsets (`T1j`).
   - `TriadFrontier/PIRKoszul.lean` proves `T1a`–`T1j`.
2. **Pillar II (`CS-026`, `QC-042`, `CM-048` — Module-LWE Reduction Tightness, `Dyadic-256..16384-A/B`, Bai Engine & QGTL Geometry):**
   - `TriadFrontier/MLWETightness.lean` proves `T2a`–`T2i`: a diagonal-product identity (the $q$-ary MLWE basis has determinant $q^m$; no published claim is refuted), an anti-periodic DFT cancellation identity (proposed as an explanation of Chen's Step 9, whose bug was found by Hongxun Wu and Thomas Vidick), FIPS 203 $\mathrm{CBD}_2/\mathrm{CBD}_3$ $4.96\times$ cliff, QGTL shifted-LWE Berry curvature, Cauchy–Schwarz floor + 1-byte `Dyadic-256` + QGTL PSD, universal $m$-twisted DFT rule, Pearson $\chi^2$/Hermite-4 variational bridge + 9-bit `Dyadic-512`, all-order Rényi-$(m+1)$ Hölder floor + TV–$\chi^2$ bridge + 10-bit `Dyadic-1024-A/B`, and integer data-processing, tensorization and tail-transfer inequalities with moment tables for the 14-bit `Dyadic-16384-A/B` weights. Rényi values, Bai overheads and DFRs (float64 model) are computed outside Lean.
3. **Pillar III (`CS-001`, `CS-004`, `CS-010`, `CS-012`, `CS-051`, `CS-CMP-012`, Cross-Pillar Unification):**
   - `TriadFrontier/KoszulTensor.lean` proves `T3e` and `T3g` ($\mathrm{rank}_F(\langle 2,2,2\rangle) \ge 6$, $\mathrm{rank}_F(T_3) \ge 5$, symbolic ALL-$m$ $\mathrm{rank}_F(\langle m,m,m\rangle) \ge m^2 + 2$, and ceiling $m^2+m$).
   - `TriadFrontier/StrassenWinograd.lean` proves `T3h` (complete characteristic-free Exact Strassen–Winograd $\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$ over every `SimpleField F`, including $\mathbb{F}_2$).
   - `TriadFrontier/BrockettDobkin.lean` proves `T3i` (a field-universal substitution-method bound, quadratic $\mathrm{rank}_F(\langle m,m,m\rangle) \ge 2m^2-m$, weaker than the published Brockett–Dobkin $2m^2-1$, and Strassen lift $\mathrm{rank}_F(\langle m,2,p\rangle) \ge mp+3$).
   - `TriadFrontier/ShannonCapacity.lean` proves `T3j` (field-universal Haemers bound $|S| \le r^t$, a $\mathbb{Z}[\sqrt{5}]$ SOS proof of the integer form of Lovász's $\Theta(C_5)=\sqrt{5}$, and exact $C_7$ minimum Haemers rank $= 4$ over every field $F$).
   - `TriadFrontier/AlgebraicComplexity.lean` proves `T3k` (universal constructive Schwartz–Zippel lemma $|Z(P)\cap S^n| \le d|S|^{n-1}$ and the two-sided bound $2\cdot 4^k - 2^k \le \mathrm{rank}_F(\langle 2^k,2^k,2^k\rangle) \le 7^k$ over every `SimpleField F`).
   - `TriadFrontier/PaleyCapacity.lean` proves `T3l` (a conditional $\mathbb{Z}[\sqrt{p}]$ 2-block SOS theorem: for every self-complementary conference graph on $4k+1$ vertices, $\alpha(G^{\boxtimes t})^2 \le (4k+1)^t$ and $\alpha(G^{\boxtimes 2m}) \ge (4k+1)^m$; hypotheses proved for $P_5, P_{13}, P_{17}$; the general capacity result is Lovász, 1979).
   - `TriadFrontier/ComplexityTriad.lean` proves `T3a`–`T3d` and `T3f`.
4. **Palomar 6-Kernel Verification & Negative Tamper Gate Boundary:**
   - `lean/Challenge.lean` defines all 31 theorem propositions (`T1a`–`T3l`) and their conjunction.
   - `lean/Solution.lean` exports the verified proofs; `lean/TriadFrontier/AdversarialTests.lean` proves 7 adversarial tests (two are closed arithmetic facts; see `ERRATA.md`); `lean/VerifyAxioms.lean` runs `#print axioms` on all **34 audited declarations** (31 theorems + master conjunction + `nonvac_all_hypotheses` + `adv_all_boundary_refutations`).
   - `lean/PalomarChallenge.lean` (excluded from `defaultTargets`) and `lean/PalomarSolution.lean` form the exact contract judged by `lake comparator --config comparator.json --paranoid` (4,300 `con-leche`/`con-ron` verified declarations on the standalone `Solution` export, `nanoda_bin` clean acceptance, plus a negative tamper gate checking that the kernel rejects `mlkemCompress1 832 = 0`; note that 0 is the true FIPS 203 value at 832, see `ERRATA.md` L01 and S03).
