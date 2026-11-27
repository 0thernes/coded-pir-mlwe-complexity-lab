<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# System & Mathematical Architecture (`docs/architecture.md`)

`coded-pir-mlwe-complexity-lab` (`v5.4.0`) is structured as a four-layer verification stack: **34 Lean 4.35.0 proofs (`T1a`–`T3m`) + 11 adversarial tests (`AdversarialTests.lean`, 37 audited declarations + 2,306 `TriadFrontier.*` declarations swept by `AuditExhaustiveAxioms.lean` under `module`)** of identities, sound linear-rank certificates, in-kernel $\mathbb{F}_{101}$ PIR existence (`T1l`), characteristic-free Bläser $\frac{5}{2}m^2-3m$ (`T3m`), and finite certificates, cross-checked by hardened C11 (90 tests + 1,024 fuzz), Eshkol dual-number AD and Python computations (including the live $\mathbb{F}_{101}$ $(6,3,3)$ 20/20 zero-error witness, Bareiss exact commutator determinants, and 90-digit Kronecker coupled FIPS 203 DFR oracle), and upward into the AMS-LaTeX preprint and CSP/WCAG-AA interactive GitHub Pages Proof Blueprint.

```text
                        +----------------------------------------------+
                        |  paper/main.tex (AMS-LaTeX Preprint v5.4.0)  |
                        |  + 8 Vector PDF Figures + refs.bib (37 HTTP) |
                        |  + docs/site/ CSP/WCAG-AA Proof Blueprint    |
                        +----------------------+-----------------------+
                                               |
             +---------------------------------+---------------------------------+
             |                                 |                                 |
+------------v-------------+     +-------------v--------------+     +------------v-------------+
| Tier 1: Lean 4.35.0      |     | Tier 2: Multi-Language     |     | Tier 3: Governance &     |
| Zero-Mathlib TCB (34+11) |     | Computational Cross-Audit  |     | Provenance Layer         |
|  - AlgebraCore.lean      |     |  - native/ (C11 90 tests)  |     |  - CLAIMS.md (C1-C34)    |
|  - PIRCertificates/Lin.  |     |  - eshkol/ (Dual-Num AD)   |     |  - LIMITATIONS/ERRATA.md |
|  - LinearRank/PIRProt.   |     |  - python/triad_verify/    |     |  - HARDENING_LOG.md      |
|  - PIRF101Cert (T1l)     |     |    (90-dig DFR, 0 ruff/my) |     |  - MANIFEST + TSR + OTS  |
|  - PIRKoszul (T1a-T1l)   |     |  - tests/test_all.py       |     |  - rosette_receipt.json  |
|  - MLWETightness (T2a-i) |     |    (26 tests, 18/18 muts)  |     |  - SLSA + Rekor + CI Gate|
|  - Koszul/Strass/Blaser  |     +----------------------------+     +--------------------------+
|  - Shannon/Paley (T3j,l) |
|  - AlgComplexity (T3k)   |
|  - NonVacuity & AdvTests |
|  - AuditExhaustiveAxioms |
+--------------------------+
```

## Pillar Dependency Architecture

1. **Pillar I (`CS-053` — Coded, Colluding, Robust & Byzantine PIR):**
   - `TriadFrontier/AlgebraCore.lean` defines zero-Mathlib `CommRing`, `SimpleField` (incl. canonical `Fin 2` and `Fin 3`), `rPow`, `chooseNat`, and `PairwiseNeq`.
   - `TriadFrontier/PIRCertificates.lean` stores $O(\log N)$ balanced binary-tree lookup certificates for the $\mathbb{F}_{11}$ rate-$2/5$ Byzantine witness (90 exact matrix inverses) and the 330-orbit pure-integer scale-128 polymatroid `h_uncond`.
   - `TriadFrontier/PIRLinearCerts.lean` certifies 23 $\mathbb{F}_2/\mathbb{F}_3$ linear-subspace 4-variable rays, denominator-3 decompositions of all 24 canonical profiles covering ALL 510 four-marginals of `h_uncond`, exact $\mathbb{F}_2$-linear subspace realizations of ALL 6 five-object retrieval marginals (`T1i`), AND the exact 6-subspace realization in $\mathbb{F}_2^{64}$ (`4 * rank` scaling) of the entire 6-object retrieval marginal $(W_1, W_2, A_1, A_2, A_3, A_4)$ across all 64 subsets (`T1j`).
   - `TriadFrontier/LinearRankSoundness.lean` & `TriadFrontier/PIRProtocol.lean` (`T1k`, closing `L02` & `S01`/`A02`) prove standard vector-space `HasSpanDim` soundness & Steinitz uniqueness for `matRankModP` ($\mathbb{F}_2,\mathbb{F}_3$) and `gf2RankSparse` ($\mathbb{F}_2$) AND field-universal exact zero-error decoding + explicit two-sided colluder-transcript bijection $\Psi_I$ for the 2-file, $N$-server, $K$-MDS flag-private PIR protocol.
   - `TriadFrontier/PIRF101Cert.lean` (`T1l`, `v5.4.0`) proves unconditional *in-kernel* constructive existence over `SimpleField (Fin 101)` of the explicit $(6,3,3)$ rate-$10/17$ zero-error 20/20 $T=3$-private PIR scheme with zero `native_decide` and zero external oracles.
   - `TriadFrontier/PIRKoszul.lean` proves `T1a`–`T1k`.
2. **Pillar II (`CS-026`, `QC-042`, `CM-048` — Module-LWE Reduction Tightness, `Dyadic-256..16384-A/B`, Bai Engine & QGTL Geometry):**
   - `TriadFrontier/MLWETightness.lean` proves `T2a`–`T2i`. Rényi values, Bai overheads and exact coupled FIPS 203 DFRs (cross-verified by a 90-digit Kronecker exact interval oracle reproducing NIST Table 1 within `0.04` bits, closing `S02`) are computed outside Lean.
3. **Pillar III (`CS-001`, `CS-004`, `CS-010`, `CS-012`, `CS-051`, `CS-CMP-012`, Cross-Pillar Unification):**
   - `TriadFrontier/KoszulTensor.lean` proves `T3e` and `T3g` ($\mathrm{rank}_F(\langle 2,2,2\rangle) \ge 6$, $\mathrm{rank}_F(T_3) \ge 5$, symbolic ALL-$m$ $\mathrm{rank}_F(\langle m,m,m\rangle) \ge m^2 + 2$, and ceiling $m^2+m$).
   - `TriadFrontier/StrassenWinograd.lean` proves `T3h` (complete characteristic-free Exact Strassen–Winograd $\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$ over every `SimpleField F`, including $\mathbb{F}_2$).
   - `TriadFrontier/BrockettDobkin.lean` proves `T3i` (field-universal substitution-method bound, quadratic $\mathrm{rank}_F(\langle m,m,m\rangle) \ge 2m^2-m$, and Strassen lift $\mathrm{rank}_F(\langle m,2,p\rangle) \ge mp+3$).
   - `TriadFrontier/BlaserLowerBound.lean` (`T3m`, `v5.4.0`) proves Markus Bläser's (FOCS 1999) characteristic-free $\frac{5}{2}m^2-3m$ lower bound ($5m^2 - 6m \le 2\,\mathrm{rank}_F(\langle m,m,m\rangle)$) over **every** `SimpleField F` (including $\mathbb{F}_2$), strictly beating Brockett–Dobkin's $2m^2-1$ for all $m \ge 6$ and tightening the Strassen–Bläser sandwich to $5\cdot 4^k - 6\cdot 2^k \le 2\,\mathrm{rank}_F(\langle 2^k,2^k,2^k\rangle) \le 2\cdot 7^k$.
   - `TriadFrontier/ShannonCapacity.lean` proves `T3j` (field-universal Haemers bound $|S| \le r^t$, a $\mathbb{Z}[\sqrt{5}]$ SOS proof of the integer form of Lovász's $\Theta(C_5)=\sqrt{5}$, and exact $C_7$ minimum Haemers rank $= 4$ over every field $F$).
   - `TriadFrontier/AlgebraicComplexity.lean` proves `T3k` (universal constructive Schwartz–Zippel lemma $|Z(P)\cap S^n| \le d|S|^{n-1}$ and the two-sided Strassen bound over every `SimpleField F`).
   - `TriadFrontier/PaleyCapacity.lean` proves `T3l` (a conditional $\mathbb{Z}[\sqrt{p}]$ 2-block SOS theorem: for every self-complementary conference graph on $4k+1$ vertices, $\alpha(G^{\boxtimes t})^2 \le (4k+1)^t$ and $\alpha(G^{\boxtimes 2m}) \ge (4k+1)^m$; hypotheses proved for $P_5, P_{13}, P_{17}$; the general capacity result is Lovász, 1979).
   - `TriadFrontier/ComplexityTriad.lean` proves `T3a`–`T3d` and `T3f`.
4. **Palomar 6-Kernel Verification & Negative Tamper Gate Boundary:**
   - `lean/Challenge.lean` defines all 34 theorem propositions (`T1a`–`T3m`) and their conjunction (`588` lines, `30,745` bytes).
   - `lean/Solution.lean` exports the verified proofs; `lean/TriadFrontier/AdversarialTests.lean` proves 11 adversarial tests (closing `L01` & `L07`, plus `adv_blaser_refutes_rank_71_at_m6`); `lean/VerifyAxioms.lean` runs `#print axioms` on all **37 audited declarations** (34 theorems + master conjunction + `nonvac_all_hypotheses` + `adv_all_boundary_refutations`), and `lean/AuditExhaustiveAxioms.lean` sweeps all **2,306** `TriadFrontier.*` declarations programmatically via `Lean.collectAxioms` under Lean 4.35.0 `module`.
   - `lean/PalomarChallenge.lean` (excluded from `defaultTargets`) and `lean/PalomarSolution.lean` form the exact contract judged by `lake comparator --config comparator.json --paranoid` (5,711 `con-leche`/`con-ron` verified declarations on the standalone `Solution` export, `nanoda_bin` clean acceptance, plus a live negative tamper gate checking that the kernel rejects the genuinely false equation `mlkemCompress1 (1665 + 832) = 1` under exact FIPS 203 Eq. (4.7)).
