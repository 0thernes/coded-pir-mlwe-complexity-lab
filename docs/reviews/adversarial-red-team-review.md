<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Adversarial Red-Team Review (`docs/reviews/adversarial-red-team-review.md`)

Independent-style adversarial critique conducted prior to public release (Build Standard B45). Every attack vector was actively pursued against the proofs, code, and manuscript.

## Attack 1 — "Can `T1e` (`h_uncond`) violate a hidden elemental Shannon inequality outside the 330 canonical orbits?"
- **Attack:** Lean verifies all 330 canonical $S_4$ orbits (`checkAll330OrbitsSubmod = true`) rather than iterating all 67,584 elemental inequalities inside WHNF. What if the orbit reduction dropped an asymmetric triple or `h_uncond` was not strictly $S_4$-invariant?
- **Audit Result:** **Defended.** `python/triad_verify/polymatroid_barrier.py` independently enumerates ALL 4,096 subsets and ALL 67,584 unordered elemental triples $\{A \cup \{i\}, A \cup \{j\}\}$ directly without orbit reduction, plus all 2,816 $T=2$ privacy checks, all 2,970 singleton Ingletons, AND all 3,814,209 6-atom retrieval-subsystem Ingletons — observing **0 violations**.

## Attack 2 — "Does `T1c` actually prove the $\mathbb{F}_{11}$ Byzantine scheme is zero-error, or could a single adversarial server confuse two messages?"
- **Attack:** A scheme claiming $B=1$ Byzantine tolerance at $N=6, K=2, T=2, E=4$ must allow unique decoding from EVERY $\binom{6}{4} = 15$ subset of 4 honest servers (and satisfy full $T=2$ flag privacy across all $\binom{6}{2}=15$ colluding server pairs for both desired file indices).
- **Audit Result:** **Defended.** `PIRCertificates.lean` explicitly supplies all 15 exact $12 \times 12$ desired inverses, all 15 exact $8 \times 8$ interference inverses, and all $30 \times 2 = 60$ exact $5 \times 5$ flag-privacy inverses over $\mathbb{F}_{11}$, and multiplies every $M \cdot M^{-1} = I \pmod{11}$ inside Lean's kernel without `native_decide`. Independently re-verified in C11 (`triad_core.c`) and Python (`pir_koszul.py`).

## Attack 3 — "Could `T2c` (`4.96x` Rényi-2 cliff) be an artifact of suboptimal discrete Gaussian parameter $\sigma$?"
- **Attack:** What if a different $\sigma > 0$ makes $R_2(\mathrm{CBD}_2 \| D_\sigma)$ much closer to $1$?
- **Audit Result:** **Defended.** $R_2(\mathrm{CBD}_\eta \| D_\sigma)$ is strictly convex in $1/(2\sigma^2)$. Both 60-digit Python (`mlwe_tightness.py`) and Eshkol v1.3.6 forward-mode dual-number AD (`eshkol/renyi_cbd_ad.esk`, Newton root-finding on $\mathrm{d}R_2/\mathrm{d}\sigma = 0$ with $|\mathrm{d}R_2/\mathrm{d}\sigma| < 10^{-14}$) converge to the unique global minima $\sigma_2^* \approx 1.022596968$, $R_2^* = 1.012890040837456$ and $\sigma_3^* \approx 1.236505352$, $R_2^* = 1.005177975971433$, matching to $< 2 \times 10^{-13}$.

## Attack 4 — "Is `Compress_1` in `T3d` faithful to NIST FIPS 203?"
- **Attack:** FIPS 203 eq. (4.7) defines $\mathrm{Compress}_1(x) = \lceil (2/q)\cdot x \rfloor \bmod 2$, with division and rounding over the rationals (ties round up).
- **Audit Result (corrected 2026-11-26; FIXED in `v5.1.0` `L01`/`S03`):** The original entry recorded the change from `+1664` to `+1665` as a bug fix (`H01`). That was wrong: $2 \cdot 832 / 3329 = 1664/3329 < 1/2$, so FIPS 203 gives $\mathrm{Compress}_1(832) = 0$. In `v5.1.0` (`H36`), `mlkemCompress1` was redefined across Lean (`T3d`, `AdversarialTests.lean`), C11, Python, tests, and the CI tamper gate to literal FIPS 203 Eq. (4.7) $\lfloor(4(x \bmod 3329)+3329)/6658\rfloor \bmod 2$ (proved equivalent to `+1664` for all $x \in \mathbb{Z}$), with exact margins $|e| \le 832$ ($b=0$) and $-832 \le e \le 831$ ($b=1$) and sharp failures at $b=0, e=+833$ and $b=1, e=+832$. See `ERRATA.md` L01 and S03.

## Attack 5 — "Are any paper claims overstated regarding $\mathrm{P} \neq \mathrm{NP}$, $C(2,4,2,2)$, or MLWE quantum hardness?"
- **Audit Result:** **Audited & hardened (`H12`).** Section 6 of `paper/main.tex`, `CLAIMS.md`, `LIMITATIONS.md`, and `README.md` mark those open frontiers as unsolved. An independent statement audit (2026-11-26) later found other overstated claims (the `T1a` resolution, the `T2a` refutation, the DFR paradox, the $\ge 7$-variable barrier); see `ERRATA.md`.
