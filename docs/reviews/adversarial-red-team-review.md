<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Adversarial Red-Team Review (`docs/reviews/adversarial-red-team-review.md`)

Independent-style adversarial critique conducted prior to public release (Build Standard B45). Every attack vector was actively pursued against the proofs, code, and manuscript.

## Attack 1 — "Can `T1e` (`h_uncond`) violate a hidden elemental Shannon inequality outside the 330 canonical orbits?"
- **Attack:** Lean verifies all 330 canonical $S_4$ orbits (`checkAll330OrbitsSubmod = true`) rather than iterating all 270,336 raw triples inside WHNF. What if the orbit reduction dropped an asymmetric triple or `h_uncond` was not strictly $S_4$-invariant?
- **Audit Result:** **Defended.** `python/triad_verify/polymatroid_barrier.py` independently enumerates ALL 4,096 subsets and ALL 67,584 unordered elemental triples $\{A \cup \{i\}, A \cup \{j\}\}$ (equivalent to all 270,336 ordered inequalities) directly without orbit reduction, plus all 2,816 $T=2$ privacy checks, all 2,970 singleton Ingletons, AND all 3,814,209 6-atom retrieval-subsystem Ingletons — observing **0 violations**.

## Attack 2 — "Does `T1c` actually prove the $\mathbb{F}_{11}$ Byzantine scheme is zero-error, or could a single adversarial server confuse two messages?"
- **Attack:** A scheme claiming $B=1$ Byzantine tolerance at $N=6, K=2, T=2, E=4$ must allow unique decoding from EVERY $\binom{6}{4} = 15$ subset of 4 honest servers (and satisfy full $T=2$ flag privacy across all $\binom{6}{2}=15$ colluding server pairs for both desired file indices).
- **Audit Result:** **Defended.** `PIRCertificates.lean` explicitly supplies all 15 exact $12 \times 12$ desired inverses, all 15 exact $8 \times 8$ interference inverses, and all $30 \times 2 = 60$ exact $5 \times 5$ flag-privacy inverses over $\mathbb{F}_{11}$, and multiplies every $M \cdot M^{-1} = I \pmod{11}$ inside Lean's kernel without `native_decide`. Independently re-verified in C11 (`triad_core.c`) and Python (`pir_koszul.py`).

## Attack 3 — "Could `T2c` (`4.96x` Rényi-2 cliff) be an artifact of suboptimal discrete Gaussian parameter $\sigma$?"
- **Attack:** What if a different $\sigma > 0$ makes $R_2(\mathrm{CBD}_2 \| D_\sigma)$ much closer to $1$?
- **Audit Result:** **Defended.** $R_2(\mathrm{CBD}_\eta \| D_\sigma)$ is strictly convex in $1/(2\sigma^2)$. Both 60-digit Python (`mlwe_tightness.py`) and Eshkol v1.3.6 forward-mode dual-number AD (`eshkol/renyi_cbd_ad.esk`, Newton root-finding on $\mathrm{d}R_2/\mathrm{d}\sigma = 0$ with $|\mathrm{d}R_2/\mathrm{d}\sigma| < 10^{-14}$) converge to the unique global minima $\sigma_2^* \approx 1.022596968$, $R_2^* = 1.012890040837456$ and $\sigma_3^* \approx 1.236505352$, $R_2^* = 1.005177975971433$, matching to $< 2 \times 10^{-13}$.

## Attack 4 — "Is `Compress_1` in `T3d` faithful to NIST FIPS 203?"
- **Attack:** FIPS 203 Section 4.2.1 defines $\mathrm{Compress}_1(x) = \lceil (2/q)\cdot x \rfloor \bmod 2$ with round-half-up.
- **Audit Result:** **Caught real defect during red-team pass (`H01`)!** Our first draft used $+1664$, which rounded $x = 832$ down to $0$ instead of up to $1$. Both Lean `decide` and Python caught it immediately; we fixed the constant to $+1665$ across Lean, C11, Python, and LaTeX, and added sharp boundary regression tests at $e = \pm 831$ and $e = +832$.

## Attack 5 — "Are any paper claims overstated regarding $\mathrm{P} \neq \mathrm{NP}$, $C(2,4,2,2)$, or MLWE quantum hardness?"
- **Audit Result:** **Audited & hardened (`H12`).** Section 6 of `paper/main.tex`, `CLAIMS.md` (`O1`–`O4`), `LIMITATIONS.md`, and `README.md` all explicitly mark those four open frontiers as **unsolved**.
