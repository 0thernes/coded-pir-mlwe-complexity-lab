<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# ADR 0003: Exterior-Power Koszul–Veronese Architecture for Flag-Private Coded Byzantine PIR

- **Status:** Accepted (2026-11-25)
- **Context:** Prior Linear Full-Support-Rank (LFSR) coded-colluding PIR schemes (Sun–Zhang 2026, `arXiv:2610.37412`) restrict each query block to full-support-rank structures, incurring excess interference dimension and requiring $E \ge KT$ to match unrestricted capacity.
- **Decision:** Adopt an exterior-power Koszul–Veronese query architecture grounded in moment-curve annihilation $\langle u(\alpha), e_{r+1}-\alpha e_r \rangle = 0$ and nested flag-privacy constraints. This yields exact Pascal interference savings $K\binom{T}{T'} = \lambda^\star + (K-T')\binom{T-1}{T'}$, strictly dominates the LFSR ceiling for all $K,T \ge 2$ (`T1b`), breaks the $E \ge KT$ barrier down to $E = K+1$ (`T1c`), and admits an explicit kernel-certified zero-error $\mathbb{F}_{11}$ Byzantine rate-$2/5$ instance.
- **Consequences:** Establishes a strictly higher achievable rate frontier for coded-colluding and Byzantine PIR while clearly delineating the remaining open non-linear $C(2,4,2,2) \in [3/5, 8/13]$ and $M \ge 3$ frontiers.
