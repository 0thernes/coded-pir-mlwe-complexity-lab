<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Logged Literature Search & Prior-Art Verification (`docs/LITERATURE_SEARCH.md`)

Structured prior-art and retraction-screening log per the **Defensible Independent AI Research Playbook (v1.3, Items 15–16)**. Every bibliographic entry in `paper/refs.bib` is checked live against `doi.org` / `arxiv.org` / `eprint.iacr.org` AND screened for retractions via the Crossref Works API (`scripts/check_citations.py --online`).

## 1. Databases & Search Queries Audited (November 25–26, 2026)

| Pillar | Databases Queried | Key Search Terms | Primary Anchors Verified |
|---|---|---|---|
| **Pillar I (`CS-053` PIR & Non-Shannon Inequalities)** | arXiv (`cs.IT`), IEEE Xplore / Crossref, zbMATH | `"MDS coded PIR" "colluding" "Byzantine"`, `"LFSR" "colluding PIR"`, `"Sun" "Zhang" "2610.37412"`, `"Sun" "Tao" "2603.10769"`, `"Zhang-Yeung" "Ingleton" "Matus"`, `"linear rank inequalities" "6 variables" "Dougherty"` | `SunJafar2017`, `SunJafar2018`, `BanawanUlukus2018`, `BanawanUlukus2019`, `Tajeddine2019`, `Holzbaur2021`, `SunTaoXuZhang2026`, `SunZhang2026`, `ZhangYeung1998`, `Matus2007`, `Hammer1997`, `Kinser2011` |
| **Pillar II (`CS-026` MLWE, ML-KEM, Rényi, QGTL)** | NIST CSRC, IACR ePrint, arXiv (`cs.CR`, `quant-ph`), Crossref | `"FIPS 203" "ML-KEM" "CBD"`, `"Renyi divergence" "lattice cryptography" "Bai"`, `"Langlois Stehle" "Module-LWE"`, `"Chen" "2024/555" "Step 9"`, `"Luo" "2604.15858"`, `"quantum geometric tensor" "Provost Vallee"` | `FIPS203`, `LangloisStehle2015`, `Bai2018`, `Chen2024`, `Luo2026`, `Regev2009`, `Peikert2016`, `ProvostVallee1980` |
| **Pillar III (`CS-001/004/012/051`, `CS-CMP-012`)** | arXiv (`cs.CC`, `math.CO`), Crossref, MathSciNet / zbMATH | `"Algebrization" "Aaronson Wigderson"`, `"Natural Proofs" "Razborov Rudich"`, `"Katz Trevisan" "LDC"`, `"Koszul flattenings" "Landsberg Ottaviani"`, `"Winograd 1971" "2x2"`, `"Brockett Dobkin 1978"`, `"Blaser" "5/2" "FOCS 1999"`, `"Schwartz 1980" "Zippel 1979"`, `"Lovasz 1979" "Shannon capacity"`, `"Haemers 1979"`, `"Paley 1933"` | `AaronsonWigderson2009`, `RazborovRudich1997`, `KatzTrevisan2000`, `Shannon1949`, `Strassen1969`, `Winograd1971`, `BrockettDobkin1978`, `Blaser1999`, `LandsbergOttaviani2013`, `Schwartz1980`, `Zippel1979`, `Lovasz1979`, `Haemers1979`, `Paley1933` |

## 2. Novelty vs. Known-Literature Separation

To prevent accidental rediscovery claims, every theorem explicitly distinguishes **original constructions / discoveries** from **first-principles zero-Mathlib Lean 4 formalizations of foundational theorems**:

- **Repository Constructions, Certificates & Numerical Tables:**
  - Moment-vector annihilation & Pascal identity (`T1a`), closed-form rate comparison with Sun–Zhang's linear full-support-rank capacity (`T1b`, `T1g`, `T1h`; at $T=2$ reproducing `arXiv:2603.10769` Thm. IV.4), 90-matrix $\mathbb{F}_{11}$ inverse certificate (`T1c`), pure-integer `h_uncond` polymatroid & single $\mathbb{Z}_4$-cyclic $\mathbb{F}_2^{64}$ 6-subspace realization (`T1e`, `T1i`, `T1j`) backed by in-Lean `HasSpanDim` vector-space soundness (`T1k`, closing `L02`), field-universal linear flag-private PIR zero-error decoding + colluder-transcript bijection (`T1k`), and **unconditional in-kernel constructive existence over `SimpleField (Fin 101)` of the explicit $(6,3,3)$ rate-$10/17$ 20/20 zero-error witness (`T1l`, closing `S01`/`A02` inside all 6 Lean kernels; also cross-verified in Python & C11)**.
  - Elementary $q^m$ diagonal-product identity (`T2a`; records the $q$-ary MLWE basis determinant without refuting any published claim; note `arXiv:2604.15858` is Luo Part I on Weber's conjecture while the determinant-ideal step is in Part IV `arXiv:2605.17412`), anti-periodic & $m$-twisted DFT cancellation (`T2b`, `T2f`; proposed explanation of Chen 2024/555 Step 9, whose bug was found by Hongxun Wu and Thomas Vidick), integer covariance/variance inequalities (`T2d`, `T2e`, `T2g`), cleared-denominator Bai inequalities & branchless 8/9/10/14-bit `Dyadic-256`/`512`/`1024-A/B`/`16384-A/B` noise tables with 60-digit Rényi/Bai and 90-digit Kronecker-verified exact coupled FIPS 203 DFRs (`T2e`, `T2g`–`T2i`, closing `S02`), and exact NIST FIPS 203 Eq. (4.7) `Compress_1` (`T3d`).
  - Pure-integer $\{-1,0,+1\}$ 18-nnz Koszul flattening left-inverses & symbolic ALL-$m$ monomial left-inverse (`T3e`, `T3g`), and zero-reals $\mathbb{Z}[\sqrt{4k+1}]$ 2-block conference-matrix SOS proof of the conditional conference-graph bound (`T3j`, `T3l`, formalizing Lovász 1979 without floating-point SDP or real analysis).
- **Machine-Checked Zero-Mathlib Formalizations of Classical Foundations (Credited to Original Authors):**
  - Projective $\mathbb{P}^3$ concurrent/coplanar dichotomy (`T1f`), Zhang–Yeung 1998 & Matúš 2007 identities (`T1g`, `T1h`), multilinear-extension uniqueness (`T3a`), Natural Proofs counting step (`T3b`, Razborov–Rudich 1997), $B$-error-correcting code distance $2B+1$ & averaging bound (`T3c`, `T3f`), pigeonhole counting (`T3f`), Strassen 1969 / Winograd 1971 exact $\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$ (`T3h`), substitution lower bound $2m^2-m$ (`T3i`), **Markus Bläser (FOCS 1999, `10.1109/SFFCS.1999.814576`) characteristic-free $\frac{5}{2}m^2-3m$ matrix-multiplication lower bound over every field including $\mathbb{F}_2$ (`T3m`, surpassing Brockett–Dobkin $2m^2-1$ for all $m \ge 6$)**, Schwartz–Zippel 1979/1980 (`T3k`), Lovász 1979 & Haemers 1979 (`T3j`, `T3l`).

## 3. Automated Retraction Watch & DOI Resolution Audit

Run live via:
```bash
python scripts/check_citations.py --online
```
- **Total BibTeX entries:** 37/37 resolved HTTP 200 (`doi.org` handles, `arxiv.org`, `eprint.iacr.org`, `csrc.nist.gov`).
- **Crossref Retraction Audit:** **0 retractions** across all Crossref-indexed DOIs (`update-to`, `updated-by`, and `relation` fields checked programmatically).
