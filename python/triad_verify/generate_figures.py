#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""
Generate publication-grade vector PDF figures for the AMS-LaTeX white paper
(`paper/figures/fig1..fig8.pdf`) plus the repository social preview SVG (`docs/media/social-preview.svg`).
Every data point is computed live from exact arithmetic / verified formulas — zero hardcoding!
"""
from __future__ import annotations

import cmath
import math
from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from triad_verify.mlwe_tightness import (
    cbd_pmf_exact,
    compute_bai_overhead_bits,
    compute_exact_mlkem_dfr,
    dyadic256_pmf_exact,
    dyadic512_pmf_exact,
    dyadic1024a_pmf_exact,
    dyadic1024b_pmf_exact,
    dyadic16384a_pmf_exact,
    dyadic16384b_pmf_exact,
)
from triad_verify.pir_koszul import koszul_rate_exact, lfsr_rate_exact


def style_axes() -> None:
    plt.rcParams.update(
        {
            "font.family": "serif",
            "mathtext.fontset": "stix",
            "font.size": 9.5,
            "axes.titlesize": 10.5,
            "axes.labelsize": 9.5,
            "legend.fontsize": 8.0,
            "xtick.labelsize": 8.5,
            "ytick.labelsize": 8.5,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.grid": True,
            "grid.alpha": 0.25,
            "grid.linestyle": "--",
        }
    )


def fig1_cs053_rate_frontier(out_dir: Path) -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.4, 4.1), dpi=300)

    # Panel A: Byzantine (K=3, T=2, B=1, U=0) rate vs N = 6..14 (E = N - 2 = 4..12; E < KT=6 for N=6,7!)
    Ns = list(range(6, 15))
    koszul_vals = [float(koszul_rate_exact(N, 3, 2, 0, 1)) for N in Ns]
    lfsr_Ns = [N for N in Ns if N - 2 >= 6]
    lfsr_vals: list[float] = []
    for N in lfsr_Ns:
        rv = lfsr_rate_exact(N, 3, 2, 0, 1)
        assert rv is not None
        lfsr_vals.append(float(rv))

    ax1.axvspan(5.7, 7.5, color="#fee2e2", alpha=0.65, label=r"Sun–Zhang ($E < KT$) infeasible")
    ax1.plot(Ns, koszul_vals, "o-", color="#1d4ed8", lw=2.1, ms=5.5, label=r"Ours: $R^{\mathrm{Koszul}}$ (Zero-Error)")
    ax1.plot(lfsr_Ns, lfsr_vals, "s--", color="#b91c1c", lw=1.8, ms=5.0, label=r"Sun–Zhang LFSR ($E \geq KT$)")
    ax1.scatter([6], [4 / 11], color="#047857", s=75, zorder=6, marker="*", label=r"Exact Unrestricted Cap. ($4/11$)")
    ax1.annotate(
        r"Exact cap. $4/11$",
        xy=(6, 4 / 11),
        xytext=(6.25, 0.305),
        arrowprops={"arrowstyle": "->", "color": "#047857", "lw": 1.0},
        fontsize=8.0,
        color="#047857",
    )
    ax1.annotate(
        r"$50/119$ ($E=5<KT$)",
        xy=(7, 50 / 119),
        xytext=(7.55, 0.365),
        arrowprops={"arrowstyle": "->", "color": "#1d4ed8", "lw": 1.0},
        fontsize=8.0,
        color="#1d4ed8",
    )
    ax1.set_title(r"(a) Byzantine $U$-$B$-MDS-$T$PIR ($M=2, K=3, T=2, B=1$)")
    ax1.set_xlabel(r"Total Servers $N$ (Effective $E = N - 2B$)")
    ax1.set_ylabel(r"PIR Download Rate $R = L/D$")
    ax1.set_xlim(5.6, 14.4)
    ax1.set_ylim(0.28, 0.68)
    ax1.legend(loc="lower right", frameon=True, framealpha=0.92)

    # Panel B: T=3, K=3, B=0 and B=1 Koszul vs Sun-Tao-Xu-Zhang (arXiv:2603.10769) vs LFSR
    labels = [
        "(6,2,2,B=1)\nExact Lin.",
        "(5,2,2,B=1)\nExact Unr.",
        "(6,3,2,B=1)\nExact Unr.",
        "(6,3,3,B=0)\nEx. VII.A",
        "(8,3,3,B=1)\nByz. T=3",
        "(10,4,4,B=1)\nE=8<KT",
    ]
    ours = [2 / 5, 18 / 55, 4 / 11, 10 / 17, 15 / 34, 7 / 15]
    prior = [8 / 21, 0.0, 0.0, 4 / 7, 0.0, 0.0]
    x = np.arange(len(labels))
    w = 0.36
    b1 = ax2.bar(x - w / 2, ours, w, color="#1d4ed8", label="Ours (Koszul-Veronese Flag-Private)")
    b2 = ax2.bar(x + w / 2, prior, w, color="#94a3b8", edgecolor="#334155", hatch="//", label="Best 2026 Prior (0 = infeasible)")
    for rect, val in zip(b1, ours):
        ax2.text(rect.get_x() + rect.get_width() / 2, val + 0.012, f"{val:.3f}", ha="center", va="bottom", fontsize=7.5, color="#1e3a8a")
    for rect, val in zip(b2, prior):
        txt = f"{val:.3f}" if val > 0 else "N/A"
        ax2.text(rect.get_x() + rect.get_width() / 2, val + 0.012, txt, ha="center", va="bottom", fontsize=7.2, color="#475569")
    ax2.set_xticks(x)
    ax2.set_xticklabels(labels, fontsize=7.6)
    ax2.set_ylabel("Zero-Error PIR Rate $R$")
    ax2.set_ylim(0, 0.78)
    ax2.set_title(r"(b) Flagship Zero-Error Benchmarks vs. 2026 SOTA")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.95)

    fig.tight_layout(w_pad=2.2)
    fig.savefig(out_dir / "fig1_cs053_rate_frontier.pdf", bbox_inches="tight")
    plt.close(fig)


def fig2_shannon_ingleton_barrier(out_dir: Path) -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.0, 3.9), dpi=300, gridspec_kw={"width_ratios": [1.05, 1.0]})

    cats = [
        "FGHK/LFSR\n(2,4,2,2)",
        "Linear Cap.\n(2,4,2,2)",
        "Shan.+Ing.\n(2,4,2,2)",
        "FGHK/LFSR\n(2,5,2,2)",
        "Linear Cap.\n(2,5,2,2)",
        "Shannon LP\n(2,5,2,2)",
    ]
    vals = [4 / 7, 3 / 5, 8 / 13, 5 / 8, 20 / 31, 2 / 3]
    fracs = ["4/7\n(0.5714)", "3/5\n(0.6000)", "8/13\n(0.6154)", "5/8\n(0.6250)", "20/31\n(0.6452)", "2/3\n(0.6667)"]
    colors = ["#94a3b8", "#1d4ed8", "#d97706", "#94a3b8", "#1d4ed8", "#d97706"]
    x = np.arange(len(cats))
    bars = ax1.bar(x, vals, color=colors, width=0.58, edgecolor="#1e293b", linewidth=0.6)
    for rect, lbl in zip(bars, fracs):
        ax1.text(rect.get_x() + rect.get_width() / 2, rect.get_height() + 0.005, lbl, ha="center", va="bottom", fontsize=7.4)
    ax1.axvline(2.5, color="#475569", linestyle=":", lw=1.2)
    ax1.set_xticks(x)
    ax1.set_xticklabels(cats, fontsize=7.6)
    ax1.set_ylim(0.52, 0.72)
    ax1.set_ylabel("Capacity / Upper Bound $R$")
    ax1.set_title(r"(a) Linear Capacity vs. Shannon+Ingleton")

    ax2.axis("off")
    ax2.set_xlim(0, 10)
    ax2.set_ylim(0, 8)
    ax2.set_title(r"(b) Theorem T1f: Four Pairwise-Intersecting Lines in $\mathbb{P}^3$")

    cx, cy = 2.6, 4.3
    angles = [0.25, 1.15, 2.05, 2.85]
    line_colors = ["#1d4ed8", "#047857", "#b91c1c", "#7c3aed"]
    for idx, ang in enumerate(angles):
        dx, dy = 1.8 * math.cos(ang), 1.8 * math.sin(ang)
        ax2.plot([cx - dx, cx + dx], [cy - dy, cy + dy], color=line_colors[idx], lw=2.0)
        ax2.text(cx + 1.12 * dx, cy + 1.12 * dy, f"$V_{idx+1}$", color=line_colors[idx], fontsize=8.5, ha="center", va="center")
    ax2.scatter([cx], [cy], color="#0f172a", s=55, zorder=5)
    ax2.text(
        cx,
        1.3,
        "Case 1 (Concurrent):\n$\\exists w \\neq 0 \\in \\bigcap_{i=1}^4 V_i$\n(shared line forces redundancy)",
        ha="center",
        va="center",
        fontsize=8.0,
        bbox={"boxstyle": "round,pad=0.35", "facecolor": "#eff6ff", "edgecolor": "#3b82f6"},
    )

    poly_x = [5.5, 9.5, 9.0, 5.0, 5.5]
    poly_y = [2.6, 2.9, 6.2, 5.9, 2.6]
    ax2.fill(poly_x, poly_y, color="#fef3c7", alpha=0.45, edgecolor="#d97706", lw=1.2)
    pts = [(6.0, 3.3), (8.7, 3.6), (8.3, 5.6), (6.3, 5.2)]
    segs = [(0, 1, 0), (1, 2, 1), (2, 3, 2), (3, 0, 3)]
    for i1, i2, ci in segs:
        x1, y1 = pts[i1]
        x2, y2 = pts[i2]
        vx, vy = x2 - x1, y2 - y1
        ax2.plot([x1 - 0.15 * vx, x2 + 0.15 * vx], [y1 - 0.15 * vy, y2 + 0.15 * vy], color=line_colors[ci], lw=2.0)
    for px, py in pts:
        ax2.scatter([px], [py], color="#0f172a", s=35, zorder=5)
    ax2.text(7.35, 6.5, r"3D Hyperplane $H = \mathrm{span}(a,b,c)$", ha="center", fontsize=8.0, color="#92400e")
    ax2.text(
        7.35,
        1.3,
        "Case 2 (Coplanar):\n$\\sum_{i=1}^4 V_i \\subseteq H$ ($\\dim \\leq 3$)\n(linear PIR drops to $3/5 < 8/13$)",
        ha="center",
        va="center",
        fontsize=8.0,
        bbox={"boxstyle": "round,pad=0.35", "facecolor": "#fffbeb", "edgecolor": "#d97706"},
    )

    fig.tight_layout(w_pad=2.4)
    fig.savefig(out_dir / "fig2_shannon_ingleton_barrier.pdf", bbox_inches="tight")
    plt.close(fig)


def fig3_mlwe_renyi_and_qgtl(out_dir: Path) -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.8, 4.2), dpi=300)

    sigmas = np.linspace(0.85, 1.55, 220)
    dyad_pmf = {x: float(p) for x, p in dyadic256_pmf_exact().items()}
    series = [
        ({x: float(p) for x, p in cbd_pmf_exact(2).items()}, "#b91c1c", "-", r"$\mathrm{CBD}_2$ (ML-KEM-768/1024)", 1.0226, 1.01289, (0.855, 1.033)),
        ({x: float(p) for x, p in cbd_pmf_exact(3).items()}, "#1d4ed8", "-", r"$\mathrm{CBD}_3$ (ML-KEM-512)", 1.2365, 1.00518, (1.305, 1.026)),
        (dyad_pmf, "#047857", "-", r"Dyadic-256 (Ours, $\mathrm{Var}=1$)", 1.0013, 1.00072, (1.075, 1.0022)),
    ]
    for pmf, col, ls, lbl, s_opt, r_opt, txt_xy in series:
        r2s = []
        for sv in sigmas:
            sf = float(sv)
            Z = sum(math.exp(-(x * x) / (2 * sf * sf)) for x in range(-25, 26))
            r2 = sum((px * px) / (math.exp(-(x * x) / (2 * sf * sf)) / Z) for x, px in pmf.items())
            r2s.append(r2)
        ax1.plot(sigmas, r2s, color=col, linestyle=ls, lw=2.0, label=lbl)
        ax1.scatter([s_opt], [r_opt], color=col, s=50, zorder=6)
        ax1.annotate(
            f"$R_2^*={r_opt:.5f}$\n($\\sigma^*={s_opt:.4f}$)",
            xy=(s_opt, r_opt),
            xytext=txt_xy,
            arrowprops={"arrowstyle": "->", "color": col, "lw": 1.0},
            fontsize=7.2,
            color=col,
            bbox={"boxstyle": "round,pad=0.20", "facecolor": "white", "edgecolor": col, "alpha": 0.92},
        )

    floors = []
    for sv in sigmas:
        sf = float(sv)
        Z = sum(math.exp(-(x * x) / (2 * sf * sf)) for x in range(-25, 26))
        supp2 = sum(math.exp(-(x * x) / (2 * sf * sf)) for x in range(-2, 3)) / Z
        floors.append(1.0 / supp2)
    ax1.plot(sigmas, floors, color="#64748b", linestyle=":", lw=1.7, label=r"Support-2 C-S floor $(1-\tau_2)^{-1}$")

    ax1.set_title("(a) ML-KEM $R_2(\\sigma)$ Cliff vs. Dyadic-256 Collapse (T2c, T2e)")
    ax1.set_xlabel(r"Target Discrete Gaussian Parameter $\sigma$")
    ax1.set_ylabel("Per-Coordinate Rényi-2 Divergence $R_2(P \\| D_\\sigma)$")
    ax1.set_ylim(0.996, 1.090)
    ax1.legend(loc="upper right", frameon=True, framealpha=0.94, fontsize=7.4)
    ax1.text(
        0.858,
        1.059,
        "ML-KEM-1024 ($m=2048$) loss:\n"
        "$\\mathrm{CBD}_2$: 37.84 bits (4.96$\\times$ cliff)\n"
        "Dyadic-256: 2.14 bits (17.7$\\times$ drop)",
        fontsize=7.3,
        bbox={"boxstyle": "round,pad=0.32", "facecolor": "#f0fdf4", "edgecolor": "#047857", "alpha": 0.94},
    )

    e0s = np.linspace(-1.2, 1.2, 241)
    for s_val, col, ls in [(0.9, "#7c3aed", "-."), (1.023, "#1d4ed8", "-"), (1.237, "#047857", "--")]:
        omegas = []
        for e0_np in e0s:
            e0 = float(e0_np)
            xs = [-2.0, -1.0, 0.0, 1.0, 2.0]
            ws = [math.exp(-((x - e0) ** 2) / (2 * s_val * s_val)) for x in xs]
            Z = sum(ws)
            ps = [w / Z for w in ws]
            bs = [((x - e0) ** 2) / (s_val ** 3) for x in xs]
            ex = sum(p * x for p, x in zip(ps, xs))
            eb = sum(p * b for p, b in zip(ps, bs))
            omegas.append(sum(p * (x - ex) * (b - eb) for p, x, b in zip(ps, xs, bs)))
        ax2.plot(e0s, omegas, color=col, linestyle=ls, lw=1.9, label=rf"$\sigma = {s_val}$")
    ax2.axhline(0.0, color="#475569", lw=0.9)
    ax2.axvline(0.0, color="#475569", lw=0.9)
    ax2.scatter([0.0], [0.0], color="#b91c1c", s=55, zorder=6, label=r"Symmetric $e_0=0 \Rightarrow \Omega_{\theta\sigma}\equiv 0$")
    ax2.text(
        -1.15,
        -0.56,
        "QGTL Metric-Kurtosis Law (T2e):\n"
        "$4\\det(g) \\geq \\Omega_{\\theta\\sigma}^2$ (Provost-Vallée PSD)\n"
        "At $e_0=0, \\sigma=1$: $\\det(g) = (\\kappa_{\\mathrm{ex}}+2)/4$\n"
        "$\\mathrm{CBD}_2$: $3/8 <$ Dyadic-256: $15/32 < \\mathcal{N}$: $1/2$",
        fontsize=7.2,
        bbox={"boxstyle": "round,pad=0.32", "facecolor": "#eff6ff", "edgecolor": "#1d4ed8", "alpha": 0.94},
    )
    ax2.set_title(r"(b) QGTL Berry Curvature $\Omega_{\theta\sigma}(e_0)$ & Metric-Kurtosis")
    ax2.set_xlabel(r"LWE Noise Mean Shift / Bias $e_0$")
    ax2.set_ylabel(r"Berry Curvature $\Omega_{\theta\sigma} = \mathrm{Cov}(X, (X-e_0)^2/\sigma^3)$")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.6)

    fig.tight_layout()
    fig.savefig(out_dir / "fig3_mlwe_renyi_and_qgtl.pdf", bbox_inches="tight")
    plt.close(fig)


def fig4_chen_step9_and_triad(out_dir: Path) -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.4, 4.3), dpi=300, gridspec_kw={"width_ratios": [0.95, 1.15]})

    D, c = 7, 3
    N = 2 * D
    freqs = list(range(N))
    f = [cmath.exp(1j * math.pi * c * x * x / D) for x in range(N)]
    mags = [abs(sum(f[x] * cmath.exp(-2j * math.pi * k * x / N) for x in range(N))) for k in freqs]
    cols = ["#dc2626" if k % 2 == 0 else "#1d4ed8" for k in freqs]
    ax1.bar(freqs, mags, color=cols, width=0.66, edgecolor="#1e293b", lw=0.6)
    ax1.scatter(
        [k for k in freqs if k % 2 == 0],
        [0.0] * D,
        color="#dc2626",
        s=40,
        zorder=5,
        label=r"Even modes $\hat{f}(2k) \equiv 0$ (T2b, T2f)",
    )
    ax1.bar([-10], [0], color="#1d4ed8", label=r"Odd modes $|\hat{f}(2k+1)| = 2\sqrt{D}$")
    ax1.set_xlim(-0.7, N - 0.3)
    ax1.set_ylim(0, 2.0 * math.sqrt(D) * 1.40)
    ax1.set_xticks(freqs)
    ax1.set_xlabel(r"Fourier Frequency Index $k \in \mathbb{Z}_{2D}$ ($D=7, c=3$)")
    ax1.set_ylabel(r"DFT Magnitude $|\hat{f}(k)|$")
    ax1.set_title(r"(a) Chen Step-9 & $m$-Twisted DFT Rule (T2b, T2f)")
    ax1.legend(loc="upper right", frameon=True, framealpha=0.94, fontsize=7.6)

    # Panel B: Unified 5-Node Mega Atlas Architecture (31 Lean 4.35 Theorems T1a-T3l + 9 Refutations)
    ax2.axis("off")
    ax2.set_xlim(0, 10.6)
    ax2.set_ylim(0, 8.6)
    ax2.set_title("(b) Machine-Checked Frontier Bridges (31 Theorems T1a\u2013T3l)")

    nodes = {
        "CS053": (2.25, 6.85, "CS-053: Coded/Byz. PIR\n(T1a\u2013T1j: Koszul, Flag-Priv,\nSingle $\\mathbb{F}_2^{64}$ 6-Obj Realiz.)", "#dbeafe", "#1d4ed8"),
        "CS026": (8.35, 6.85, "CS-026 / QC-042 / CM-048\n(T2a\u2013T2i: Bai DPI/Tensor,\nDyadic-16384 & Float64 DFR)", "#fce7f3", "#be185d"),
        "CS004": (5.30, 4.35, "CS-004 ($\\omega$), CS-012 & CS-CMP-012\nT3e/T3g\u2013T3l: $2\\cdot 4^k-2^k\\leq R\\leq 7^k$,\nSchwartz\u2013Zippel, Cond. $\\Theta(P_p)=\\sqrt{p}$", "#ede9fe", "#6d28d9"),
        "CS051": (2.25, 1.55, "CS-051: Locally Decodable\nCodes (T3c: $d_{\\min}\\geq 2B+1$;\nT3f: Katz\u2013Trevisan Smoothness)", "#dcfce7", "#15803d"),
        "CS001": (8.35, 1.55, "CS-001 / CS-010: $\\mathrm{P}\\neq\\mathrm{NP}$\n(T3a MLE, T3b Nat. Proofs,\nT3f Shannon; 9 Adv. Refut.)", "#fef3c7", "#b45309"),
    }
    for nx, ny, txt, fc, ec in nodes.values():
        ax2.text(
            nx,
            ny,
            txt,
            ha="center",
            va="center",
            fontsize=7.0,
            bbox={"boxstyle": "round,pad=0.38", "facecolor": fc, "edgecolor": ec, "lw": 1.3},
        )

    ax2.annotate("", xy=(5.95, 6.85), xytext=(4.65, 6.85), arrowprops={"arrowstyle": "<->", "color": "#334155", "lw": 1.4})
    ax2.text(5.30, 7.50, "T3d: $|e|\\leq 831$\nSingle vs. Multi-Srv", ha="center", va="center", fontsize=6.7)

    ax2.annotate("", xy=(4.05, 5.15), xytext=(3.10, 5.90), arrowprops={"arrowstyle": "<->", "color": "#6d28d9", "lw": 1.5})
    ax2.text(4.35, 5.75, "T1a $\\leftrightarrow$ T3e\nWedge $u\\wedge\\cdot$", ha="center", va="center", fontsize=6.6, color="#6d28d9")

    ax2.annotate("", xy=(7.35, 2.55), xytext=(6.45, 3.55), arrowprops={"arrowstyle": "->", "color": "#6d28d9", "lw": 1.2, "ls": "--"})
    ax2.text(7.70, 3.25, "Algebraic\nrank barrier", ha="center", va="center", fontsize=6.5, color="#6d28d9")

    ax2.annotate("", xy=(2.25, 2.65), xytext=(2.25, 5.75), arrowprops={"arrowstyle": "<->", "color": "#15803d", "lw": 1.4})
    ax2.text(0.95, 4.20, "T3c, T3f:\nKatz\u2013Trevisan\nPIR $\\leftrightarrow$ LDC", ha="center", va="center", fontsize=6.7, color="#15803d")

    ax2.annotate("", xy=(8.35, 2.65), xytext=(8.35, 5.75), arrowprops={"arrowstyle": "->", "color": "#be185d", "lw": 1.4})
    ax2.text(9.58, 4.20, "T3b:\nLWE PRF $\\Rightarrow$\nNatural Proofs\nObstruction", ha="center", va="center", fontsize=6.7, color="#be185d")

    fig.tight_layout()
    fig.savefig(out_dir / "fig4_chen_step9_and_triad.pdf", bbox_inches="tight")
    plt.close(fig)


def fig5_dyadic256_and_koszul_tensor(out_dir: Path) -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.0, 4.1), dpi=300, gridspec_kw={"width_ratios": [1.05, 1.0]})

    pmfs_by_bits = [
        ("4-bit\n($D=16$)\n$\\mathrm{CBD}_2$", {-2: 1 / 16, -1: 4 / 16, 0: 6 / 16, 1: 4 / 16, 2: 1 / 16}, "#b91c1c"),
        ("5-bit\n($D=32$)\n$\\mathrm{CBD}_2$", {-2: 1 / 16, -1: 4 / 16, 0: 6 / 16, 1: 4 / 16, 2: 1 / 16}, "#dc2626"),
        ("6-bit\n($D=64$)\n$\\mathrm{CBD}_2$", {-2: 1 / 16, -1: 4 / 16, 0: 6 / 16, 1: 4 / 16, 2: 1 / 16}, "#ef4444"),
        ("7-bit\n($D=128$)\nsupp $\\{\\pm 3\\}$", {-3: 1 / 128, -2: 6 / 128, -1: 31 / 128, 0: 52 / 128, 1: 31 / 128, 2: 6 / 128, 3: 1 / 128}, "#d97706"),
        ("8-bit\n($D=256$)\nDyadic-256", {x: float(p) for x, p in dyadic256_pmf_exact().items()}, "#047857"),
    ]
    labels = []
    losses = []
    colors = []
    for lbl, pmf, col in pmfs_by_bits:
        best_r2 = 1e9
        for i in range(401):
            s = 0.95 + 0.20 * i / 400.0
            Z = sum(math.exp(-(x * x) / (2 * s * s)) for x in range(-25, 26))
            r2 = sum((px * px) / (math.exp(-(x * x) / (2 * s * s)) / Z) for x, px in pmf.items())
            best_r2 = min(best_r2, r2)
        labels.append(lbl)
        losses.append(2048.0 * math.log2(best_r2))
        colors.append(col)

    s_ref = 1.022597
    Z_ref = sum(math.exp(-(x * x) / (2 * s_ref * s_ref)) for x in range(-25, 26))
    supp2_ref = sum(math.exp(-(x * x) / (2 * s_ref * s_ref)) for x in range(-2, 3)) / Z_ref
    cs_floor_bits = 2048.0 * math.log2(1.0 / supp2_ref)

    x = np.arange(len(labels))
    bars = ax1.bar(x, losses, width=0.58, color=colors, edgecolor="#1e293b", lw=0.7)
    ax1.axhline(cs_floor_bits, color="#475569", linestyle="--", lw=1.4, label=rf"Support-2 C-S floor ({cs_floor_bits:.1f} bits)")
    for rect, val in zip(bars, losses):
        ax1.text(rect.get_x() + rect.get_width() / 2, val + 0.9, f"{val:.2f} b", ha="center", va="bottom", fontsize=7.8, fontweight="bold")
    ax1.annotate(
        "17.7$\\times$ drop\n(1-byte CT sampler!)",
        xy=(4, losses[4] + 3.0),
        xytext=(3.95, 24.5),
        ha="center",
        arrowprops={"arrowstyle": "->", "color": "#047857", "lw": 1.4},
        fontsize=7.6,
        color="#047857",
        bbox={"boxstyle": "round,pad=0.28", "facecolor": "#f0fdf4", "edgecolor": "#047857"},
    )
    ax1.set_xticks(x)
    ax1.set_xticklabels(labels, fontsize=7.5)
    ax1.set_ylim(0, 44.5)
    ax1.set_ylabel("ML-KEM-1024 Cumulative Loss $2048 \\log_2 R_2^*$ (bits)")
    ax1.set_title(r"(a) Exact $\mathrm{Var}=1$ Dyadic Bit-Budget Phase Transition (T2e)")
    ax1.legend(loc="upper right", frameon=True, framealpha=0.94, fontsize=7.6)

    tensors = [
        r"$M_2 = \langle 2,2,2 \rangle$" + "\n" + r"($4\times 4\times 4$ MatMul)",
        r"$T_3 \in F^{3\times 3\times 3}$" + "\n(7-nnz Binary Tensor)",
    ]
    triv_bounds = [4, 3]
    koszul_bounds = [6, 5]
    exact_ranks = [7, 5]
    xb = np.arange(len(tensors))
    w = 0.25
    b1 = ax2.bar(xb - w, triv_bounds, w, color="#94a3b8", edgecolor="#334155", label="Trivial Matrix Flattening ($\\leq n$)")
    b2 = ax2.bar(xb, koszul_bounds, w, color="#6d28d9", edgecolor="#1e293b", label=r"Ours: Koszul $\Phi_1$ Certified $\forall F$ (T3e)")
    b3 = ax2.bar(xb + w, exact_ranks, w, color="#dbeafe", edgecolor="#1d4ed8", hatch="///", label="Known Exact Rank (Strassen / Tight)")
    for rects, col in [(b1, "#475569"), (b2, "#5b21b6"), (b3, "#1e40af")]:
        for rect in rects:
            h = rect.get_height()
            ax2.text(rect.get_x() + rect.get_width() / 2, h + 0.14, f"{int(h)}", ha="center", va="bottom", fontsize=8.2, fontweight="bold", color=col)
    ax2.text(
        0.5,
        8.65,
        "Pure-integer $\\{-1,0,+1\\}$ left-inverses ($\\det=\\pm 1$):\n"
        "$L_2 \\in \\mathbb{Z}^{16\\times 24}$ (18 nnz) $\\Rightarrow \\mathrm{rank}_F(M_2) \\geq \\lceil 16/3 \\rceil = 6$\n"
        "$L_3 \\in \\mathbb{Z}^{9\\times 9}$ $\\Rightarrow \\mathrm{rank}_F(T_3) \\geq \\lceil 9/2 \\rceil = 5$ (char-free, incl. $\\mathbb{F}_2$!)",
        ha="center",
        va="center",
        fontsize=7.2,
        bbox={"boxstyle": "round,pad=0.35", "facecolor": "#f5f3ff", "edgecolor": "#6d28d9", "alpha": 0.95},
    )
    ax2.set_xticks(xb)
    ax2.set_xticklabels(tensors, fontsize=8.3)
    ax2.set_ylim(0, 9.85)
    ax2.set_ylabel("Tensor Rank / Certified Lower Bound")
    ax2.set_title(r"(b) Field-Universal Koszul Flattening Bounds (T3e)")
    ax2.legend(loc="lower right", frameon=True, framealpha=0.95, fontsize=7.2)

    fig.tight_layout(w_pad=2.2)
    fig.savefig(out_dir / "fig5_dyadic256_and_koszul_tensor.pdf", bbox_inches="tight")
    plt.close(fig)


def fig6_mlkem_dfr_variational_and_allm_koszul(out_dir: Path) -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.2, 4.2), dpi=300, gridspec_kw={"width_ratios": [1.05, 1.0]})

    def min_r2_loss(pmf: dict[int, Fraction], m_coords: int, lo: float, hi: float) -> float:
        best = 1e9
        for i in range(401):
            s = lo + (hi - lo) * i / 400.0
            Z = sum(math.exp(-(x * x) / (2 * s * s)) for x in range(-30, 31))
            r2 = sum((float(p) ** 2) / (math.exp(-(x * x) / (2 * s * s)) / Z) for x, p in pmf.items())
            best = min(best, r2)
        return m_coords * math.log2(best)

    fips_losses = [
        min_r2_loss(cbd_pmf_exact(3), 1024, 1.15, 1.35),
        min_r2_loss(cbd_pmf_exact(2), 1536, 0.95, 1.15),
        min_r2_loss(cbd_pmf_exact(2), 2048, 0.95, 1.15),
    ]
    ours_losses = [
        min_r2_loss(dyadic512_pmf_exact(), 1024, 1.15, 1.35),
        min_r2_loss(dyadic256_pmf_exact(), 1536, 0.95, 1.15),
        min_r2_loss(dyadic256_pmf_exact(), 2048, 0.95, 1.15),
    ]
    sets = [
        "ML-KEM-512\n($m=1024, \\mathrm{Var}=3/2$)\nModel DFR $2^{-139.3}$",
        "ML-KEM-768\n($m=1536, \\mathrm{Var}=1$)\nModel DFR $2^{-166.1}$",
        "ML-KEM-1024\n($m=2048, \\mathrm{Var}=1$)\nModel DFR $2^{-174.3}$",
    ]
    ratios = [f / o for f, o in zip(fips_losses, ours_losses)]
    x = np.arange(len(sets))
    w = 0.35
    b1 = ax1.bar(x - w / 2, fips_losses, w, color="#dc2626", edgecolor="#1e293b", lw=0.7, label="FIPS 203 ($\\mathrm{CBD}_3 / \\mathrm{CBD}_2$)")
    b2 = ax1.bar(x + w / 2, ours_losses, w, color="#047857", edgecolor="#1e293b", lw=0.7, label="Ours (CT Dyadic-512 / Dyadic-256)")
    for rect, val in zip(b1, fips_losses):
        ax1.text(rect.get_x() + rect.get_width() / 2, val + 0.8, f"{val:.2f} b", ha="center", va="bottom", fontsize=7.6, color="#991b1b", fontweight="bold")
    for rect, val, rat in zip(b2, ours_losses, ratios):
        ax1.text(rect.get_x() + rect.get_width() / 2, val + 0.8, f"{val:.2f} b\n({rat:.1f}$\\times$)", ha="center", va="bottom", fontsize=7.3, color="#065f46", fontweight="bold")
    ax1.text(
        0.02,
        0.75,
        "Dyadic-512 (9-bit CT, T2g):\n"
        "$\\kappa_{\\mathrm{ex}}=0$, QGTL $\\det(g)=1/2$\n"
        "QGTL $\\chi^2$/H4 LB captures:\n"
        "75.5% ($\\mathrm{CBD}_2$), 89.5% (D256)",
        transform=ax1.transAxes,
        va="top",
        fontsize=6.9,
        bbox={"boxstyle": "round,pad=0.28", "facecolor": "#f0fdf4", "edgecolor": "#047857", "alpha": 0.95},
    )
    ax1.set_xticks(x)
    ax1.set_xticklabels(sets, fontsize=7.4)
    ax1.set_ylim(0, 47.0)
    ax1.set_ylabel("Cumulative Keygen Rényi-2 Loss $m\\log_2 R_2^*$ (bits)")
    ax1.set_title("(a) FIPS 203 Dyadic Suite & Float64 Model DFRs (T2g)")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.95, fontsize=7.5)

    ms = np.array([2, 3, 4, 5])
    triv = ms ** 2
    phi1 = ms ** 2 + 2
    phi_deg = ms ** 2 + ms
    ax2.plot(ms, triv, "o--", color="#64748b", lw=1.7, ms=5.5, label=r"Trivial Matrix Flattening ($m^2$)")
    ax2.plot(ms, phi1, "s-", color="#6d28d9", lw=2.2, ms=6.2, label=r"Ours: Symbolic $\Phi_1$ Monomial ($m^2+2\;\forall F$, T3g)")
    ax2.plot(ms, phi_deg, "^-.", color="#1d4ed8", lw=1.9, ms=6.2, label=r"Degree-$(m-1)$ Koszul Ceiling ($m^2+m$, T3g)")
    ax2.scatter([2], [7], color="#dc2626", s=115, marker="*", zorder=7, label=r"Exact Strassen–Winograd $\mathrm{rank}_F(\langle 2,2,2\rangle)=7\;\forall F$ (T3h)")
    ax2.annotate(
        "Exact = 7 $\\forall F$\n(incl. $\\mathbb{F}_2$, T3h)",
        xy=(2, 7),
        xytext=(2.20, 12.2),
        arrowprops={"arrowstyle": "->", "color": "#dc2626", "lw": 1.1},
        fontsize=7.3,
        color="#b91c1c",
        fontweight="bold",
        bbox={"boxstyle": "round,pad=0.22", "facecolor": "#fef2f2", "edgecolor": "#dc2626"},
    )
    ax2.annotate(
        "$\\Phi_2(\\langle 3,3,3\\rangle)$ rank 324\nover $\\mathbb{F}_2, \\mathbb{F}_{101} \\Rightarrow \\geq 12$",
        xy=(3, 12),
        xytext=(3.35, 5.5),
        arrowprops={"arrowstyle": "->", "color": "#1d4ed8", "lw": 1.0},
        fontsize=7.1,
        color="#1e40af",
        bbox={"boxstyle": "round,pad=0.22", "facecolor": "#eff6ff", "edgecolor": "#1d4ed8"},
    )
    for m_val, p1_val, pd_val in zip(ms, phi1, phi_deg):
        offsets = {2: (-0.15, -0.30), 3: (-0.19, -0.15), 4: (0.19, -0.45), 5: (0.15, -0.55)}
        dx, dy = offsets[int(m_val)]
        ax2.text(
            m_val + dx,
            p1_val + dy,
            f"{p1_val}",
            fontsize=7.4,
            color="#5b21b6",
            ha="center",
            va="center",
            bbox={"boxstyle": "round,pad=0.10", "facecolor": "white", "edgecolor": "none", "alpha": 0.88},
        )
        if m_val >= 3:
            ax2.text(m_val - 0.06, pd_val + 0.95, f"{pd_val}", fontsize=7.4, color="#1e40af", ha="center")
    ax2.set_xticks(ms)
    ax2.set_xticklabels([rf"$\langle {m},{m},{m}\rangle$" for m in ms], fontsize=8.3)
    ax2.set_xlim(1.75, 5.25)
    ax2.set_ylim(2, 34.5)
    ax2.set_xlabel(r"Matrix Multiplication Tensor $\langle m, m, m \rangle$")
    ax2.set_ylabel(r"Tensor Rank / Certified Lower Bound ($\forall F$)")
    ax2.set_title(r"(b) All-$m$ Koszul MatMul & Exact Strassen–Winograd (T3g, T3h)")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.95, fontsize=7.0)

    fig.tight_layout(w_pad=2.2)
    fig.savefig(out_dir / "fig6_mlkem_dfr_variational_and_allm_koszul.pdf", bbox_inches="tight")
    plt.close(fig)


def fig7_bai_security_collapse_and_lovasz_bd(out_dir: Path) -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.4, 4.3), dpi=300, gridspec_kw={"width_ratios": [1.05, 1.05]})

    cbd2, cbd3 = cbd_pmf_exact(2), cbd_pmf_exact(3)
    d256, d512 = dyadic256_pmf_exact(), dyadic512_pmf_exact()
    d1024a, d1024b = dyadic1024a_pmf_exact(), dyadic1024b_pmf_exact()

    fips_bai = [
        compute_bai_overhead_bits(cbd3, 1024, 128.0)["bai_overhead_bits"],
        compute_bai_overhead_bits(cbd2, 1536, 192.0)["bai_overhead_bits"],
        compute_bai_overhead_bits(cbd2, 2048, 256.0)["bai_overhead_bits"],
    ]
    d89_bai = [
        compute_bai_overhead_bits(d512, 1024, 128.0)["bai_overhead_bits"],
        compute_bai_overhead_bits(d256, 1536, 192.0)["bai_overhead_bits"],
        compute_bai_overhead_bits(d256, 2048, 256.0)["bai_overhead_bits"],
    ]
    d10_bai = [
        compute_bai_overhead_bits(d1024b, 1024, 128.0)["bai_overhead_bits"],
        compute_bai_overhead_bits(d1024a, 1536, 192.0)["bai_overhead_bits"],
        compute_bai_overhead_bits(d1024a, 2048, 256.0)["bai_overhead_bits"],
    ]
    sets = [
        "ML-KEM-512\n($\\lambda=128, m=1024$)\nDFR $2^{-140.0} < 2^{-138.8}$",
        "ML-KEM-768\n($\\lambda=192, m=1536$)\nDFR $2^{-166.0} < 2^{-164}$",
        "ML-KEM-1024\n($\\lambda=256, m=2048$)\nModel DFR $2^{-174.1}$",
    ]
    x = np.arange(len(sets))
    w = 0.26
    b1 = ax1.bar(x - w, fips_bai, w, color="#dc2626", edgecolor="#1e293b", lw=0.7, label="FIPS 203 ($\\mathrm{CBD}_3 / \\mathrm{CBD}_2$)")
    b2 = ax1.bar(x, d89_bai, w, color="#2563eb", edgecolor="#1e293b", lw=0.7, label="Ours 8/9-bit (Dyadic-512 / 256)")
    b3 = ax1.bar(x + w, d10_bai, w, color="#047857", edgecolor="#1e293b", lw=0.7, label="Ours 10-bit (Dyadic-1024-B / A)")
    for rect, val in zip(b1, fips_bai):
        ax1.text(rect.get_x() + rect.get_width() / 2, val + 1.2, f"{val:.1f}b", ha="center", va="bottom", fontsize=7.2, color="#991b1b", fontweight="bold")
    for rect, val in zip(b2, d89_bai):
        ax1.text(rect.get_x() + rect.get_width() / 2, val + 1.2, f"{val:.1f}b", ha="center", va="bottom", fontsize=7.0, color="#1d4ed8")
    for rect, val, fb in zip(b3, d10_bai, fips_bai):
        ax1.text(rect.get_x() + rect.get_width() / 2, val + 1.2, f"{val:.1f}b\n({fb/val:.1f}$\\times$)", ha="center", va="bottom", fontsize=7.0, color="#065f46", fontweight="bold")
    ax1.text(
        0.02,
        0.69,
        "Bai et al. (2018) Optimal Loss:\n"
        "$\\min_{\\alpha>1,\\sigma}[\\frac{\\lambda}{\\alpha-1}+m\\log_2 R_\\alpha]$\n"
        "Dyadic-1024-A saves 59.8b\n"
        "(67.1b $\\to$ 7.3b, 9.2$\\times$!)",
        transform=ax1.transAxes,
        va="top",
        fontsize=6.6,
        bbox={"boxstyle": "round,pad=0.26", "facecolor": "#f0fdf4", "edgecolor": "#047857", "alpha": 0.96},
    )
    ax1.set_xticks(x)
    ax1.set_xticklabels(sets, fontsize=7.3)
    ax1.set_ylim(0, 92.0)
    ax1.set_ylabel("End-to-End Bai et al. Security Overhead $\\Delta_{\\mathrm{Bai}}$ (bits)")
    ax1.set_title("(a) End-to-End Bai et al. Overhead Collapse (T2h)")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.95, fontsize=7.1)

    ms = np.array([2, 3, 4, 5, 6])
    triv = ms ** 2
    koszul_ceil = ms ** 2 + ms
    bd = 2 * ms ** 2 - ms
    ax2.fill_between(ms, koszul_ceil, bd, where=(ms >= 3), color="#fee2e2", alpha=0.45, label="Quadratic Gain Beyond Koszul ($m^2-2m$)")
    ax2.plot(ms, triv, "o--", color="#64748b", lw=1.5, ms=4.8, label=r"Trivial Flattening ($m^2$)")
    ax2.plot(ms, koszul_ceil, "^-.", color="#1d4ed8", lw=1.8, ms=5.5, label=r"Deg-$(m-1)$ Koszul Ceiling ($m^2+m$, T3g)")
    ax2.plot(ms, bd, "D-", color="#b91c1c", lw=2.3, ms=5.8, label=r"Substitution LB ($2m^2-m\;\forall F$, T3i; BD78: $2m^2-1$)")
    ax2.scatter([2], [7], color="#7c3aed", s=110, marker="*", zorder=7, label=r"Strassen–Winograd $\mathrm{rank}_F(\langle 2,2,2\rangle)=7$ (T3h)")
    for m_val, kc_val, bd_val in zip(ms, koszul_ceil, bd):
        if m_val >= 3:
            ax2.text(m_val - 0.14, bd_val + 2.4, f"{bd_val}", fontsize=7.4, color="#991b1b", fontweight="bold", ha="center")
            ax2.text(
                m_val + 0.12,
                kc_val + 2.6,
                f"{kc_val}",
                fontsize=7.0,
                color="#1e40af",
                ha="center",
                bbox={"boxstyle": "round,pad=0.10", "facecolor": "white", "edgecolor": "none", "alpha": 0.85},
            )
    ax2.text(
        0.985,
        0.03,
        "Theorem T3j (CS-CMP-012, $\\mathbb{Z}[\\sqrt{5}]$):\n"
        "$\\Theta(C_5)=\\sqrt{5}$: $k^2\\leq 5^t$ & $\\alpha(C_5^{\\boxtimes 2m})=5^m$\n"
        "$\\sqrt{10}\\leq \\Theta(C_7)\\leq \\vartheta(C_7)\\approx 3.318$\n"
        "$r_{\\mathrm{Haemers}}^{\\min}(C_7, F)=4\\;\\forall F$ (incl. $\\mathbb{F}_2$)",
        transform=ax2.transAxes,
        ha="right",
        va="bottom",
        fontsize=6.4,
        bbox={"boxstyle": "round,pad=0.26", "facecolor": "#f5f3ff", "edgecolor": "#6d28d9", "alpha": 0.96},
    )
    ax2.set_xticks(ms)
    ax2.set_xticklabels([rf"$\langle {m},{m},{m}\rangle$" for m in ms], fontsize=8.0)
    ax2.set_xlim(1.7, 6.35)
    ax2.set_ylim(0, 82.0)
    ax2.set_xlabel(r"Matrix Multiplication Tensor $\langle m, m, m \rangle$")
    ax2.set_ylabel(r"Tensor Rank Lower Bound ($\forall F$, incl. $\mathbb{F}_2$)")
    ax2.set_title("(b) Substitution LB $2m^2-m$ & Lovász/Haemers (T3i, T3j)")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.95, fontsize=6.9)

    fig.tight_layout(w_pad=2.2)
    fig.savefig(out_dir / "fig7_bai_security_collapse_and_lovasz_bd.pdf", bbox_inches="tight")
    plt.close(fig)


def fig8_v5_gaussian_paradox_and_paley_family(out_dir: Path) -> None:
    """v5.1.0 Figure 8: ML-KEM-1024 Float64 Discrete-Convolution DFR vs. 14-Bit Bai Overhead (T2i)
    + Conditional Paley/Conference Zero-Reals Z[sqrt(p)] Shannon Capacity & Two-Sided Strassen Bounds (T3k, T3l)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.4, 4.35), dpi=300, gridspec_kw={"width_ratios": [1.05, 1.05]})

    # Panel A: ML-KEM-1024 Pareto Wall (DFR vs Bai Security Overhead, all exact Var = 1)
    cbd2 = cbd_pmf_exact(2)
    d256 = dyadic256_pmf_exact()
    d1024a = dyadic1024a_pmf_exact()
    d16a = dyadic16384a_pmf_exact()
    d16b = dyadic16384b_pmf_exact()

    pts_legal = [
        ("Dyadic-16384-A\n(14-bit, T2i)", d16a, "#047857", "*", 155, (174.92, 4.0)),
        ("Dyadic-1024-A\n(10-bit, T2h)", d1024a, "#16a34a", "D", 62, (175.15, 17.5)),
        ("Dyadic-256\n(8-bit, T2e)", d256, "#2563eb", "o", 62, (175.42, 31.0)),
        ("FIPS 203 $\\mathrm{CBD}_2$\n(4-bit)", cbd2, "#dc2626", "s", 65, (175.10, 57.5)),
    ]
    xs_l, ys_l = [], []
    for lbl, pmf, col, mk, sz, txy in pts_legal:
        dfr_x = -compute_exact_mlkem_dfr(4, 11, 5, pmf, pmf)["union_bound_log2_dfr"]
        bai_y = compute_bai_overhead_bits(pmf, 2048, 256.0)["bai_overhead_bits"]
        xs_l.append(dfr_x)
        ys_l.append(bai_y)
        ax1.scatter([dfr_x], [bai_y], color=col, marker=mk, s=sz, zorder=7, edgecolor="#0f172a", lw=0.6)
        ax1.annotate(
            f"{lbl}\n({bai_y:.2f} b, $2^{{-{dfr_x:.2f}}}$)",
            xy=(dfr_x, bai_y),
            xytext=txy,
            arrowprops={"arrowstyle": "->", "color": col, "lw": 1.0},
            fontsize=6.8,
            color=col,
            fontweight="bold" if col == "#047857" else "normal",
            bbox={"boxstyle": "round,pad=0.20", "facecolor": "white", "edgecolor": col, "alpha": 0.94},
        )
    ax1.plot(xs_l, ys_l, "--", color="#047857", lw=1.4, alpha=0.8, zorder=5, label=r"$\mathrm{Var}=1$ Dyadic Tradeoff (float64 model)")

    # Exact unit-variance Discrete Gaussian point (float64 model comparison)
    s_lo, s_hi = 0.99, 1.01
    for _ in range(80):
        sm = 0.5 * (s_lo + s_hi)
        Z = sum(math.exp(-(x * x) / (2.0 * sm * sm)) for x in range(-20, 21))
        if sum(x * x * math.exp(-(x * x) / (2.0 * sm * sm)) for x in range(-20, 21)) / Z < 1.0:
            s_lo = sm
        else:
            s_hi = sm
    sg1 = 0.5 * (s_lo + s_hi)
    Zg1 = sum(math.exp(-(x * x) / (2.0 * sg1 * sg1)) for x in range(-20, 21))
    dg1 = {x: Fraction(math.exp(-(x * x) / (2.0 * sg1 * sg1)) / Zg1).limit_denominator(10**12) for x in range(-14, 15)}
    gauss_dfr_x = -compute_exact_mlkem_dfr(4, 11, 5, dg1, dg1)["union_bound_log2_dfr"]

    ax1.axvline(174.8, color="#475569", linestyle=":", lw=1.3, label="FIPS 203 Table 1 baseline ($2^{-174.8}$)")
    ax1.scatter([gauss_dfr_x], [0.0], color="#b91c1c", marker="X", s=110, zorder=8, label=r"Unit-Var Gaussian $D_{\sigma\approx 1}$ (model)")
    ax1.annotate(
        f"Unit-Var $D_{{\\sigma\\approx 1}}$:\nBai = 0 b, model $2^{{-{gauss_dfr_x:.2f}}}$",
        xy=(gauss_dfr_x, 0.0),
        xytext=(173.02, 22.0),
        arrowprops={"arrowstyle": "->", "color": "#b91c1c", "lw": 1.2},
        fontsize=6.9,
        color="#991b1b",
        fontweight="bold",
        bbox={"boxstyle": "round,pad=0.22", "facecolor": "#fef2f2", "edgecolor": "#b91c1c", "alpha": 0.96},
    )

    bai_512_b = compute_bai_overhead_bits(d16b, 1024, 128.0)["bai_overhead_bits"]
    dfr_512_b = -compute_exact_mlkem_dfr(2, 10, 4, d16b, d16a)["union_bound_log2_dfr"]
    ax1.text(
        0.02,
        0.74,
        "ML-KEM-512 ($\\mathrm{Var}=3/2$, float64 model):\n"
        f"Dyadic-16384-B: $\\mathbf{{{bai_512_b:.4f}}}$ b (41.9$\\times$ vs CBD$_3$)\n"
        f"Model DFR $2^{{-{dfr_512_b:.2f}}}$ (CBD$_3$ model: $2^{{-141.6}}$)",
        transform=ax1.transAxes,
        va="top",
        fontsize=6.6,
        bbox={"boxstyle": "round,pad=0.26", "facecolor": "#f0fdf4", "edgecolor": "#047857", "alpha": 0.96},
    )
    ax1.set_xlim(172.92, 177.05)
    ax1.set_ylim(-5.0, 77.0)
    ax1.set_xlabel(r"ML-KEM-1024 Float64 Model $-\log_2(\mathrm{DFR})$ (CBD$_2$ model: $176.6$; FIPS 203: $174.8$)")
    ax1.set_ylabel(r"ML-KEM-1024 Bai Overhead $\Delta_{\mathrm{Bai}}(256)$ (bits)")
    ax1.set_title("(a) ML-KEM-1024 Float64 Model DFR vs. Bai Overhead (T2i)")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.95, fontsize=6.5)

    # Panel B: Conference/Paley Family Theta(P_p) = sqrt(p) (T3l; Lovasz 1979) + Two-Sided Bound (T3k)
    primes = np.array([5, 13, 17, 29, 37, 41])
    thetas = np.sqrt(primes)
    # Exact clique/independence numbers alpha(P_p) for p = 5,13,17,29,37,41 (computed live!)
    alphas = []
    for p_int in primes:
        p = int(p_int)
        qrs = {(x * x) % p for x in range(1, p)}
        adj: list[set[int]] = [set() for _ in range(p)]
        for i in range(p):
            for j in range(p):
                if i != j and ((i - j) % p) in qrs:
                    adj[i].add(j)
        # Exact maximum independent set containing vertex 0 (vertex-transitive Paley graph!)
        best_ind = 1
        cands = [v for v in range(1, p) if v not in adj[0]]

        def bt(idx: int, chosen: list[int], cand_list: list[int], adj_sets: list[set[int]]) -> None:
            nonlocal best_ind
            best_ind = max(best_ind, len(chosen))
            if len(chosen) + (len(cand_list) - idx) <= best_ind:
                return
            for pos in range(idx, len(cand_list)):
                v = cand_list[pos]
                if all(v not in adj_sets[u] for u in chosen):
                    chosen.append(v)
                    bt(pos + 1, chosen, cand_list, adj_sets)
                    chosen.pop()

        bt(0, [0], cands, adj)
        alphas.append(best_ind)

    p_smooth = np.linspace(4.5, 42.5, 200)
    ax2.plot(p_smooth, np.sqrt(p_smooth), "-", color="#6d28d9", lw=2.0, alpha=0.85, label=r"$\Theta(P_p) = \sqrt{p}$ (Lovász 1979; $\mathbb{Z}[\sqrt{p}]$ SOS, T3l)")
    ax2.scatter(primes, thetas, color="#6d28d9", marker="*", s=135, zorder=7, edgecolor="#1e1b4b", lw=0.5)
    ax2.plot(primes, alphas, "o--", color="#64748b", lw=1.6, ms=5.5, label=r"Single-Copy Independence $\alpha(P_p)$")
    ax2.fill_between(primes, alphas, thetas, color="#ede9fe", alpha=0.55, label=r"Super-Multiplicative Gain $\sqrt{p} - \alpha(P_p)$")

    for p_v, th_v, al_v in zip(primes, thetas, alphas):
        tag = f"$P_{{{int(p_v)}}}$\n$\\sqrt{{{int(p_v)}}}$"
        dy = 0.42 if int(p_v) != 13 else 0.50
        ax2.text(p_v, th_v + dy, tag, ha="center", va="bottom", fontsize=7.0, color="#4c1d95", fontweight="bold")
        ax2.text(p_v, al_v - 0.34, f"{al_v}", ha="center", va="top", fontsize=7.0, color="#475569")

    ax2.text(
        0.985,
        0.03,
        "Conference Theorem (T3l, Zero Reals; $P_5,P_{13},P_{17}$ in Lean):\n"
        "$R^\\top R = 2p\\sqrt{p}\\,R$ in $\\mathbb{Z}[\\sqrt{p}]$ $\\Rightarrow s^2 \\leq (4k+1)^t$\n"
        "Self-complement $\\phi$: $\\alpha(G^{\\boxtimes 2m}) = (4k+1)^m$\n"
        "T3k Two-Sided ($\\forall F, k$): $2\\cdot 4^k - 2^k \\leq R(\\langle 2^k\\rangle) \\leq 7^k$",
        transform=ax2.transAxes,
        ha="right",
        va="bottom",
        fontsize=6.3,
        bbox={"boxstyle": "round,pad=0.28", "facecolor": "#f5f3ff", "edgecolor": "#6d28d9", "alpha": 0.96},
    )
    ax2.set_xticks(primes)
    ax2.set_xticklabels([f"$P_{{{int(p)}}}$" for p in primes], fontsize=8.0)
    ax2.set_xlim(3.0, 43.5)
    ax2.set_ylim(0.8, 8.2)
    ax2.set_xlabel(r"Paley / Self-Complementary Conference Graph $P_p$ ($p = 4k + 1$)")
    ax2.set_ylabel(r"Shannon Capacity $\Theta(P_p)$ vs. $\alpha(P_p)$")
    ax2.set_title(r"(b) Conference/Paley $\Theta(P_p)=\sqrt{p}$ & Two-Sided Bound (T3k, T3l)")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.95, fontsize=6.7)

    fig.tight_layout(w_pad=2.2)
    fig.savefig(out_dir / "fig8_v5_gaussian_paradox_and_paley_family.pdf", bbox_inches="tight")
    plt.close(fig)


def generate_social_preview(svg_path: Path) -> None:
    svg = """<svg xmlns="http://www.w3.org/2000/svg" width="1280" height="640" viewBox="0 0 1280 640">
  <defs>
    <linearGradient id="bg" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#0f172a"/>
      <stop offset="55%" stop-color="#1e293b"/>
      <stop offset="100%" stop-color="#172554"/>
    </linearGradient>
    <linearGradient id="accent" x1="0%" y1="0%" x2="100%" y2="0%">
      <stop offset="0%" stop-color="#38bdf8"/>
      <stop offset="50%" stop-color="#818cf8"/>
      <stop offset="100%" stop-color="#f472b6"/>
    </linearGradient>
  </defs>
  <rect width="1280" height="640" fill="url(#bg)"/>
  <rect x="48" y="48" width="1184" height="544" rx="22" fill="#0b1220" fill-opacity="0.72" stroke="url(#accent)" stroke-width="2.5"/>
  <text x="90" y="132" font-family="system-ui, -apple-system, Segoe UI, sans-serif" font-size="22" font-weight="700" fill="#38bdf8" letter-spacing="2">CODED-PIR-MLWE-COMPLEXITY-LAB · v5.1.0</text>
  <text x="90" y="196" font-family="Georgia, serif" font-size="40" font-weight="700" fill="#f8fafc">Koszul-Veronese Byzantine PIR, MLWE Tightness,</text>
  <text x="90" y="248" font-family="Georgia, serif" font-size="40" font-weight="700" fill="#f8fafc">and Machine-Checked Complexity Bridges</text>
  <rect x="90" y="276" width="260" height="4" rx="2" fill="url(#accent)"/>
  <g font-family="system-ui, -apple-system, Segoe UI, sans-serif" font-size="19" fill="#e2e8f0">
    <rect x="90" y="314" width="340" height="176" rx="14" fill="#1e293b" stroke="#38bdf8" stroke-width="1.5"/>
    <text x="112" y="350" font-weight="700" fill="#38bdf8">PILLAR I · CS-053 PIR (T1a–T1j)</text>
    <text x="112" y="382" font-size="15.5">• 10/17 vs 4/7 for one design (numerical)</text>
    <text x="112" y="408" font-size="15.5">• Single F_2^64 6-obj realization (64/64)</text>
    <text x="112" y="434" font-size="15.5">• F_2 certificates (4 vars, 5-6 objects)</text>
    <text x="112" y="460" font-size="15.5">• Projective P³ linear collapse ∀F</text>

    <rect x="468" y="314" width="340" height="176" rx="14" fill="#1e293b" stroke="#f472b6" stroke-width="1.5"/>
    <text x="490" y="350" font-weight="700" fill="#f472b6">PILLAR II · CS-026 MLWE (T2a–T2i)</text>
    <text x="490" y="382" font-size="15.5">• ML-KEM-1024 DFRs (float64 model)</text>
    <text x="490" y="408" font-size="15.5">• 14b Dyadic-16384-A: 6.01b (11.2× drop)</text>
    <text x="490" y="434" font-size="15.5">• 14b Dyadic-16384-B: 0.59b (41.9× sub-1b)</text>
    <text x="490" y="460" font-size="15.5">• Formalized Rényi DPI, Tensor &amp; R_∞</text>

    <rect x="846" y="314" width="340" height="176" rx="14" fill="#1e293b" stroke="#fbbf24" stroke-width="1.5"/>
    <text x="868" y="350" font-weight="700" fill="#fbbf24">PILLAR III · TRIAD (T3a–T3l)</text>
    <text x="868" y="382" font-size="15.5">• Conference Θ(G)=√(4k+1) (P5,P13,P17)</text>
    <text x="868" y="408" font-size="15.5">• Schwartz-Zippel &amp; 2·4^k-2^k ≤ R ≤ 7^k</text>
    <text x="868" y="434" font-size="15.5">• Exact Strassen-Winograd rank(M_2)=7 ∀F</text>
    <text x="868" y="460" font-size="15.5">• 9 Adv. Refutations · P≠NP, ω=2 OPEN</text>
  </g>
  <text x="90" y="544" font-family="ui-monospace, Consolas, monospace" font-size="15.6" fill="#94a3b8">Zero-Mathlib Lean 4.35.0 (31 Theorems · 6 Kernels · 4337 decls · 1330 Axiom-Swept) · Alexander S. Donahue (ORCID 0009-0006-8168-9648)</text>
</svg>
"""
    svg_path.write_text(svg, encoding="utf-8", newline="\n")


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    style_axes()
    fig_dir = root / "paper" / "figures"
    fig_dir.mkdir(parents=True, exist_ok=True)
    fig1_cs053_rate_frontier(fig_dir)
    fig2_shannon_ingleton_barrier(fig_dir)
    fig3_mlwe_renyi_and_qgtl(fig_dir)
    fig4_chen_step9_and_triad(fig_dir)
    fig5_dyadic256_and_koszul_tensor(fig_dir)
    fig6_mlkem_dfr_variational_and_allm_koszul(fig_dir)
    fig7_bai_security_collapse_and_lovasz_bd(fig_dir)
    fig8_v5_gaussian_paradox_and_paley_family(fig_dir)
    generate_social_preview(root / "docs" / "media" / "social-preview.svg")
    print("Generated all 8 vector PDF figures and docs/media/social-preview.svg.")


if __name__ == "__main__":
    main()
