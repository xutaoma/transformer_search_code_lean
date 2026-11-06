#!/usr/bin/env python3
"""Regenerate the paper figures from experiments/results/*.npz.

Usage (from the repository root):  python3 experiments/make_figures.py
Writes PDFs to figure/ and PDF+PNG previews to experiments/figures/.
"""
import os
import sys

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
from matplotlib.lines import Line2D

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RES = os.path.join(ROOT, "experiments", "results")
OUT_PDF = os.path.join(ROOT, "figure")
OUT_PREV = os.path.join(ROOT, "experiments", "figures")
os.makedirs(OUT_PDF, exist_ok=True)
os.makedirs(OUT_PREV, exist_ok=True)

# ----------------------------------------------------------------------------
# style
# ----------------------------------------------------------------------------
BLUE, ORANGE, AQUA, VIOLET = "#2a78d6", "#eb6834", "#1baf7a", "#6250d6"
INK, GRAY, GRID = "#222222", "#8c8c8c", "#e4e4e4"
# sequential blues for the ordinal N sweep
BLUES6 = ["#bcd4f2", "#8fb6ea", "#6197de", "#3b7bd2", "#255fb0", "#153f7e"]

plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["STIXGeneral", "Times New Roman", "Times", "DejaVu Serif"],
    "mathtext.fontset": "stix",
    "font.size": 7.5,
    "axes.labelsize": 7.5,
    "axes.titlesize": 7.5,
    "xtick.labelsize": 6.5,
    "ytick.labelsize": 6.5,
    "legend.fontsize": 6.3,
    "legend.frameon": False,
    "legend.handlelength": 1.7,
    "legend.handletextpad": 0.5,
    "legend.labelspacing": 0.28,
    "legend.borderaxespad": 0.3,
    "axes.linewidth": 0.5,
    "axes.edgecolor": INK,
    "axes.labelcolor": INK,
    "xtick.color": INK,
    "ytick.color": INK,
    "xtick.major.width": 0.5,
    "ytick.major.width": 0.5,
    "xtick.minor.width": 0.4,
    "ytick.minor.width": 0.4,
    "xtick.major.size": 2.4,
    "ytick.major.size": 2.4,
    "xtick.minor.size": 1.4,
    "ytick.minor.size": 1.4,
    "xtick.direction": "out",
    "ytick.direction": "out",
    "lines.linewidth": 1.1,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "savefig.dpi": 300,
})

LW = 1.1
MK = dict(marker="o", ms=2.9, mfc="white", mew=0.75, ls="none")


def tidy(ax, xlog=True, ylog=False, grid="y"):
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    if xlog:
        ax.set_xscale("log")
        ax.xaxis.set_major_locator(mticker.LogLocator(base=10.0, numticks=7))
        ax.xaxis.set_minor_locator(mticker.LogLocator(base=10.0, subs=(2, 5), numticks=20))
        ax.xaxis.set_minor_formatter(mticker.NullFormatter())
    if ylog:
        ax.set_yscale("log")
        ax.yaxis.set_major_locator(mticker.LogLocator(base=10.0, numticks=7))
        ax.yaxis.set_minor_formatter(mticker.NullFormatter())
    ax.grid(False)
    if grid:
        ax.grid(True, axis=grid, color=GRID, lw=0.5, zorder=0)
    ax.set_axisbelow(True)
    ax.tick_params(which="both", colors=INK)


def save(fig, name):
    fig.savefig(os.path.join(OUT_PDF, name + ".pdf"), bbox_inches="tight", pad_inches=0.015)
    fig.savefig(os.path.join(OUT_PREV, "fig_" + name + ".pdf"), bbox_inches="tight", pad_inches=0.015)
    fig.savefig(os.path.join(OUT_PREV, "fig_" + name + ".png"), bbox_inches="tight", pad_inches=0.02)
    plt.close(fig)
    print("wrote", name)


def load(name):
    return np.load(os.path.join(RES, name), allow_pickle=True)


def pos(t, *ys):
    m = t > 0
    return (t[m],) + tuple(y[m] for y in ys)


def sub(x, k=2):
    return x[::k]


def fit_slope(x, y, lo, hi, logy=False):
    m = (x >= lo) & (x <= hi)
    if logy:
        m &= y > 0
        return np.polyfit(np.log(x[m]), np.log(y[m]), 1)[0]
    return np.polyfit(np.log(x[m]), y[m], 1)[0]


# names in theta: a1 b1 a2 b2 g1 d1 g2 d2
IDX = dict(a1=0, b1=1, a2=2, b2=3, g1=4, d1=5, g2=6, d2=7)


def col(theta, name):
    return theta[:, IDX[name]]


# ----------------------------------------------------------------------------
# 1. rates_main
# ----------------------------------------------------------------------------
def fig_rates_main():
    A1 = load("A1_reduced.npz")
    A2 = load("A2_full.npz")
    N = int(A1["N"])
    t1, th1 = A1["t"], A1["theta"]
    t2, th2 = A2["t"], A2["theta"]
    series = [
        ("$a_2$", lambda th: col(th, "a2"), BLUE, "-"),
        ("$b_1$", lambda th: col(th, "b1"), ORANGE, "-"),
        ("$g_1-d_1$", lambda th: col(th, "g1") - col(th, "d1"), AQUA, "-"),
        ("$g_2-d_2$", lambda th: col(th, "g2") - col(th, "d2"), VIOLET, (0, (3.2, 1.6))),
    ]
    fig, ax = plt.subplots(figsize=(2.75, 2.05))
    tidy(ax)
    tt1 = t1[t1 > 0]
    for lab, f, c, ls in series:
        y = f(th1)[t1 > 0]
        ax.plot(tt1, y, color=c, ls=ls, lw=LW, label=lab, zorder=3)
    m2 = t2 > 0
    for lab, f, c, ls in series:
        ax.plot(sub(t2[m2]), sub(f(th2)[m2]), color=c, zorder=4, **MK)
    # slope guides
    tg = np.array([1e3, 1e9])
    a2 = col(th1, "a2")
    g = col(th1, "g1") - col(th1, "d1")
    y0 = np.interp(np.log(1e3), np.log(tt1), a2[t1 > 0]) + 2.5
    ax.plot(tg, y0 + 2 * np.log(tg / 1e3), color=GRAY, ls=(0, (2.5, 1.8)), lw=0.8, zorder=2)
    ax.text(1e9, y0 + 2 * np.log(1e6) + 0.6, "slope 2", color=GRAY, fontsize=6.3, ha="right", va="bottom")
    y1 = np.interp(np.log(1e3), np.log(tt1), g[t1 > 0]) - 2.5
    ax.plot(tg, y1 + np.log(tg / 1e3), color=GRAY, ls=(0, (2.5, 1.8)), lw=0.8, zorder=2)
    ax.text(1e9, y1 + np.log(1e6) - 1.0, "slope 1", color=GRAY, fontsize=6.3, ha="right", va="top")
    ax.set_xlabel("training time $t$")
    ax.set_ylabel("effective parameter")
    ax.set_xlim(0.8, 2e9)
    ax.set_ylim(-1, 42)
    ax.set_yticks([0, 10, 20, 30, 40])
    handles, labels = ax.get_legend_handles_labels()
    handles += [Line2D([], [], color=GRAY, lw=LW), Line2D([], [], color=GRAY, **MK)]
    labels += ["reduced flow", "full matrices"]
    ax.legend(handles, labels, loc="upper left", ncol=1)
    save(fig, "rates_main")


# ----------------------------------------------------------------------------
# 2. gen_decay
# ----------------------------------------------------------------------------
def fig_gen_decay():
    R = load("B_gen_reduced.npz")
    F = load("B_gen_full.npz")
    t, tf = R["t"], F["t"]
    series = [
        ("$\\mathcal{L}_{\\mathrm{gen}}$ (max over states)", "L_gen", INK),
        ("forward", "mean_forward", BLUE),
        ("backtrack, non-root parent", "mean_backtrack_nonroot", ORANGE),
        ("backtrack, root parent", "mean_backtrack_root", AQUA),
    ]
    fig, ax = plt.subplots(figsize=(2.75, 2.05))
    tidy(ax, ylog=True)
    m = t >= 10
    for lab, k, c in series:
        ax.plot(t[m], R[k][m], color=c, lw=LW, label=lab, zorder=3)
    mf = tf >= 10
    for lab, k, c in series[1:]:
        ax.plot(sub(tf[mf]), sub(F[k][mf]), color=c, zorder=4, **MK)
    # guides
    tg = np.array([1e4, 1e9])
    yb = np.interp(np.log(1e4), np.log(t[m]), np.log(R["mean_backtrack_nonroot"][m]))
    for p, lab, off in [(-1.0, "$t^{-1}$", -3.4), (-15 / 16, "$t^{-15/16}$", -2.0)]:
        y = np.exp(yb + off + p * np.log(tg / 1e4))
        ax.plot(tg, y, color=GRAY, ls=(0, (2.5, 1.8)), lw=0.8, zorder=2)
        ax.text(1.35e9, y[-1], lab, color=GRAY, fontsize=6.3, ha="left", va="center")
    ax.set_xlabel("training time $t$")
    ax.set_ylabel("admissible-token loss")
    ax.set_xlim(8, 5e9)
    ax.set_ylim(1e-9, 30)
    ax.yaxis.set_major_locator(mticker.LogLocator(base=10.0, numticks=6))
    handles, labels = ax.get_legend_handles_labels()
    handles += [Line2D([], [], color=GRAY, **MK)]
    labels += ["full matrices"]
    ax.legend(handles, labels, loc="lower left")
    save(fig, "gen_decay")


# ----------------------------------------------------------------------------
# 3. exponent_vs_N : local log-log slope of the root-backtracking loss
# ----------------------------------------------------------------------------
def fig_exponent_vs_N():
    C = load("C_curves.npz")
    Ns = [8, 10, 12, 16, 24, 32]
    fig, ax = plt.subplots(figsize=(2.75, 2.05))
    tidy(ax, grid=None)
    for N, c in zip(Ns, BLUES6):
        t, y = C["t_%d" % N], C["mean_%d" % N]
        lt, ly = np.log(t), np.log(y)
        s = np.gradient(ly, lt)
        ax.plot(t, s, color=c, lw=LW, zorder=3)
        th = -(N - 1) / N
        ax.axhline(th, color=GRAY, ls=(0, (2.5, 1.8)), lw=0.6, zorder=2)
        ax.text(1.25e9, th, "$N=%d$" % N, color=INK, fontsize=6.3, ha="left", va="center")
    ax.set_xlabel("training time $t$")
    ax.set_ylabel("local exponent, root-backtracking loss")
    ax.set_xlim(1e4, 1e9)
    ax.set_ylim(-1.0, -0.86)
    ax.set_yticks([-1.0, -0.95, -0.9])
    save(fig, "exponent_vs_N")


# ----------------------------------------------------------------------------
# 4. rates_individual
# ----------------------------------------------------------------------------
def fig_rates_individual():
    A1 = load("A1_reduced.npz")
    N = int(A1["N"])
    t, th = A1["t"], A1["theta"]
    m = t > 0
    tt = t[m]
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(2.75, 2.5), sharex=True,
                                   gridspec_kw=dict(height_ratios=[1.15, 1.0], hspace=0.12))
    tidy(ax1)
    tidy(ax2)
    dash = (0, (3.2, 1.6))
    ax1.plot(tt, col(th, "g1")[m], color=BLUE, lw=LW, label="$g_1$", zorder=3)
    ax1.plot(tt, col(th, "g2")[m], color=ORANGE, lw=LW, ls=dash, label="$g_2$", zorder=3)
    tg = np.array([1e3, 1e9])
    g1 = col(th, "g1")[m]
    y0 = np.interp(np.log(1e3), np.log(tt), g1) + 2.5
    ax1.plot(tg, y0 + (N - 1) / N * np.log(tg / 1e3), color=GRAY, ls=(0, (2.5, 1.8)), lw=0.8, zorder=2)
    ax1.text(1e9, y0 + (N - 1) / N * np.log(1e6) + 0.5, "slope $(N{-}1)/N$", color=GRAY, fontsize=6.3,
             ha="right", va="bottom")
    ax1.set_ylim(-1, 26)
    ax1.set_yticks([0, 10, 20])
    ax1.legend(loc="upper left", ncol=2, columnspacing=1.0)
    ax2.axhline(0, color=GRAY, lw=0.5, zorder=1)
    ax2.plot(tt, col(th, "d1")[m], color=AQUA, lw=LW, label="$d_1$", zorder=3)
    ax2.plot(tt, col(th, "d2")[m], color=VIOLET, lw=LW, ls=dash, label="$d_2$", zorder=3)
    cons1 = col(th, "g1") + (N - 1) * col(th, "d1")
    cons2 = col(th, "g2") + (N - 1) * col(th, "d2")
    ax2.plot(tt, cons1[m], color=INK, lw=0.9, label="$g_1+(N{-}1)d_1$", zorder=3)
    ax2.plot(tt, cons2[m], color=INK, lw=0.9, ls=(0, (1.2, 1.2)), label="$g_2+(N{-}1)d_2$", zorder=3)
    d1 = col(th, "d1")[m]
    y1 = np.interp(np.log(1e3), np.log(tt), d1) - 0.45
    ax2.plot(tg, y1 - np.log(tg / 1e3) / N, color=GRAY, ls=(0, (2.5, 1.8)), lw=0.8, zorder=2)
    ax2.text(1e9, y1 - np.log(1e6) / N - 0.12, "slope $-1/N$", color=GRAY, fontsize=6.3, ha="right", va="top")
    ax2.set_ylim(-2.4, 0.6)
    ax2.set_yticks([-2, -1, 0])
    ax2.legend(loc="lower left", ncol=2, columnspacing=1.0)
    ax2.set_xlabel("training time $t$")
    ax2.set_xlim(0.8, 2e9)
    fig.supylabel("parameter value", fontsize=7.5, x=0.0)
    save(fig, "rates_individual")


# ----------------------------------------------------------------------------
# 5. gaps
# ----------------------------------------------------------------------------
def fig_gaps():
    A1 = load("A1_reduced.npz")
    t, th = A1["t"], A1["theta"]
    m = t > 0
    tt = t[m]
    u = (col(th, "a2") - col(th, "b1"))[m]
    v = (col(th, "g1") - col(th, "d1") - col(th, "g2") + col(th, "d2"))[m]
    w = (2 * (col(th, "g1") - col(th, "d1")) - col(th, "a2"))[m]
    b2 = col(th, "b2")[m]
    fig, ax = plt.subplots(figsize=(2.75, 2.05))
    tidy(ax)
    ax.axhline(0, color=GRAY, lw=0.5, zorder=1)
    ax.plot(tt, u, color=BLUE, lw=LW, label="$u=a_2-b_1$", zorder=3)
    ax.plot(tt, w, color=AQUA, lw=LW, label="$2(g_1-d_1)-a_2$", zorder=3)
    ax.plot(tt, v, color=ORANGE, lw=LW, label="$v=g_1-d_1-g_2+d_2$", zorder=3)
    ax.plot(tt, b2, color=VIOLET, lw=LW, ls=(0, (3.2, 1.6)), label="$b_2$", zorder=3)
    ax.set_xlabel("training time $t$")
    ax.set_ylabel("gap variable")
    ax.set_xlim(0.8, 2e9)
    ax.set_ylim(-0.8, 7.2)
    ax.legend(loc="upper left", ncol=2, columnspacing=1.0)
    save(fig, "gaps")


# ----------------------------------------------------------------------------
# 6. subspace
# ----------------------------------------------------------------------------
def fig_subspace():
    A2 = load("A2_full.npz")
    t, dist = A2["t"], A2["dist"]
    m = t > 0
    fig, ax = plt.subplots(figsize=(2.75, 2.05))
    tidy(ax, ylog=True)
    for j, (lab, c, ls) in enumerate([("$\\mathbf{A}_1$", BLUE, "-"), ("$\\mathbf{A}_2$", ORANGE, (0, (3.2, 1.6))),
                                      ("$\\mathbf{B}_1$", AQUA, "-"), ("$\\mathbf{B}_2$", VIOLET, (0, (3.2, 1.6)))]):
        y = np.maximum(dist[m, j], 1e-12)
        ax.plot(t[m], y, color=c, ls=ls, lw=LW, label=lab, zorder=3)
    ax.set_xlabel("training time $t$")
    ax.set_ylabel("relative distance to $\\mathcal{F}$")
    ax.set_xlim(0.08, 1e6)
    ax.set_ylim(1e-6, 3)
    ax.legend(loc="upper right", ncol=2, columnspacing=1.0)
    save(fig, "subspace")


# ----------------------------------------------------------------------------
# 7. gen_accuracy
# ----------------------------------------------------------------------------
def fig_gen_accuracy():
    B = load("B_diagnostics.npz")
    t = B["t"]
    m = (t >= 1) & (t <= 1e6)
    fig, ax = plt.subplots(figsize=(2.75, 2.05))
    tidy(ax)
    series = [
        ("all states", "accuracy", INK, "-"),
        ("forward, back-edge to parent", "acc_forward_backedge", BLUE, "-"),
        ("forward, no back-edge", "acc_forward_no_backedge", ORANGE, (0, (3.2, 1.6))),
        ("backtrack, non-root parent", "acc_backtrack_nonroot", AQUA, "-"),
        ("backtrack, root parent", "acc_backtrack_root", VIOLET, (0, (3.2, 1.6))),
    ]
    for lab, k, c, ls in series:
        ax.plot(t[m], B[k][m], color=c, ls=ls, lw=LW, label=lab, zorder=3)
    ax.set_xlabel("training time $t$")
    ax.set_ylabel("fraction of valid argmax moves")
    ax.set_xlim(0.8, 1e6)
    ax.set_ylim(-0.03, 1.05)
    ax.set_yticks([0, 0.25, 0.5, 0.75, 1.0])
    ax.legend(loc="center right", bbox_to_anchor=(1.0, 0.42))
    save(fig, "gen_accuracy")


# ----------------------------------------------------------------------------
# 8. init_ablation
# ----------------------------------------------------------------------------
def fig_init_ablation():
    D1, D2, D3, D3r = (load(n) for n in ["D1_reduced.npz", "D2_reduced.npz", "D3_reduced.npz",
                                          "D3_roundoff_reduced.npz"])
    D4 = [load("D4_seed%d.npz" % s) for s in (1, 2, 3)]
    panels = [
        ("$b_2-b_1$", lambda th: col(th, "b2") - col(th, "b1")),
        ("$g_1-d_1$", lambda th: col(th, "g1") - col(th, "d1")),
        ("$a_2$", lambda th: col(th, "a2")),
        ("$b_1$", lambda th: col(th, "b1")),
    ]
    runs = [
        ("D1: proposed initialization", D1, BLUE, "-", 1.5),
        ("D2: constant, $\\mathrm{ReLU}'(0)=1$", D2, ORANGE, (0, (3.2, 1.6)), 1.1),
        ("D3: constant, $\\mathrm{ReLU}'(0)=0$", D3, AQUA, "-", 1.1),
        ("D3 with round-off", D3r, AQUA, (0, (1.2, 1.2)), 1.1),
    ]
    fig, axes = plt.subplots(2, 2, figsize=(4.7, 3.15), sharex=True)
    for ax, (title, f) in zip(axes.ravel(), panels):
        tidy(ax)
        ax.axhline(0, color=GRAY, lw=0.5, zorder=1)
        for lab, D, c, ls, lw in runs:
            t, th = D["t"], D["theta"]
            m = t > 0
            ax.plot(t[m], f(th)[m], color=c, ls=ls, lw=lw, label=lab, zorder=3)
        for s, D in enumerate(D4):
            t, th = D["t"], D["theta"]
            m = t > 0
            ax.plot(sub(t[m]), sub(f(th)[m]), color=VIOLET, zorder=4,
                    label="D4: full matrices (3 seeds)" if s == 0 else None, **MK)
        ax.set_title(title, loc="left", pad=3)
        ax.set_xlim(0.08, 1e6)
    for ax in axes[1]:
        ax.set_xlabel("training time $t$")
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=3, bbox_to_anchor=(0.5, 0.0), columnspacing=1.2)
    fig.subplots_adjust(hspace=0.38, wspace=0.26, bottom=0.21, top=0.95, left=0.09, right=0.99)
    save(fig, "init_ablation")


# ----------------------------------------------------------------------------
# 9. init_wrong_side
# ----------------------------------------------------------------------------
def fig_init_wrong_side():
    W = load("D2_wrong_side.npz")
    cases = [("16", "2"), ("40", "3"), ("16", "8")]
    rows = [("$b_2-b_1$", lambda th: col(th, "b2") - col(th, "b1"), (-1.0, 0.5)),
            ("$b_1$", lambda th: col(th, "b1"), (-0.3, 1.0))]
    runs = [("D1: proposed initialization", "D1", BLUE, "-", 1.5),
            ("D2: constant, $\\mathrm{ReLU}'(0)=1$", "D2", ORANGE, "-", 1.1),
            ("D3: constant, $\\mathrm{ReLU}'(0)=0$", "D3", AQUA, (0, (1.2, 1.2)), 1.1)]
    fig, axes = plt.subplots(2, 3, figsize=(4.7, 2.75), sharex=True, sharey="row")
    for j, (N, K) in enumerate(cases):
        for i, (ylab, f, ylim) in enumerate(rows):
            ax = axes[i, j]
            tidy(ax)
            ax.axhline(0, color=GRAY, lw=0.5, zorder=1)
            for lab, key, c, ls, lw in runs:
                t = W["%s_N%s_K%s_t" % (key, N, K)]
                th = W["%s_N%s_K%s_theta" % (key, N, K)]
                m = t > 0
                ax.plot(t[m], f(th)[m], color=c, ls=ls, lw=lw, label=lab, zorder=3)
            ax.set_ylim(*ylim)
            ax.set_xlim(0.05, 3e3)
            if i == 0:
                ax.set_title("$N=%s,\\ K=%s$" % (N, K), loc="left", pad=3)
            if j == 0:
                ax.set_ylabel(ylab + " (clipped)")
            if i == 1:
                ax.set_xlabel("training time $t$")
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=3, bbox_to_anchor=(0.5, 0.0), columnspacing=1.6)
    fig.subplots_adjust(hspace=0.3, wspace=0.12, bottom=0.22, top=0.92, left=0.1, right=0.99)
    save(fig, "init_wrong_side")


if __name__ == "__main__":
    which = sys.argv[1:] or ["rates_main", "gen_decay", "exponent_vs_N", "rates_individual", "gaps",
                             "subspace", "gen_accuracy", "init_ablation", "init_wrong_side"]
    for w in which:
        globals()["fig_" + w]()
