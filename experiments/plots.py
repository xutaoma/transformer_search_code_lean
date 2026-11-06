"""All figures of the plan, from results/ only. Saves each figure in figures/ as both PDF and PNG."""
import json, pathlib
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import model as M

HERE = pathlib.Path(__file__).resolve().parent
RES = HERE / "results"; FIG = HERE / "figures"
# categorical slots (validated default palette), fixed entity -> colour
BLUE, ORANGE, AQUA, YELLOW, MAGENTA, GREEN, VIOLET, RED = ("#2a78d6", "#eb6834", "#1baf7a", "#eda100",
                                                           "#e87ba4", "#008300", "#6250d6", "#e34948")
INK, MUTED = "#0b0b0b", "#52514e"
plt.rcParams.update({
    "font.size": 9, "axes.titlesize": 10, "axes.labelsize": 9, "legend.fontsize": 8, "lines.linewidth": 1.5,
    "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": MUTED, "text.color": INK,
    "axes.labelcolor": INK, "xtick.color": MUTED, "ytick.color": MUTED, "axes.grid": True, "grid.color": "#e6e5e0",
    "grid.linewidth": 0.6, "legend.frameon": False, "pdf.fonttype": 42, "figure.dpi": 150, "savefig.bbox": "tight"})
IDX = {n: i for i, n in enumerate(M.NAMES)}


def save(fig, name):
    fig.savefig(FIG / f"{name}.pdf")
    fig.savefig(FIG / f"{name}.png", dpi=300)


def load(name):
    p = RES / name
    return np.load(p, allow_pickle=True) if p.exists() else None


def q(th, k):
    if k in IDX:
        return th[:, IDX[k]]
    return {"g1-d1": lambda: th[:, IDX["g1"]] - th[:, IDX["d1"]], "g2-d2": lambda: th[:, IDX["g2"]] - th[:, IDX["d2"]],
            "u": lambda: th[:, IDX["a2"]] - th[:, IDX["b1"]],
            "v": lambda: (th[:, IDX["g1"]] - th[:, IDX["d1"]]) - (th[:, IDX["g2"]] - th[:, IDX["d2"]]),
            "2(g1-d1)-a2": lambda: 2 * (th[:, IDX["g1"]] - th[:, IDX["d1"]]) - th[:, IDX["a2"]]}[k]()


LABEL = {"a2": r"$a_2$", "b1": r"$b_1$", "b2": r"$b_2$", "a1": r"$a_1$", "g1-d1": r"$g_1-d_1$", "g2-d2": r"$g_2-d_2$", "g1": r"$g_1$", "g2": r"$g_2$",
         "d1": r"$d_1$", "d2": r"$d_2$", "u": r"$u=a_2-b_1$", "v": r"$v=(g_1-d_1)-(g_2-d_2)$", "2(g1-d1)-a2": r"$2(g_1-d_1)-a_2$"}


def overlay(ax, keys, colors, A1, A2, slopes=None, styles=None):
    t = A1["t"]; m = t >= 1
    for k, col in zip(keys, colors):
        ls = (styles or {}).get(k, "-")
        lab = LABEL[k] + (f"  (slope {slopes[k]['slope']:.3f})" if slopes else "")
        ax.plot(t[m], q(A1["theta"], k)[m], color=col, ls=ls, label=lab)
        if A2 is not None:
            s = A2["t"] >= 1
            ax.plot(A2["t"][s], q(A2["theta"], k)[s], ls="none", marker="o", ms=4, mfc="white", mew=1.0, color=col, zorder=3)
    ax.set_xscale("log"); ax.set_xlabel("training time $t$")


def ref_slope(ax, slope, t_end, y_end, label):
    x = np.array([1e3, t_end])
    ax.plot(x, y_end + slope * (np.log(x) - np.log(t_end)), color=MUTED, ls=(0, (4, 3)), lw=1, zorder=1)
    ax.annotate(label, (t_end, y_end), xytext=(4, 0), textcoords="offset points", ha="left", va="center", color=MUTED, fontsize=8, annotation_clip=False)


def marker_legend(ax, A2):
    if A2 is not None:
        ax.plot([], [], ls="-", color=MUTED, label="reduced flow (A1)")
        ax.plot([], [], ls="none", marker="o", ms=4, mfc="white", color=MUTED, label="full matrices (A2)")


def fig_rates(A1, A2, sl):
    fig, ax = plt.subplots(figsize=(6.2, 3.8))
    keys = ["a2", "b1", "g1-d1", "g2-d2"]
    overlay(ax, keys, [BLUE, ORANGE, AQUA, VIOLET], A1, A2, sl, styles={"g2-d2": (0, (3, 2))})
    ta, tb = A1["t"][-1], A1["theta"][-1]
    ref_slope(ax, 2.0, ta, q(A1["theta"], "a2")[-1] + 1.5, "slope 2")
    ref_slope(ax, 1.0, ta, q(A1["theta"], "g1-d1")[-1] - 2.0, "slope 1")
    marker_legend(ax, A2); ax.legend(loc="upper left", ncol=1)
    ax.set_ylabel("effective parameter"); ax.set_title(r"Growth rates against $\ln t$ ($N=16,\ K=8$); fit on $t\in[10^3,10^9]$", loc="left")
    save(fig, "fig_rates_main"); plt.close(fig)


def fig_individual(A1, A2, sl, N):
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(8.6, 3.4))
    overlay(ax, ["g1", "g2", "d1", "d2"], [BLUE, ORANGE, AQUA, MAGENTA], A1, A2, sl, styles={"g2": (0, (3, 2)), "d2": (0, (3, 2))})
    ax.set_ylabel("parameter"); marker_legend(ax, A2); ax.legend(loc="center left")
    ax.set_title(fr"Individual parameters (refs {(N - 1) / N:.4f}, {-1 / N:.4f})", loc="left")
    ref_slope(ax, (N - 1) / N, A1["t"][-1], q(A1["theta"], "g1")[-1] + 1.5, f"{(N - 1) / N:.4f}")
    ref_slope(ax, -1 / N, A1["t"][-1], q(A1["theta"], "d1")[-1] - 1.5, f"{-1 / N:.4f}")
    t = A1["t"]; m = t >= 0.01
    th = A1["theta"]
    c1 = th[:, IDX["g1"]] + (N - 1) * th[:, IDX["d1"]]; c2 = th[:, IDX["g2"]] + (N - 1) * th[:, IDX["d2"]]
    bx.plot(t[m], c1[m], color=BLUE, label=r"$g_1+(N-1)d_1$")
    bx.plot(t[m], c2[m], color=ORANGE, label=r"$g_2+(N-1)d_2$")
    bx.set_xscale("log"); bx.set_xlabel("training time $t$"); bx.legend(loc="center right")
    bx.set_title("Conserved combinations", loc="left")
    fig.tight_layout(); save(fig, "fig_rates_individual"); plt.close(fig)


def fig_gaps(A1, A2):
    fig, axs = plt.subplots(1, 2, figsize=(8.6, 3.2))
    overlay(axs[0], ["u", "2(g1-d1)-a2"], [BLUE, ORANGE], A1, A2)
    marker_legend(axs[0], A2)
    axs[0].legend(); axs[0].set_title("Bounded gaps", loc="left"); axs[0].set_ylabel("value")
    overlay(axs[1], ["v", "b2", "a1"], [AQUA, YELLOW, VIOLET], A1, A2)
    marker_legend(axs[1], A2)
    axs[1].legend(); axs[1].set_title(r"Small quantities ($v,\ b_2,\ a_1$)", loc="left")
    fig.tight_layout(); save(fig, "fig_gaps"); plt.close(fig)


def fig_subspace(A2):
    fig, ax = plt.subplots(figsize=(5.4, 3.2))
    m = A2["t"] > 0
    for i, (nm, col) in enumerate(zip((r"$A_1$", r"$A_2$", r"$B_1$", r"$B_2$"), (BLUE, ORANGE, AQUA, YELLOW))):
        ax.plot(A2["t"][m], A2["dist"][m, i], color=col, label=nm)
    ax.axhline(1e-2, color=MUTED, ls=(0, (4, 3)), lw=1); ax.annotate("acceptance $10^{-2}$", (A2["t"][m][0], 1e-2), xytext=(2, 3), textcoords="offset points", color=MUTED, fontsize=8)
    ax.set_xscale("log"); ax.set_yscale("log"); ax.set_xlabel("training time $t$")
    ax.set_ylabel(r"$\|X-\Pi X\|_F/\|X\|_F$"); ax.legend(); ax.set_title("Distance to the permutation-invariant subspace", loc="left")
    save(fig, "fig_subspace"); plt.close(fig)


def fig_gen(N):
    B = load("B_gen_reduced.npz"); B2 = load("B_gen_full.npz")
    D = load("B_diagnostics.npz")
    ex = json.loads((RES / "B_exponents.json").read_text())["A1"]["exponents"]
    fig, ax = plt.subplots(figsize=(6.6, 4.0))
    t = B["t"]; m = t >= 10
    # L_gen is drawn beneath in neutral ink; the three category means sit on top
    ax.plot(t[m], B["L_gen"][m], color=INK, lw=1.2, label=fr"$L_{{gen}}$ (max)  ({ex['L_gen']['slope']:.3f})")
    for key, col, name in (("forward", BLUE, "forward"), ("backtrack_nonroot", ORANGE, "backtrack, non-root parent"), ("backtrack_root", AQUA, "backtrack, root parent")):
        ax.plot(t[m], B[f"mean_{key}"][m], color=col, label=f"mean {name}  ({ex['mean_' + key]['slope']:.3f})")
        if B2 is not None:
            s = B2["t"] >= 10
            ax.plot(B2["t"][s], B2[f"mean_{key}"][s], ls="none", marker="o", ms=4, mfc="white", color=col, zorder=3)
    # reference slopes anchored at the last point
    tt = np.array([1e3, 1e9])
    for slope, lab, y0 in ((-1.0, r"$t^{-1}$", B["mean_backtrack_nonroot"][-1] / 6), (-(N - 1) / N, fr"$t^{{-{(N - 1) / N:.4f}}}$", B["mean_backtrack_root"][-1] * 4)):
        ax.plot(tt, y0 * (tt / 1e9) ** slope, color=MUTED, ls=(0, (4, 3)), lw=1)
        ax.annotate(lab, (1e9, y0), xytext=(3, 0), textcoords="offset points", color=MUTED, fontsize=8, va="center")
    if B2 is not None:
        ax.plot([], [], ls="none", marker="o", ms=4, mfc="white", color=MUTED, label="full matrices (A2)")
    ax.set_xscale("log"); ax.set_yscale("log"); ax.set_xlabel("training time $t$"); ax.set_ylabel("admissible-token loss")
    ax.legend(loc="lower left"); ax.set_title(r"Generalization decay; exponents fitted on $[10^3,10^9]$", loc="left")
    save(fig, "fig_gen_decay"); plt.close(fig)

    fig, ax = plt.subplots(figsize=(6.2, 3.4))
    t = D["t"]; m = t <= 1e7
    for key, col, name in (("forward_no_backedge", BLUE, "forward, no back-edge"), ("forward_backedge", RED, r"forward, edge $n_t\to$ parent"),
                           ("backtrack_nonroot", ORANGE, "backtrack, non-root parent"), ("backtrack_root", AQUA, "backtrack, root parent")):
        ax.plot(t[m], D[f"acc_{key}"][m], color=col, label=name)
    ax.plot(B["t"][B["t"] <= 1e7], B["accuracy"][B["t"] <= 1e7], color=INK, lw=1.2, ls=(0, (3, 2)), label="all prefixes")
    ax.set_xscale("log"); ax.set_xlabel("training time $t$"); ax.set_ylabel(r"fraction with argmax in $C_t$")
    ax.legend(loc="lower right"); ax.set_title("Accuracy on the test set", loc="left")
    save(fig, "fig_gen_accuracy"); plt.close(fig)


def fig_C():
    rows = np.genfromtxt(RES / "C_exponents.csv", delimiter=",", names=True)
    fig, ax = plt.subplots(figsize=(4.8, 3.2))
    Ns = np.linspace(7.5, 33, 200)
    ax.plot(Ns, -(Ns - 1) / Ns, color=MUTED, ls=(0, (4, 3)), lw=1, label=r"$-(N-1)/N$")
    ax.plot(rows["N"], rows["fitted"], ls="none", marker="o", ms=6, color=BLUE, label="fitted exponent")
    ax.set_xlabel("$N$"); ax.set_ylabel("exponent of mean backtrack-root loss"); ax.legend()
    ax.set_title(r"Exponent vs. $N$ (fit on $t\in[10^4,10^9]$)", loc="left")
    save(fig, "fig_exponent_vs_N"); plt.close(fig)


def fig_D():
    runs = [("D1_reduced", BLUE, "-", "D1 new init, $R'(0)=1$"), ("D2_reduced", ORANGE, "-", "D2 constant, $R'(0)=1$"), ("D3_reduced", AQUA, "-", "D3 constant, $R'(0)=0$ (exact)"),
            ("D3_roundoff_reduced", AQUA, (0, (3, 2)), "D3 with round-off in heads")]
    seeds = [load(f"D4_seed{s}.npz") for s in (1, 2, 3)]
    panels = [("b2-b1", lambda th: th[:, IDX["b2"]] - th[:, IDX["b1"]], r"$b_2-b_1$"), ("g1-d1", lambda th: q(th, "g1-d1"), r"$g_1-d_1$"), ("a2", lambda th: q(th, "a2"), r"$a_2$"), ("b1", lambda th: q(th, "b1"), r"$b_1$")]
    fig, axs = plt.subplots(2, 2, figsize=(8.6, 5.4), sharex=True)
    for ax, (_, f, name) in zip(axs.flat, panels):
        for tag, col, ls, lab in runs:
            d = load(tag + ".npz")
            ax.plot(d["t"][1:], f(d["theta"])[1:], color=col, ls=ls, label=lab)
        for i, d in enumerate(seeds):
            if d is not None:
                ax.plot(d["t"][1:], f(d["theta"])[1:], ls="none", marker="o", ms=3.5, mfc="white", color=VIOLET, label="D4 full matrices, 3 seeds" if i == 0 else None)
        ax.set_xscale("log"); ax.set_title(name, loc="left")
    axs[1, 0].set_xlabel("training time $t$"); axs[1, 1].set_xlabel("training time $t$")
    axs[0, 1].legend(loc="center left", bbox_to_anchor=(1.0, 0.0))
    fig.tight_layout(); save(fig, "fig_init_ablation"); plt.close(fig)


def fig_wrong_side():
    d = load("D2_wrong_side.npz")
    if d is None:
        return
    cases = [(16, 2), (40, 3), (16, 8)]
    runs = [("D1", BLUE, "-", "D1 new init, $R'(0)=1$"), ("D2", ORANGE, "-", "D2 constant, $R'(0)=1$"), ("D3", AQUA, "-", "D3 constant, $R'(0)=0$")]
    fig, axs = plt.subplots(2, 3, figsize=(9.2, 4.8), sharex=True, sharey="row")
    for j, (N, K) in enumerate(cases):
        for tag, col, ls, lab in runs:
            t, th = d[f"{tag}_N{N}_K{K}_t"], d[f"{tag}_N{N}_K{K}_theta"]
            m = (t > 0) & (t <= 2e3)
            axs[0, j].plot(t[m], (th[:, IDX["b2"]] - th[:, IDX["b1"]])[m], color=col, ls=ls, label=lab)
            axs[1, j].plot(t[m], th[m, IDX["b1"]], color=col, ls=ls)
        axs[0, j].set_title(f"$N={N},\\ K={K}$", loc="left")
        axs[1, j].set_xlabel("training time $t$"); axs[1, j].set_xscale("log")
        for ax in (axs[0, j], axs[1, j]):
            ax.axhline(0, color=MUTED, lw=0.8)
    axs[0, 0].set_ylim(-1.0, 0.6); axs[1, 0].set_ylim(-0.3, 1.0)
    axs[0, 0].set_ylabel("$b_2-b_1$ (axis clipped)"); axs[1, 0].set_ylabel("$b_1$ (axis clipped)")
    axs[0, 2].legend(loc="lower left")
    fig.tight_layout(); save(fig, "fig_init_wrong_side"); plt.close(fig)


def main(cfg):
    N = cfg["A"]["N"]
    A1 = load("A1_reduced.npz"); A2 = load("A2_full.npz")
    sl = json.loads((RES / "A1_slopes.json").read_text())["slopes"]
    fig_rates(A1, A2, sl); fig_individual(A1, A2, sl, N); fig_gaps(A1, A2)
    if A2 is not None:
        fig_subspace(A2)
    fig_gen(N); fig_C(); fig_D(); fig_wrong_side()
    print("figures:", sorted(p.name for p in FIG.iterdir() if p.suffix in (".pdf", ".png")))
