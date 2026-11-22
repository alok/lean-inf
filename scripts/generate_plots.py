#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = ["matplotlib>=3.9", "numpy>=2.0"]
# ///
"""Generate publication-quality plots directly from `lean-inf` JSON outputs.

Produces:
  1. plots/step_function_finite_eval.png
     Three-panel figure showing L_N(x), L'_N(x) (Dirac delta peak N/4, area 1),
     and L''_N(x) (dipole) for N = 10, 40, 100 with Lean 4 `evalFinite(H -> N)` points overlaid.
  2. plots/benchmark_speedups.png
     Two-panel figure showing real measured Lean 4 wall-clock timings for
     Naive HashMap vs Verified Balanced-Tree vs Verified Karatsuba multiplication,
     plus speedup bars for signum, pow, and Newton inversion.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


REPO_ROOT = Path(__file__).resolve().parent.parent
INF_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "inf"
PLOTS_DIR = REPO_ROOT / "plots"


def run_inf_json(args: list[str]) -> dict[str, Any]:
    proc = subprocess.run(
        [str(INF_BIN), *args],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )
    return json.loads(proc.stdout)


def make_step_plot() -> None:
    ns = [10.0, 40.0, 100.0]
    colors = ["#6366f1", "#0ea5e9", "#dc2626"]
    datasets = [run_inf_json(["step-demo", "--N", str(int(n)), "--json"]) for n in ns]

    plt.rcParams.update({
        "font.family": "serif",
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.grid": True,
        "grid.alpha": 0.25,
    })

    fig, axes = plt.subplots(1, 3, figsize=(15.5, 4.6), dpi=220)
    x_grid = np.linspace(-0.4, 0.4, 1000)

    # Panel 1: Step function L_N(x)
    ax = axes[0]
    ax.step([-0.4, 0.0, 0.4], [0.0, 1.0, 1.0], where="post",
            color="#111827", ls="--", lw=1.4, alpha=0.6, label=r"Heaviside $U(x)$")
    for n, col, data in zip(ns, colors, datasets):
        y = 1.0 / (1.0 + np.exp(-n * x_grid))
        ax.plot(x_grid, y, color=col, lw=2.0, label=rf"$H \mapsto N = {int(n)}$")
        xs_lc = [s["x_finite"] for s in data["samples"] if abs(s["x_finite"]) <= 0.4]
        ys_lc = [s["step_finite"] for s in data["samples"] if abs(s["x_finite"]) <= 0.4]
        ax.scatter(xs_lc[::2], ys_lc[::2], color=col, s=16, zorder=4, alpha=0.85)
    ax.set_title(r"Nonstandard Step $L_H(x) = \frac{1}{1 + e^{-Hx}}$", fontsize=11.5, pad=10)
    ax.set_xlabel(r"$x = c\varepsilon \mapsto c / N$")
    ax.set_ylabel(r"$L_N(x)$")
    ax.set_xlim(-0.4, 0.4)
    ax.set_ylim(-0.08, 1.12)
    ax.legend(frameon=False, fontsize=8.5, loc="lower right")

    # Panel 2: First derivative L'_N(x) (Dirac delta spike = N/4)
    ax = axes[1]
    for n, col, data in zip(ns, colors, datasets):
        s_val = 1.0 / (1.0 + np.exp(-n * x_grid))
        dy = n * s_val * (1.0 - s_val)
        ax.plot(x_grid, dy, color=col, lw=2.0,
                label=rf"$N={int(n)}$ (peak $N/4={n/4:.1f}$)")
        xs_lc = [s["x_finite"] for s in data["samples"] if abs(s["x_finite"]) <= 0.4]
        dys_lc = [s["deriv_finite"] for s in data["samples"] if abs(s["x_finite"]) <= 0.4]
        ax.scatter(xs_lc[::2], dys_lc[::2], color=col, s=18, zorder=4, marker="o",
                   edgecolors="white", linewidths=0.4)
    ax.annotate(
        r"Lean 4 AD at $x=0$:" + "\n" + r"$D_{\varepsilon^2} L_H(0) = \frac{1}{4}H - \frac{1}{48}\varepsilon + \dots$" + "\n" + r"$H \mapsto 100 \;\Rightarrow\; 25.0$",
        xy=(0.0, 25.0), xytext=(0.09, 20.5),
        fontsize=8.5,
        bbox={"boxstyle": "round,pad=0.35", "fc": "#fef2f2", "ec": "#dc2626", "lw": 0.9},
        arrowprops={"arrowstyle": "->", "color": "#dc2626", "lw": 1.1},
    )
    ax.set_title(r"1st Derivative $L'_H(x)$ (Dirac Delta, Area $= 1$)", fontsize=11.5, pad=10)
    ax.set_xlabel(r"$x = c\varepsilon \mapsto c / N$")
    ax.set_ylabel(r"$L'_N(x)$")
    ax.set_xlim(-0.4, 0.4)
    ax.legend(frameon=False, fontsize=8.2, loc="upper left")

    # Panel 3: Second derivative L''_N(x) (Dipole moment)
    ax = axes[2]
    x_zoom = np.linspace(-0.15, 0.15, 800)
    for n, col, data in zip([10.0, 40.0, 100.0], colors, datasets):
        s_val = 1.0 / (1.0 + np.exp(-n * x_zoom))
        d2y = (n * n) * s_val * (1.0 - s_val) * (1.0 - 2.0 * s_val)
        ax.plot(x_zoom, d2y / (n * n), color=col, lw=1.9, alpha=0.85,
                label=rf"$N={int(n)}$ (scaled $/N^2$)")
        if n == 100.0:
            xs_lc = [s["x_finite"] for s in data["samples"] if abs(s["x_finite"]) <= 0.15]
            d2s_lc = [s["deriv2_finite"] / (n * n) for s in data["samples"] if abs(s["x_finite"]) <= 0.15]
            ax.scatter(xs_lc[::2], d2s_lc[::2], color=col, s=18, zorder=4,
                       edgecolors="white", linewidths=0.4, label=r"Lean 4 $D^2_{\varepsilon^2}$ ($N=100$)")
    ax.axhline(0.0, color="#6b7280", lw=0.8, ls=":")
    ax.set_title(r"2nd Derivative $L''_H(x) / N^2$ (Dipole)", fontsize=11.5, pad=10)
    ax.set_xlabel(r"$x = c\varepsilon \mapsto c / N$")
    ax.set_ylabel(r"$L''_N(x) / N^2 = \sigma''(Nx)$")
    ax.set_xlim(-0.15, 0.15)
    ax.legend(frameon=False, fontsize=8.0, loc="upper right")

    area_100 = datasets[-1]["riemann_area_finite"]
    fig.suptitle(
        f"lean-inf: Pure Levi-Civita AD of Step Function & Finite Specialization (H ↦ N)  |  Dots = Lean 4 evalFinite(N)  |  Hyperfinite Area = {area_100:.4f}",
        fontsize=12.5, fontweight="bold", y=1.02,
    )
    fig.tight_layout()
    PLOTS_DIR.mkdir(parents=True, exist_ok=True)
    out = PLOTS_DIR / "step_function_finite_eval.png"
    fig.savefig(out, bbox_inches="tight")
    plt.close(fig)
    print(f"Wrote {out}")


def make_bench_plot(bench_data: dict[str, Any]) -> None:
    rows = bench_data["benchmarks"]
    dense = [r for r in rows if r["category"] == "mul_dense"]
    others = [r for r in rows if r["category"] in ("signum", "pow", "inv", "mul_sparse")]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.2, 4.8), dpi=220)

    # Panel 1: Multiplication scaling (log-log)
    sizes = [r["size"] for r in dense]
    naive = [r["naive_us"] for r in dense]
    sparse = [r["sparse_us"] for r in dense]
    fast = [r["fast_us"] for r in dense]

    ax1.loglog(sizes, naive, "o-", color="#ef4444", lw=2.2, ms=6, label=r"Original Naive HashMap $O(n^2)$")
    ax1.loglog(sizes, sparse, "s--", color="#f59e0b", lw=2.0, ms=5.5, label=r"Verified Balanced Tree (mulTree) $O(n^2 \log n)$")
    ax1.loglog(sizes, fast, "^-", color="#10b981", lw=2.4, ms=6.5, label=r"Verified Karatsuba (FastLC.mul) $O(n^{1.585})$")
    ax1.set_title("Dense Levi-Civita Multiplication (Lean 4 Native)", fontsize=11.5, pad=10)
    ax1.set_xlabel("Number of terms $n$")
    ax1.set_ylabel("Mean time per multiply (µs, log scale)")
    ax1.set_xticks(sizes)
    ax1.get_xaxis().set_major_formatter(plt.ScalarFormatter())
    ax1.legend(frameon=False, fontsize=8.5, loc="upper left")

    # Annotate largest speedup cleanly below the curve
    if dense:
        last = dense[-1]
        ax1.annotate(
            f"{last['speedup']:.1f}× faster\nat n={last['size']}",
            xy=(last["size"], last["fast_us"]),
            xytext=(last["size"] * 0.48, last["fast_us"] * 0.14),
            fontsize=9.5, fontweight="bold", color="#047857",
            bbox={"boxstyle": "round,pad=0.3", "fc": "#ecfdf5", "ec": "#10b981", "lw": 0.9},
            arrowprops={"arrowstyle": "->", "color": "#047857", "lw": 1.3},
        )

    # Panel 2: Speedup bar chart across largest tested size per category
    best_by_cat: dict[str, dict[str, Any]] = {}
    for r in rows:
        best_by_cat[r["category"]] = r
    labels_map = {
        "mul_dense": "Dense Mul\n(Karatsuba, n=512)",
        "mul_sparse": "Sparse Mul\n(mulTree, n=64)",
        "signum": "signum\n(O(1), n=256)",
        "pow": "Power x^k\n(Binary, k=48)",
        "inv": "Inverse 1/x\n(Newton, ord=40)",
    }
    cats = ["mul_dense", "mul_sparse", "signum", "pow", "inv"]
    bar_labels = [labels_map[c] for c in cats if c in best_by_cat]
    speedups = [best_by_cat[c]["speedup"] for c in cats if c in best_by_cat]
    bar_colors = ["#10b981", "#0ea5e9", "#6366f1", "#8b5cf6", "#ec4899"]

    bars = ax2.bar(range(len(bar_labels)), speedups, color=bar_colors[:len(bar_labels)], width=0.58)
    ax2.set_yscale("log")
    ax2.set_xticks(range(len(bar_labels)))
    ax2.set_xticklabels(bar_labels, fontsize=8.5)
    ax2.set_ylabel("Speedup over Original Naive (×, log scale)")
    ax2.set_title("Verified Refactor Speedups (Zero-sorry Lean 4 Proofs)", fontsize=11.5, pad=10)
    for bar, sp in zip(bars, speedups):
        ax2.text(
            bar.get_x() + bar.get_width() / 2.0,
            sp * 1.15,
            f"{sp:.1f}×",
            ha="center", va="bottom", fontsize=9, fontweight="bold",
        )
    ax2.set_ylim(1.0, max(speedups) * 2.8)

    fig.suptitle("lean-inf: Verified Refactoring Performance (Naive HashMap vs Verified FastLC)",
                 fontsize=12.5, fontweight="bold", y=1.02)
    fig.tight_layout()
    out = PLOTS_DIR / "benchmark_speedups.png"
    fig.savefig(out, bbox_inches="tight")
    plt.close(fig)
    print(f"Wrote {out}")


def main() -> None:
    make_step_plot()
    bench = run_inf_json(["bench", "--json"])
    (PLOTS_DIR / "bench_results.json").write_text(json.dumps(bench, indent=2) + "\n")
    make_bench_plot(bench)


if __name__ == "__main__":
    main()
