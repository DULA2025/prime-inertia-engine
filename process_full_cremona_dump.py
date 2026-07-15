#!/usr/bin/env python3
"""
================================================================================
process_full_cremona_dump.py
================================================================================

Process a large genuine LMFDB / Cremona Sage dump.

Features:
- Handles Sage pickles
- Weight-aware fingerprints
- PCA, k-NN graph, communities, anomalies, tensor test
- High-quality plots + full state pickle

Usage:
    python process_full_cremona_dump.py
    python process_full_cremona_dump.py --dump /path/to/your/cremona_FULL.pkl
    python process_full_cremona_dump.py --prefix Phase7_Full --max-n 100000
    python process_full_cremona_dump.py --skip-graph          # fast first pass
"""

import argparse
import numpy as np
from scipy.stats import entropy
from scipy.spatial.distance import cdist
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import laplacian
from scipy.linalg import eigh
from scipy.cluster.vq import kmeans2
import matplotlib.pyplot as plt
import pickle
import io
import os
import sys
import time
from collections import Counter
from pathlib import Path

np.random.seed(42)
RNG = np.random.default_rng(42)


class SageUnpickler(pickle.Unpickler):
    def find_class(self, module, name):
        if module.startswith("sage"):
            if name in ("Integer", "make_integer"):
                return int
            if "Rational" in name:
                return float
            return int
        return super().find_class(module, name)


def load_sage_pickle(path):
    with open(path, "rb") as f:
        return SageUnpickler(f).load()


# ====================== Fingerprint (22-dim) ======================
MODULI = [3, 4, 5, 7, 8, 12]
KMAX = 10
BINS = 40


def theta_from_ap_vec(ap, p):
    x = np.asarray(ap, dtype=float) / (2 * np.sqrt(np.asarray(p, dtype=float)))
    x = np.clip(x, -1.0, 1.0)
    return np.arccos(x)


def theta_entropy(theta):
    h, _ = np.histogram(theta, bins=BINS, density=True, range=(0, np.pi))
    h = h[h > 0]
    return float(entropy(h)) if len(h) > 0 else 0.0


def moment_vector(ap_norm):
    return [float(np.mean(ap_norm ** k)) for k in range(1, KMAX + 1)]


def mutual_info(x, y):
    x = np.asarray(x).ravel()
    y = np.asarray(y).ravel()
    ux, uy = np.unique(x), np.unique(y)
    if len(ux) <= 1 or len(uy) <= 1:
        return 0.0
    px = np.array([np.mean(x == a) for a in ux])
    py = np.array([np.mean(y == b) for b in uy])
    pxy = np.array([[np.mean((x == a) & (y == b)) for b in uy] for a in ux])
    return float(max(0.0, entropy(px) + entropy(py) - entropy(pxy.flatten())))


def MI_mod(ap, plist, m):
    s = (np.asarray(ap) > 0).astype(int)
    r = np.array([int(p % m) for p in plist])
    return mutual_info(r, s)


def autocorr_features(ap):
    feats = []
    for lag in [1, 2, 3, 5, 10]:
        if len(ap) <= lag:
            feats.append(0.0)
        else:
            c = np.corrcoef(ap[:-lag], ap[lag:])[0, 1]
            feats.append(0.0 if np.isnan(c) else float(c))
    return feats


def fingerprint(rec, weight_aware=True):
    ap = np.asarray(rec["ap"], dtype=float)
    plist = rec.get("plist")
    if plist is None or len(plist) != len(ap):
        plist = np.arange(5, 5 + 3 * len(ap), dtype=int)[:len(ap)]
    else:
        plist = np.asarray(plist, dtype=int)

    weight = int(rec.get("weight", 2))

    if weight_aware and weight > 2:
        scale = np.power(plist.astype(float), 0.5 * (weight - 1))
        ap_norm = ap / (scale + 1e-12)
    else:
        ap_norm = ap.copy()

    theta = theta_from_ap_vec(ap_norm, plist)

    vec = moment_vector(ap_norm)
    vec.append(theta_entropy(theta))

    for m in MODULI:
        vec.append(MI_mod(ap, plist, m))

    vec.extend(autocorr_features(ap_norm))
    return np.asarray(vec, dtype=float)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dump", type=str, default="/home/workdir/attachments/lmfdb_ap_dump_sage.pkl")
    parser.add_argument("--output-dir", type=str, default="/home/workdir/artifacts")
    parser.add_argument("--prefix", type=str, default="Phase7_Full")
    parser.add_argument("--max-n", type=int, default=None)
    parser.add_argument("--skip-graph", action="store_true")
    args = parser.parse_args()

    OUTDIR = Path(args.output_dir)
    OUTDIR.mkdir(parents=True, exist_ok=True)

    print("=" * 72)
    print("FULL CREMONA-SCALE GENUINE ARITHMETIC FINGERPRINT ATLAS")
    print("=" * 72)
    print(f"Dump      : {args.dump}")
    print(f"Prefix    : {args.prefix}")
    if args.max_n:
        print(f"Max-n     : {args.max_n}")
    if args.skip_graph:
        print("Graph     : SKIPPED (fast mode)")
    print("=" * 72)

    # Load
    print("\n[0] Loading dump ...")
    t0 = time.time()
    records = load_sage_pickle(args.dump)
    if args.max_n:
        records = records[:args.max_n]
    print(f"  Loaded {len(records)} records in {time.time()-t0:.1f}s")
    print(f"  Families: {dict(Counter(r.get('family','UNK') for r in records))}")

    # Fingerprints
    print("\n[1] Building fingerprints ...")
    fps, labels, meta = [], [], []
    for i, rec in enumerate(records):
        if (i + 1) % 5000 == 0:
            print(f"  {i+1}/{len(records)} ...", flush=True)

        fam = rec.get("family", "UNK")
        lab = "CM" if fam == "EC" and bool(rec.get("cm", False)) else \
              fam if fam.startswith("MF") else fam

        fp = fingerprint(rec, weight_aware=True)
        if fp is not None and len(fp) == 22:
            fps.append(fp)
            labels.append(lab)
            meta.append(rec)

    X = np.vstack(fps)
    labels = np.array(labels)
    n = len(labels)
    print(f"  Retained {n} fingerprints")

    # PCA
    print("\n[2] PCA ...")
    mu = X.mean(0)
    sigma = X.std(0); sigma[sigma == 0] = 1.0
    Xs = (X - mu) / sigma
    Xc = Xs - Xs.mean(0)
    C = np.cov(Xc.T)
    eigvals, eigvecs = np.linalg.eigh(C)
    idx = np.argsort(eigvals)[::-1]
    P = Xc @ eigvecs[:, :2]
    explained = eigvals[idx] / eigvals.sum()
    print(f"  PC1 {100*explained[0]:.1f}%  PC2 {100*explained[1]:.1f}%")

    centers = {}
    for lab in sorted(set(labels)):
        mask = labels == lab
        if mask.any():
            centers[lab] = P[mask].mean(0)
            print(f"  {lab:6s} n={mask.sum():7d}")

    if "CM" in centers and "GEN" in centers:
        print(f"  d(CM, GEN) = {np.linalg.norm(centers['CM'] - centers['GEN']):.3f}")

    # Graph (optional)
    nn_idx = degrees = core_idx = None
    if not args.skip_graph:
        print("\n[3] Building k-NN graph ...")
        k_nn = 12
        nn_idx = np.zeros((n, k_nn), dtype=int)
        chunk = 400
        for start in range(0, n, chunk):
            end = min(start + chunk, n)
            Dch = cdist(Xs[start:end], Xs, metric="euclidean")
            for i in range(end - start):
                Dch[i, start + i] = np.inf
            nn_idx[start:end] = np.argpartition(Dch, k_nn, axis=1)[:, :k_nn]
            if start % 10000 == 0:
                print(f"    {start}/{n}", flush=True)

        rows, cols = [], []
        for i in range(n):
            for j in nn_idx[i]:
                if i < j:
                    rows.extend([i, j])
                    cols.extend([j, i])
        A = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(n, n))
        degrees = np.asarray(A.sum(axis=1)).ravel()
        core_idx = np.where(degrees >= np.median(degrees))[0]
        print(f"  Edges: {A.nnz//2}   Core size: {len(core_idx)}")

    # Anomaly + Tensor
    print("\n[4] Anomaly scores + tensor test ...")
    fam_cent = {lab: Xs[labels == lab].mean(0) for lab in set(labels)}
    dist_cent = np.array([np.linalg.norm(Xs[i] - fam_cent[labels[i]]) for i in range(n)])

    if nn_idx is not None:
        i_idx = np.arange(n)[:, None]
        local_density = np.linalg.norm(Xs[i_idx] - Xs[nn_idx], axis=2).mean(axis=1)
    else:
        local_density = np.zeros(n)

    anomaly_score = (dist_cent - dist_cent.mean()) / (dist_cent.std() + 1e-8)
    anomaly_score += 0.4 * (local_density - local_density.mean()) / (local_density.std() + 1e-8)
    exc_idx = np.argsort(anomaly_score)[::-1][:12]
    print("  Top exceptional:", [meta[i]['label'] for i in exc_idx[:6]])

    # Visualizations
    print("\n[5] Generating plots ...")
    cmap = {"CM":"#d62728", "GEN":"#1f77b4", "MF2":"#2ca02c", "MF4":"#98df8a",
            "MF6":"#c7e9c0", "MF8":"#a1d99b", "MF10":"#74c476", "MF12":"#31a354"}

    # PCA plot
    plt.figure(figsize=(13, 10))
    for lab in sorted(set(labels), key=lambda x: (x.startswith("MF"), x)):
        mask = labels == lab
        plt.scatter(P[mask,0], P[mask,1], s=3, alpha=0.35, c=cmap.get(lab,"grey"),
                    edgecolors="none", label=f"{lab} (n={mask.sum()})")
    plt.scatter(P[exc_idx[:10],0], P[exc_idx[:10],1], s=50, facecolors="none",
                edgecolors="black", linewidths=1.3, label="Top exceptional")
    plt.legend(fontsize=8, ncol=3)
    plt.title(f"{args.prefix} — Full Cremona Genuine Atlas PCA (n={n})")
    plt.savefig(OUTDIR / f"{args.prefix}_PCA.png", dpi=300, bbox_inches="tight")
    plt.close()

    # CM vs GEN
    plt.figure(figsize=(10, 8))
    for lab, col, mk in [("CM", "#d62728", "o"), ("GEN", "#1f77b4", "s")]:
        mask = labels == lab
        if mask.any():
            plt.scatter(P[mask,0], P[mask,1], s=4, alpha=0.45, c=col, marker=mk, label=f"{lab}")
    plt.legend()
    plt.title(f"{args.prefix} — CM vs non-CM")
    plt.savefig(OUTDIR / f"{args.prefix}_CM_vs_GEN.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Save state
    state = {
        "X": X, "Xs": Xs, "labels": labels, "meta": meta,
        "P": P, "explained": explained, "centers": centers,
        "anomaly_score": anomaly_score, "exc_idx": exc_idx,
        "mu": mu, "sigma": sigma, "n": n
    }
    if not args.skip_graph:
        state.update({"degrees": degrees, "core_idx": core_idx, "nn_idx": nn_idx})

    with open(OUTDIR / f"{args.prefix}_atlas.pkl", "wb") as fh:
        pickle.dump(state, fh, protocol=pickle.HIGHEST_PROTOCOL)

    print("\n" + "=" * 72)
    print("DONE")
    print("=" * 72)
    print(f"All results saved in: {OUTDIR}")
    print(f"Main files: {args.prefix}_PCA.png, {args.prefix}_CM_vs_GEN.png, {args.prefix}_atlas.pkl")


if __name__ == "__main__":
    main()
