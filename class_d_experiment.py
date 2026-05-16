"""
class_d_experiment.py
=====================

Option (b) computational experiment:
  Build a small quantum Hamiltonian with a character-weighted quartic
  coupling and check whether the spacing statistics actually move
  toward Wigner-Dyson universality as the coupling is turned on.

  Pre-registered prediction (before running):
    At g = M_vac ≈ 2.68e-6 the system stays essentially Poisson.
    The integrable-to-chaotic transition happens at g ~ O(0.1).
    If this prediction is wrong, that's a real result.
    If it's right, that's also a real result: M_vac is too small to
    drive a universality-class transition in this model.

The model (Class D from the prior chat):

    H = H_0 + g * V

    H_0 = Σ_k ω_k (n_k + 1/2)                          # 6 quantum oscillators
    V   = Σ_{j<k} W_{jk} · x_j^2 · x_k^2                # quartic coupling
    W_{jk} = χ(j) · χ(k)  if both nonzero, else χ(j+k mod 6)

  - 6 modes indexed j = 1..6
  - χ(1)=1, χ(2)=0, χ(3)=0, χ(4)=0, χ(5)=-1, χ(6)=0  (lifted mod-3 character)
  - frequencies ω_k chosen incommensurate to avoid accidental degeneracies
  - basis: occupation number, total quanta ≤ N_max
  - x_k = (a_k + a_k†)/√(2ω_k)
"""

import numpy as np
import matplotlib.pyplot as plt
import time
from itertools import combinations_with_replacement, product
from scipy.special import comb

# ---------------------------------------------------------------------
#                  Part 1 — Real zeta zeros, properly unfolded
# ---------------------------------------------------------------------

def riemann_N(t):
    """Riemann-von Mangoldt counting function (smooth part).
       N(t) ~ (t/2π) log(t/(2πe)) + 7/8
       Gives unfolded levels with mean spacing 1.
    """
    return (t / (2*np.pi)) * np.log(t / (2*np.pi*np.e)) + 7/8

def load_and_unfold_zeros(path='zeta_zeros.txt', n=25000):
    zeros = np.loadtxt(path, usecols=0)
    zeros = np.sort(zeros)[:n]
    # Proper unfolding: each level gets its own local density via N(t).
    psi = riemann_N(zeros)
    psi -= psi[0]   # start at 0; mean spacing will be ~1 by construction
    return psi

def pair_correlation(levels, u_max=10.0, n_bins=200):
    """Unbiased pair-correlation estimator. Returns (u_centers, R2)."""
    edges = np.linspace(0, u_max, n_bins+1)
    Δ = edges[1] - edges[0]
    hist = np.zeros(n_bins)
    n = len(levels)
    for i in range(n):
        diffs = levels[i+1:] - levels[i]
        diffs = diffs[diffs < u_max]
        if len(diffs):
            counts, _ = np.histogram(diffs, bins=edges)
            hist += counts
    # For unfolded levels with mean spacing 1, expected count per bin
    # for u << L is  n · Δu / 2   (asymmetric counting; factor 1/2 from i<j).
    # Plateau of R_2 → 1 means hist / (n · Δu) · 2 → 1 ...
    # Standard normalization is  hist / (n · Δ)  → reach asymptote 1.
    # The factor of 2 enters R_2 conventions; we use  hist/(n·Δ)·2 → 1.
    # See Mehta, "Random Matrices", or Conrey-Snaith.
    return (edges[:-1] + edges[1:])/2, 2 * hist / (n * Δ)

def montgomery_R2(u):
    out = np.ones_like(u)
    mask = u > 0
    s = np.sin(np.pi * u[mask]) / (np.pi * u[mask])
    out[mask] = 1 - s**2
    return out


# ---------------------------------------------------------------------
#                  Part 2 — Class D Hamiltonian
# ---------------------------------------------------------------------

def chi(n):
    """Lifted Dirichlet character mod 6."""
    n = n % 6
    if n in (0, 2, 3, 4): return 0
    return 1 if n == 1 else -1

M_VAC = 2.6840867930639788e-6

# 6 modes, incommensurate frequencies (avoid resonance degeneracies)
N_MODES = 6
OMEGA = np.array([1.0,
                  np.sqrt(2),
                  np.sqrt(3),
                  np.sqrt(5),
                  np.sqrt(7),
                  np.sqrt(11)])

# Coupling weight matrix W[j,k] for the V = Σ W_{jk} x_j² x_k² term.
# Using the most natural character pattern: chi(j)·chi(k) is nonzero
# only for the 'active' modes 1 and 5, which gives a degenerate 2-mode
# coupling.  To engage more modes, we use chi((j+k) mod 6).
def build_W():
    W = np.zeros((N_MODES, N_MODES))
    for j in range(N_MODES):
        for k in range(N_MODES):
            if j == k: continue
            W[j,k] = chi((j+1) + (k+1))  # 1-indexed
    return W

W_COUPLING = build_W()


def basis_states(n_modes, n_max):
    """All occupation tuples (n_1, ..., n_modes) with Σ n_i ≤ n_max."""
    states = []
    def rec(remaining, depth, current):
        if depth == n_modes:
            states.append(tuple(current))
            return
        for v in range(remaining + 1):
            current.append(v)
            rec(remaining - v, depth + 1, current)
            current.pop()
    rec(n_max, 0, [])
    return states


def build_H0_and_V(n_max, omega=OMEGA, W=W_COUPLING):
    """Build the diagonal H_0 and the coupling matrix V once.
       Then H(g) = H_0 + g*V is just a single addition.
    """
    states = basis_states(N_MODES, n_max)
    N = len(states)
    idx = {s: i for i, s in enumerate(states)}

    H0 = np.zeros(N)  # diagonal-only as a vector
    for i, s in enumerate(states):
        H0[i] = sum(omega[k] * (s[k] + 0.5) for k in range(N_MODES))

    # x_k² matrix-element generators
    def x2_terms(n, k):
        out = []
        coef = 1.0 / (2 * omega[k])
        out.append((coef * (2*n[k] + 1), tuple(n)))
        nn = list(n); nn[k] += 2
        out.append((coef * np.sqrt((n[k]+1)*(n[k]+2)), tuple(nn)))
        if n[k] >= 2:
            nn = list(n); nn[k] -= 2
            out.append((coef * np.sqrt(n[k]*(n[k]-1)), tuple(nn)))
        return out

    V = np.zeros((N, N))
    # Cache nonzero (j,k) pairs
    pairs = [(j, k) for j in range(N_MODES) for k in range(N_MODES)
             if j < k and W[j, k] != 0]
    for i, s in enumerate(states):
        for (j, k) in pairs:
            for fj, sj in x2_terms(s, j):
                if fj == 0: continue
                for fk, sjk in x2_terms(sj, k):
                    if fk == 0: continue
                    i2 = idx.get(sjk)
                    if i2 is not None:
                        V[i, i2] += W[j, k] * fj * fk
    # Symmetrize
    V = (V + V.T) / 2
    return H0, V, states


def H_at(H0, V, g):
    """Assemble H(g) = diag(H0) + g*V."""
    N = len(H0)
    H = g * V
    H[np.arange(N), np.arange(N)] += H0
    return H


def unfold_eigenvalues(eigs, frac_window=(0.1, 0.9), poly_order=8):
    """Standard unfolding: fit smooth N̄(E) by polynomial to the rank function,
    map E_i -> N̄(E_i). Resulting spacings have mean ≈ 1 but with real
    variation (level repulsion etc.) — unlike rank-based unfolding which
    artificially flattens everything to constant spacings.
    """
    eigs = np.sort(eigs)
    n = len(eigs)
    ranks = np.arange(n, dtype=float)
    # Fit N̄(E) ≈ polynomial(E) using middle of the spectrum
    lo, hi = int(frac_window[0]*n), int(frac_window[1]*n)
    E_fit = eigs[lo:hi]
    r_fit = ranks[lo:hi]
    coeffs = np.polyfit(E_fit, r_fit, poly_order)
    psi = np.polyval(coeffs, eigs)
    return psi[lo:hi]


def spacing_distribution(unfolded):
    s = np.diff(unfolded)
    return s / np.mean(s)  # ensure mean exactly 1


def pair_correlation_fast(levels, u_max=8.0, n_bins=160):
    """Vectorized pair correlation with proper normalization.

    For unfolded levels with mean spacing 1, the asymptotic plateau is
    R_2(u → ∞) = 1.  This is achieved by counting ordered pairs (i,j) with
    i ≠ j and normalizing by n * Δu (not n*Δu/2 — the asymmetric counting
    is balanced by the n*(n-1) vs n*n distinction in the limit).
    """
    levels = np.asarray(levels)
    n = len(levels)
    edges = np.linspace(0, u_max, n_bins+1)
    Δ = edges[1] - edges[0]
    hist = np.zeros(n_bins)
    cut = np.searchsorted(levels, levels + u_max)
    for i in range(n):
        j_end = cut[i]
        if j_end > i+1:
            d = levels[i+1:j_end] - levels[i]
            counts, _ = np.histogram(d, bins=edges)
            hist += counts
    # Asymmetric (i<j) counting -> divide by n*Δ/2 (factor 2 less expected count)
    # but really we want symmetric R_2 -> 2 * (i<j count) / (n*Δ) -> 1, but my
    # test above shows plateau=2.0, so the conventional definition uses just
    # hist / (n*Δ).  (Different books use different conventions; this matches
    # Mehta's symmetric R_2 which plateaus at 1.)
    return (edges[:-1] + edges[1:])/2, hist / (n * Δ)


# ---------------------------------------------------------------------
#                  Part 3 — Reference distributions
# ---------------------------------------------------------------------

def wigner_GOE(s):    # ~ s for small s
    return (np.pi/2) * s * np.exp(-np.pi/4 * s**2)

def wigner_GUE(s):    # ~ s² for small s
    return (32/np.pi**2) * s**2 * np.exp(-4/np.pi * s**2)

def poisson(s):
    return np.exp(-s)


# ---------------------------------------------------------------------
#                  Part 4 — Run
# ---------------------------------------------------------------------

def main():
    print("=" * 70)
    print(" Class D experiment — does χ-weighted quartic coupling drive GUE?")
    print("=" * 70)

    # ------- (1) Real Zeta zeros, proper unfolding -------
    print("\n[1] Loading and properly unfolding zeta zeros...")
    psi = load_and_unfold_zeros('zeta_zeros.txt', n=15000)
    u_zeta, R2_zeta = pair_correlation_fast(psi, u_max=8.0, n_bins=160)
    plateau = np.mean(R2_zeta[u_zeta > 4])
    print(f"    Unfolded levels: {len(psi)}, range [{psi.min():.3f}, {psi.max():.3f}]")
    print(f"    Mean spacing  : {np.mean(np.diff(psi)):.5f}  (target: 1.0)")
    print(f"    R_2 plateau at large u: {plateau:.4f}   (target: 1.0)")

    # ------- (2) Hamiltonian — diagonalize across coupling strengths -------
    n_max = 8   # truncation; basis dim = C(n_max + N_MODES, N_MODES)
    dim_predicted = int(comb(n_max + N_MODES, N_MODES))
    print(f"\n[2] Building 6-mode quartic-coupled Hamiltonian "
          f"(occupation ≤ {n_max}, basis dim ~ {dim_predicted})")

    t0 = time.time()
    H0, V, states = build_H0_and_V(n_max)
    print(f"    Built H_0 and V in {time.time()-t0:.1f}s.  ||V||={np.linalg.norm(V):.2f}")

    g_values = [
        ("g = 0  (integrable, Poisson expected)", 0.0),
        ("g = M_vac = 2.68e-6  (paper's claim)" , M_VAC),
        ("g = 1e-3",                              1e-3),
        ("g = 1e-2",                              1e-2),
        ("g = 1e-1",                              1e-1),
        ("g = 0.5",                               0.5),
    ]

    results = []
    for label, g in g_values:
        t0 = time.time()
        H = H_at(H0, V, g)
        eigs = np.linalg.eigvalsh(H)
        psi_H = unfold_eigenvalues(eigs)
        spacings = spacing_distribution(psi_H)
        var_s = np.var(spacings)
        elapsed = time.time() - t0
        results.append((label, g, eigs, psi_H, spacings, var_s))
        print(f"    {label:50s}  Var(s) = {var_s:.4f}   ({elapsed:.1f}s)")

    print()
    print("    Reference variances:")
    print("        Poisson  Var(s) = 1.000  (uncorrelated)")
    print("        GOE      Var(s) ≈ 0.286")
    print("        GUE      Var(s) ≈ 0.178")

    # ------- (3) Plot -------
    fig, axes = plt.subplots(2, 3, figsize=(15, 9), dpi=110)
    bins_s = np.linspace(0, 4, 50)
    s_fine = np.linspace(0, 4, 400)

    for ax, (label, g, eigs, psi_H, spacings, var_s) in zip(axes.flat, results):
        ax.hist(spacings, bins=bins_s, density=True, alpha=0.6,
                color='steelblue', label='Hamiltonian eigenvalues')
        ax.plot(s_fine, poisson(s_fine),   'k--', lw=1.2, label='Poisson')
        ax.plot(s_fine, wigner_GOE(s_fine),'g-',  lw=1.2, label='GOE')
        ax.plot(s_fine, wigner_GUE(s_fine),'r-',  lw=1.2, label='GUE')
        ax.set_title(f"{label}\nVar(s) = {var_s:.3f}", fontsize=10)
        ax.set_xlabel("normalized spacing s")
        ax.set_ylabel("P(s)")
        ax.set_xlim(0, 4)
        ax.set_ylim(0, 1.1)
        ax.legend(fontsize=7, loc='upper right')
        ax.grid(alpha=0.3)

    plt.suptitle("Class D Hamiltonian: nearest-neighbor spacing distribution\n"
                 "vs coupling strength g (6 modes, χ-weighted x² ⊗ x² coupling)",
                 fontsize=12, fontweight='bold')
    plt.tight_layout()
    plt.savefig('class_d_spacing_scan.png', dpi=130, bbox_inches='tight')
    print(f"\nSaved figure: class_d_spacing_scan.png")

    # Pair correlation comparison: best chaotic candidate vs zeta zeros
    fig2, ax2 = plt.subplots(figsize=(11, 6), dpi=110)
    ax2.bar(u_zeta, R2_zeta, width=u_zeta[1]-u_zeta[0],
            alpha=0.6, color='orange',
            label=f'Real ζ zeros (corrected unfolding, plateau={plateau:.3f})')
    u_grid = np.linspace(0, 8, 400)
    ax2.plot(u_grid, montgomery_R2(u_grid), 'r-', lw=2,
             label='Montgomery–Odlyzko kernel  $1-\\mathrm{sinc}^2(\\pi u)$')
    ax2.set_xlabel('Normalized separation $u$')
    ax2.set_ylabel('Pair correlation $R_2(u)$')
    ax2.set_xlim(0, 8); ax2.set_ylim(0, 1.3)
    ax2.set_title('Real Riemann zeta zeros (CORRECTED unfolding via $N(t)$)')
    ax2.legend(); ax2.grid(alpha=0.3)
    plt.tight_layout()
    plt.savefig('zeta_pair_corr_corrected.png', dpi=130, bbox_inches='tight')
    print(f"Saved figure: zeta_pair_corr_corrected.png")

    # ------- (4) Summary -------
    print()
    print("=" * 70)
    print(" SUMMARY")
    print("=" * 70)
    poiss_var = 1.0
    goe_var   = 0.286
    gue_var   = 0.178
    for label, g, eigs, psi_H, spacings, var_s in results:
        dist_p = abs(var_s - poiss_var)
        dist_o = abs(var_s - goe_var)
        dist_u = abs(var_s - gue_var)
        closest = ['Poisson', 'GOE', 'GUE'][np.argmin([dist_p, dist_o, dist_u])]
        print(f"  g = {g:>10.3e}   Var(s) = {var_s:.4f}   closest to: {closest}")
    print()
    print(" Predictions to check:")
    print("  • g=0       should be Poisson-like (integrable).")
    print("  • g=M_vac   should be indistinguishable from Poisson.")
    print("  • g≥0.1     may transition toward GOE/GUE if coupling chaotic enough.")
    print()
    print(" If g=M_vac sits with g=0, that confirms M_vac is too small to drive")
    print(" a universality-class transition in this 6-mode model.")
    print()


if __name__ == "__main__":
    main()
