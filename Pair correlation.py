import numpy as np
import matplotlib.pyplot as plt

# ================================================
# LOAD REAL RIEMANN ZETA ZEROS
# ================================================
print("Loading real zeta zeros...")
zeros = np.loadtxt('zeta_zeros.txt', usecols=0)  # first column only
zeros = np.sort(zeros)[:25000]                   # take first 25k zeros (~ height ~10^13)

# Unfold to mean density = 1 (local density ~ log(T)/(2π))
T = zeros[-1]
mean_density = np.log(T) / (2 * np.pi)
levels_real = (zeros - zeros[0]) * mean_density

print(f"Loaded {len(levels_real):,} real Riemann zeta zeros (unfolded)")

# ================================================
# PAIR CORRELATION (same as before, correct normalization)
# ================================================
def compute_pair_correlation(levels, max_u=12.0, bins=400):
    n = len(levels)
    hist = np.zeros(bins, dtype=float)
    bin_edges = np.linspace(0, max_u, bins + 1)
    bin_width = bin_edges[1] - bin_edges[0]
    
    print("Computing pair differences for real zeros...")
    for i in range(n):
        diffs = levels[i+1:] - levels[i]
        diffs = diffs[diffs < max_u]
        if len(diffs) > 0:
            counts, _ = np.histogram(diffs, bins=bin_edges)
            hist += counts
    
    r2_est = hist / (n * bin_width)
    bin_centers = (bin_edges[:-1] + bin_edges[1:]) / 2
    return bin_centers, r2_est, bin_width

u_real, r2_real, bin_width = compute_pair_correlation(levels_real)

# ================================================
# THEORETICAL MONTGOMERY KERNEL
# ================================================
def montgomery_r2(u):
    with np.errstate(divide='ignore', invalid='ignore'):
        sinc = np.sin(np.pi * u) / (np.pi * u)
    sinc[0] = 1.0
    return 1.0 - sinc**2

x_fine = np.linspace(0, 12, 2000)

# ================================================
# PLOT — EXACTLY LIKE YOUR ORIGINAL X POST
# ================================================
plt.figure(figsize=(11, 7), dpi=140)
plt.bar(u_real, r2_real, width=bin_width, alpha=0.85, color='orange', label='Real Riemann zeta zeros')
plt.plot(x_fine, montgomery_r2(x_fine), 'r-', lw=3, label='Montgomery kernel (theory)')
plt.title('Pair Correlation — Real Riemann Zeta Zeros\n(Overlay on Montgomery–Odlyzko law)', fontsize=15, fontweight='bold')
plt.xlabel('Normalized separation $u$', fontsize=13)
plt.ylabel('Pair correlation $R_2(u)$', fontsize=13)
plt.legend(fontsize=12)
plt.grid(True, alpha=0.3)
plt.tight_layout()
plt.show()
