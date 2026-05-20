import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import brentq
import mpmath

mpmath.mp.dps = 20
chi = [0, 1, -1]
q = 3

def Z(t):
    t_mp = mpmath.mpf(t)
    s = mpmath.mpc(0.5, t_mp)
    gamma_term = mpmath.loggamma(mpmath.mpc(0.75, t_mp/2))
    theta = mpmath.im(gamma_term) - (t_mp/2) * mpmath.log(mpmath.pi / q)
    L_val = mpmath.dirichlet(s, chi)
    z_val = mpmath.exp(1j * theta) * L_val
    return float(mpmath.re(z_val))

def find_zeros(max_t=120, step=0.2):
    print("Finding zeros of L(s, χ_{-3})...")
    t_vals = np.arange(2, max_t, step)
    z_vals = [Z(t) for t in t_vals]
    zeros = []
    for i in range(len(t_vals)-1):
        if np.sign(z_vals[i]) != np.sign(z_vals[i+1]):
            root = brentq(Z, t_vals[i], t_vals[i+1])
            zeros.append(root)
    print(f"Found {len(zeros)} zeros up to t ≈ {max_t}")
    return np.array(zeros)

def dula_character(d):
    m = d % 3
    if m == 1: return 1
    if m == 2: return -1
    return 0

def compute_error(N_max):
    print(f"Computing error term up to N = {N_max:,}...")
    r = np.zeros(N_max + 1, dtype=float)
    r[0] = 1
    for d in range(1, N_max + 1):
        chi = dula_character(d)
        if chi != 0:
            r[d::d] += 6 * chi
    R = np.cumsum(r)
    Area = (2 * np.pi / np.sqrt(3)) * np.arange(N_max + 1)
    return R - Area

# ====================== MAIN ======================
zeros = find_zeros(max_t=120)

N_max = 500_000
Error = compute_error(N_max)
N_vals = np.arange(N_max + 1)          # Now includes 0 to N_max (length 500001)

# Approximate Explicit Formula
print("Building explicit formula approximation...")
Explicit = np.zeros(N_max + 1)

for gamma in zeros:
    rho = 0.5 + 1j * gamma
    # Use N_vals (includes 0)
    term = (N_vals ** (rho / 2)) / (rho * np.abs(rho))
    Explicit += 2 * np.real(term)

# ====================== IMPROVED PLOT ======================
plt.style.use('seaborn-v0_8-whitegrid')
fig, ax = plt.subplots(figsize=(14, 7), dpi=150)

# Plot only up to 300,000 for clarity
ax.plot(N_vals[:300001], Error[:300001], 
        label='Numerical Error $E(N)$ (from DULA character)', 
        color='#008B8B', linewidth=0.7, alpha=0.85)

ax.plot(N_vals[:300001], Explicit[:300001], 
        label='Explicit Formula (sum over first 58 zeros of $L(s, \\chi_{-3})$)', 
        color='#DC143C', linewidth=1.4, alpha=0.9)

ax.axhline(0, color='black', linestyle='--', linewidth=1.2, alpha=0.7)

# Professional formatting
ax.set_title(r'Hexagonal Circle Problem for Eisenstein Lattice $A_2$' + '\n' +
             r'Numerical Error vs Explicit Formula from Zeros of $L(s, \chi_{-3})$', 
             fontsize=15, fontweight='bold', pad=20)

ax.set_xlabel(r'Squared Radius $N$', fontsize=13)
ax.set_ylabel(r'Error Term $E(N)$', fontsize=13)
ax.legend(fontsize=11, loc='upper right', framealpha=0.95)
ax.set_xlim(0, 300000)
ax.grid(True, alpha=0.3, linestyle='--')

plt.tight_layout()
plt.show()

print("\nPlot generated successfully!")
