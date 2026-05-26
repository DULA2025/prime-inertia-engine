"""
EXPERIMENT A: L(s, chi_-3) in the complex plane
Visualize the geometric structure of L(s, chi_-3):
  - The critical strip 0 < Re(s) < 1
  - The functional equation as reflection about Re(s) = 1/2
  - Zeros on the critical line (assuming GRH for this character)
  - Comparison with zeta
"""
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import hsv_to_rgb
import os

# Determine the directory of the current script for local file saving
script_dir = os.path.dirname(os.path.abspath(__file__))

mp.mp.dps = 25

def chi_primitive(n):
    """Primitive chi_-3 mod 3."""
    m = n % 3
    if m == 1: return 1
    if m == 2: return -1
    return 0

def L_chi(s):
    """L(s, chi_-3), primitive character mod 3."""
    s_c = mp.mpc(s)
    val = mp.mpf(3)**(-s_c) * (mp.zeta(s_c, mp.mpf(1)/3) - mp.zeta(s_c, mp.mpf(2)/3))
    return complex(val)

def find_zeros_on_critical_line(t_min, t_max, n_samples=2000):
    """Find zeros of L(1/2 + it, chi_-3) by sign changes of the Z-function."""
    ts = np.linspace(t_min, t_max, n_samples)
    vals = np.array([L_chi(0.5 + 1j*t) for t in ts])
   
    # Z-function-like real-valued function: rotate by the gamma factor's phase
    # For our purpose, just look at real and imaginary part sign changes
    re_vals = vals.real
   
    zeros = []
    for i in range(len(re_vals) - 1):
        if re_vals[i] * re_vals[i+1] < 0 and abs(vals[i].imag) < 0.5:
            # Refine via bisection
            lo, hi = ts[i], ts[i+1]
            for _ in range(40):
                mid = (lo + hi) / 2
                if L_chi(0.5 + 1j*mid).real * L_chi(0.5 + 1j*lo).real < 0:
                    hi = mid
                else:
                    lo = mid
            zeros.append((lo + hi) / 2)
    return zeros

print("=" * 72)
print(" EXPERIMENT A: L(s, chi_-3) geometric structure in the complex plane")
print("=" * 72)
print()

# Plot 1: Domain coloring of L(s, chi_-3) over critical strip
print("Plot A.1: Domain coloring of L(s, chi_-3) over the critical strip")
sigma_range = np.linspace(-1, 2, 400)
t_range = np.linspace(0, 30, 600)
S, T = np.meshgrid(sigma_range, t_range)
print(" Computing L on grid...")
L_vals = np.zeros_like(S, dtype=complex)
for i in range(S.shape[0]):
    for j in range(S.shape[1]):
        try:
            L_vals[i, j] = L_chi(S[i, j] + 1j * T[i, j])
        except Exception:
            L_vals[i, j] = np.nan
    if i % 60 == 0:
        print(f" row {i}/{S.shape[0]}")

# Domain coloring: hue = phase, brightness = magnitude
def domain_color(z):
    """Convert complex z to color via phase=hue, magnitude=brightness."""
    h = (np.angle(z) / (2 * np.pi)) % 1
    mag = np.abs(z)
    # log-scaled brightness
    v = np.clip(1 - 1 / (1 + np.log1p(mag)), 0, 1)
    s = np.ones_like(h) * 0.85
    hsv = np.stack([h, s, v], axis=-1)
    return hsv_to_rgb(hsv)

colors = domain_color(L_vals)
fig, axes = plt.subplots(1, 2, figsize=(14, 7), dpi=110)
ax = axes[0]
ax.imshow(colors, extent=[sigma_range[0], sigma_range[-1], t_range[0], t_range[-1]],
          origin='lower', aspect='auto', interpolation='bilinear')
ax.axvline(0.5, color='white', linestyle='--', alpha=0.7, linewidth=1.5, label='Re(s) = 1/2')
ax.axvline(0, color='cyan', alpha=0.3)
ax.axvline(1, color='cyan', alpha=0.3)
ax.set_xlabel('Re(s) = σ')
ax.set_ylabel('Im(s) = t')
ax.set_title('Domain coloring of L(s, χ_{-3})')
ax.legend(loc='upper right', fontsize=9)

# Plot 2: |L(1/2 + it, chi)| along critical line, vs |zeta(1/2 + it)|
ax = axes[1]
ts_fine = np.linspace(0, 40, 800)
L_critical = np.array([abs(L_chi(0.5 + 1j*t)) for t in ts_fine])
zeta_critical = np.array([abs(complex(mp.zeta(mp.mpc(0.5, t)))) for t in ts_fine])
ax.plot(ts_fine, L_critical, 'b-', linewidth=1.5, label='|L(1/2 + it, χ_{-3})|')
ax.plot(ts_fine, zeta_critical, 'r--', linewidth=1, alpha=0.6, label='|ζ(1/2 + it)|')
ax.set_xlabel('t')
ax.set_ylabel('|L(1/2 + it)|')
ax.set_title('Magnitude along critical line')
ax.legend(fontsize=9)
ax.grid(True, alpha=0.3)
ax.set_xlim(0, 40)
plt.tight_layout()

# Save figure to the same directory as this script
png_path = os.path.join(script_dir, 'experiment_A_critical_strip.png')
plt.savefig(png_path, dpi=120, bbox_inches='tight')
plt.close()
print(f" Saved {png_path}")

# Now extract the zeros numerically
print()
print("Computing zeros of L(s, χ_{-3}) on critical line:")
zeros = find_zeros_on_critical_line(1, 40, 4000)
print(f" Found {len(zeros)} zeros in [1, 40]:")
for i, z in enumerate(zeros):
    print(f" γ_{i+1} = {z:.6f}")

# Save zeros to file in the same directory as this script
json_path = os.path.join(script_dir, 'zeros_chi_m3.json')
import json
with open(json_path, 'w') as f:
    json.dump(zeros, f)
print(f" Saved {len(zeros)} zeros to {json_path}")

# Comparison: Riemann zeta zeros in the same range
print()
print("Comparison: ordinates of zeta zeros in [1, 40]:")
zeta_zeros = []
for k in range(1, 20):
    z = float(mp.im(mp.zetazero(k)))
    if z <= 40:
        zeta_zeros.append(z)
    else:
        break
for i, z in enumerate(zeta_zeros):
    print(f" ζ_{i+1} = {z:.6f}")

# Density comparison
print()
print(f" Density of L(s, χ_{-3}) zeros in [0, 40]: {len(zeros)} zeros")
print(f" Density of ζ(s) zeros in [0, 40]: {len(zeta_zeros)} zeros")
print()
print(" Expected from Riemann–von Mangoldt-like formula:")
print(f" N_L(T) ~ (T/2π) log(T/2π·q) for L(s, χ) with conductor q=3")
T = 40
N_expected_L = (T/(2*np.pi)) * np.log(T*3/(2*np.pi))
N_expected_zeta = (T/(2*np.pi)) * np.log(T/(2*np.pi))
print(f" Expected for L: {N_expected_L:.2f}")
print(f" Expected for zeta: {N_expected_zeta:.2f}")
