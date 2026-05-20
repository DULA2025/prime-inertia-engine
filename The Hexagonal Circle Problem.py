import numpy as np
import matplotlib.pyplot as plt
from scipy.fft import fft, fftfreq

def dula_character(d):
    m = d % 3
    if m == 1: return 1
    if m == 2: return -1
    return 0

def compute_hexagonal_circle_problem(N_max):
    print(f"Computing R(N) up to N = {N_max:,} using DULA character...")
    
    # Fast sieve for cumulative character sum
    chi_sum = np.zeros(N_max + 1, dtype=float)
    for d in range(1, N_max + 1):
        chi = dula_character(d)
        if chi != 0:
            chi_sum[d::d] += chi
    
    # R(N) = 1 + 6 * cumulative sum of chi_sum
    R = 1 + 6 * np.cumsum(chi_sum)
    
    N_vals = np.arange(N_max + 1)
    Area = (2 * np.pi / np.sqrt(3)) * N_vals
    Error = R - Area
    
    return N_vals[1:], Error[1:]

# Run the experiment
N_max = 1_000_000
N_vals, Error = compute_hexagonal_circle_problem(N_max)

# Normalize
Normalized_Error = Error / (N_vals ** 0.25)

# FFT of the normalized error (to look for zero signatures)
fft_result = fft(Normalized_Error)
frequencies = fftfreq(len(Normalized_Error), d=1.0)
power_spectrum = np.abs(fft_result)**2

# Plotting
fig, axes = plt.subplots(2, 1, figsize=(14, 10), dpi=150)

# Top: Normalized Error Term
axes[0].plot(N_vals, Normalized_Error, color='teal', linewidth=0.4, alpha=0.85)
axes[0].axhline(0, color='black', linestyle='--', linewidth=1)
axes[0].set_xlim(0, 100_000)
axes[0].set_title(r'Normalized Error Term $E(N)/N^{1/4}$ — Eisenstein Lattice ($A_2$)', fontsize=13, fontweight='bold')
axes[0].set_xlabel(r'Squared Radius $N$')
axes[0].set_ylabel(r'Normalized Fluctuation')
axes[0].grid(alpha=0.3)

# Bottom: Power Spectrum (FFT)
axes[1].plot(frequencies[:len(frequencies)//2], power_spectrum[:len(frequencies)//2], 
             color='darkred', linewidth=0.8)
axes[1].set_xlim(0, 0.01)  # Focus on low frequencies where zeros should appear
axes[1].set_title(r'Power Spectrum of Normalized Error (Signatures of $L(s, \chi_{-3})$ Zeros)', fontsize=13, fontweight='bold')
axes[1].set_xlabel('Frequency')
axes[1].set_ylabel('Power')
axes[1].grid(alpha=0.3)

plt.tight_layout()
plt.show()
