import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit

# =====================================================================
# 1. LOAD YOUR K=2500 DEEP SCAN ARRAYS HERE
# Replace these placeholders with your actual exported NumPy arrays.
# Make sure k_vals and c_vals are aligned and only contain non-zero terms.
# =====================================================================
# Example load (if you saved them to a file):
# data = np.loadtxt('phase1_k2500.txt')
# k_vals = data[:, 0]
# c_vals = data[:, 1]

# --- PLACEHOLDER: OVERWRITE THIS WITH YOUR DATA ---
# Generating dummy data that mimics K=2500 exponential growth for testing
k_vals = np.arange(1, 2501, 2) # Odd k for Phase 1
c_vals = np.exp(np.pi * np.sqrt(2 * 24 / 3) * np.sqrt(k_vals) / 2) # Simulating c=24 growth
# --------------------------------------------------

# =====================================================================
# 2. RIGOROUS SADDLE-POINT REGRESSION (Hardy-Ramanujan limit)
# =====================================================================
# We fit: ln(c(k)) = ln(A) - alpha * ln(k) + C * sqrt(k)
def asymptotic_log_model(k, ln_A, alpha, C):
    return ln_A - alpha * np.log(k) + C * np.sqrt(k)

# CRITICAL: We must isolate the true asymptote.
# We slice off the "Small k" regime where polynomial noise dominates.
# For K_max = 2500, we only fit data where k > 200.
asymptotic_threshold = 200
valid_idx = k_vals > asymptotic_threshold

if np.sum(valid_idx) < 10:
    print("Error: Not enough deep data points to fit the asymptote. Check your arrays.")
    exit()

k_fit = k_vals[valid_idx]
log_c_fit = np.log(c_vals[valid_idx].astype(np.float64))

# Bounded regression to ensure physical CFT parameters
# bounds = ([min_ln_A, min_alpha, min_C], [max_ln_A, max_alpha, max_C])
popt, pcov = curve_fit(
    asymptotic_log_model, 
    k_fit, 
    log_c_fit, 
    bounds=([-np.inf, -10.0, 0.0], [np.inf, 10.0, np.inf]),
    maxfev=50000
)

ln_A_opt, alpha_opt, C_opt = popt

# =====================================================================
# 3. CENTRAL CHARGE EXTRACTION
# By Cardy's Formula: C = pi * sqrt(2c / 3)
# Therefore: c = 1.5 * (C / pi)^2
# =====================================================================
central_charge_c = 1.5 * (C_opt / np.pi)**2

print("=========================================================")
print("  PRIME INERTIA: RIGOROUS ASYMPTOTIC EXTRACTION")
print("=========================================================")
print(f"Data Points Analyzed:      {len(k_vals)}")
print(f"Asymptotic Fit Range:      k > {asymptotic_threshold}")
print("---------------------------------------------------------")
print(f"Extracted Tension (C):     {C_opt:.6f}")
print(f"Extracted Mod Weight (α):  {alpha_opt:.6f}")
print(f"Effective Central Charge:  {central_charge_c:.6f}  <-- THE TARGET")
print("=========================================================\n")

# =====================================================================
# 4. VISUAL PROOF OF CONVERGENCE
# =====================================================================
plt.style.use('dark_background')
fig, ax = plt.subplots(figsize=(10, 6))

# Plot the raw empirical data
ax.scatter(k_vals, c_vals, color='#ff00aa', s=10, label='Empirical $c_\phi(k)$')

# Plot the Hardy-Ramanujan Fit
k_smooth = np.linspace(np.min(k_vals), np.max(k_vals), 500)
c_smooth = np.exp(asymptotic_log_model(k_smooth, ln_A_opt, alpha_opt, C_opt))
ax.plot(k_smooth, c_smooth, color='#00ffcc', linestyle='--', linewidth=2, 
        label=rf'Fit: $c={central_charge_c:.2f}, \alpha={alpha_opt:.2f}$')

ax.set_title('Deep Scan Asymptotic Convergence ($K_{max} = 2500$)')
ax.set_xlabel('Collatz Orbit Length ($k$)')
ax.set_ylabel('Coefficient Magnitude (Log Scale)')
ax.set_yscale('log')
ax.axvline(asymptotic_threshold, color='white', linestyle=':', alpha=0.5, label='Asymptotic Threshold')
ax.legend()
ax.grid(True, alpha=0.2)

plt.tight_layout()
plt.show()
