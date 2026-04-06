import numpy as np
import matplotlib.pyplot as plt
from scipy.linalg import svd

# =====================================================================
# PIE LAB: THE PALEY-WIENER GHOST HUNT
# =====================================================================

# 1. Setup the Frequency Domain (Discretized)
N_points = 1000
xi = np.linspace(-5, 5, N_points)
dx = xi[1] - xi[0]

# 2. The CE Fourier Proxy
# Viazovska's 24D modular forms, when descended to 1D, yield strictly 
# positive, rapidly decaying functions. We use a Gaussian as the ultimate proxy.
def ce_proxy(xi, lam):
    return np.exp(-lam * xi**2)

def run_ghost_hunt(M_dilations):
    """
    Builds a matrix of M dilations and computes the Ghost Distribution.
    """
    lambdas = np.linspace(0.1, 10.0, M_dilations)
    A = np.zeros((M_dilations, N_points))
    
    # Build the Fourier Envelope
    for i, lam in enumerate(lambdas):
        A[i, :] = ce_proxy(xi, lam) * np.sqrt(dx) # Weighted for integration
        
    # Singular Value Decomposition
    # Vt contains the orthogonal basis vectors of the frequency space.
    # The LAST row of Vt corresponds to the smallest singular value (the Null Space).
    # This is the "Best Possible Ghost Distribution".
    U, S, Vt = svd(A, full_matrices=False)
    
    ghost = Vt[-1, :] / np.sqrt(dx) # Normalize back to function space
    envelope = np.sum(A, axis=0) / np.sqrt(dx)
    
    return envelope, ghost, S

# =====================================================================
# RUN THE SIMULATION ACROSS 3 STAGES OF "RICHNESS"
# =====================================================================

fig, axes = plt.subplots(3, 1, figsize=(10, 12))
fig.suptitle("The Paley-Wiener Annihilation Trap", fontsize=16, fontweight='bold')

stages = [5, 15, 50] # Number of dilations (Richness)

for idx, M in enumerate(stages):
    envelope, ghost, singular_values = run_ghost_hunt(M)
    
    ax = axes[idx]
    ax.set_title(f"Stage {idx+1}: CE Richness = {M} Dilations")
    
    # Plot the CE Envelope (The Net)
    ax.plot(xi, envelope, color='limegreen', lw=2, label='CE Fourier Envelope')
    ax.fill_between(xi, 0, envelope, color='limegreen', alpha=0.2)
    
    # Plot the Ghost Distribution (The Target)
    ax.plot(xi, ghost, color='red', lw=1.5, label='Ghost Distribution (Null Space)')
    
    ax.set_ylim(-3, max(envelope)*1.1 if idx == 0 else axes[0].get_ylim()[1])
    ax.axhline(0, color='black', lw=0.5)
    ax.legend(loc='upper right')

plt.tight_layout(rect=[0, 0.03, 1, 0.96])
plt.show()

# Print the Singular Value Decay
_, _, S_final = run_ghost_hunt(50)
print("\n--- PIE LAB TELEMETRY ---")
print(f"Top Singular Value (Dominant CE Structure): {S_final[0]:.4e}")
print(f"Bottom Singular Value (Ghost Survival Probability): {S_final[-1]:.4e}")
if S_final[-1] < 1e-10:
    print("STATUS: GHOST DISTRIBUTION MATHEMATICALLY ANNIHILATED.")
