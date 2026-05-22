import gc
import time
import sympy as sp
import matplotlib.pyplot as plt
import cupy as cp
import numpy as np

def get_dula_basis(N_elements):
    """Generate the prime power basis (Runs on CPU)."""
    basis = []
    n = 2
    while len(basis) < N_elements:
        if n % 6 in [1, 5]:
            factors = sp.factorint(n)
            if len(factors) == 1:
                p = list(factors.keys())[0]
                chi_6 = 1 if n % 6 == 1 else -1
                lambda_n = np.log(p)
                basis.append((n, chi_6, lambda_n))
        n += 1
    return basis

# ==========================================
# Compute Parameters
# ==========================================
N = 15000  
lambdas = [0.0, 0.05, 0.25, 1.0]

print(f"Generating DULA basis for N = {N}...")
basis = get_dula_basis(N)

# Push to GPU
m_vals = cp.array([b[0] for b in basis], dtype=cp.float64)
chi_vals = cp.array([b[1] for b in basis], dtype=cp.float64)
lambda_vals = cp.array([b[2] for b in basis], dtype=cp.float64)

# ==========================================
# Vectorized Operator Construction (GPU)
# ==========================================
print("Constructing Tensors on GPU...")

# 1. Rigid DULA Matrix (Rank-1 Vacuum)
chi_matrix = cp.outer(chi_vals, chi_vals)
sqrt_m_matrix = cp.sqrt(cp.outer(m_vals, m_vals))
A_DULA = chi_matrix / sqrt_m_matrix
cp.fill_diagonal(A_DULA, chi_vals * lambda_vals)

# 2. FULL-RANK Composite Perturbation (Undamped)
# The physical collision of primes generating the 1 and 5 mod 6 composites
m_col = m_vals[:, cp.newaxis]
m_row = m_vals[cp.newaxis, :]
C_ij = m_col * m_row  # The Composite Matrix

# The raw, irreducible chaotic scattering field: cos(sqrt(C_ij))
# (Denominator removed to prevent amplitude crushing)
V_comp = cp.cos(cp.sqrt(C_ij))

# Maintain strict DULA parity across the composite interactions
V_comp = V_comp * chi_matrix

# ==========================================
# Spectral Analysis (VRAM Optimized)
# ==========================================
fig, axes = plt.subplots(2, 2, figsize=(16, 12))
fig.suptitle(f"High-Resolution Spectral Flow (N={N})\nUndamped Full-Rank Composite Friction", fontsize=18, fontweight='bold')

for idx, lam in enumerate(lambdas):
    print(f"\nComputing λ = {lam}...")
    
    if lam == 0.0:
        A_Final = A_DULA.copy()
    else:
        A_Final = A_DULA + lam * V_comp
    
    # Diagonalize using the VRAM-saving eigvalsh
    print("  -> Diagonalizing Full-Rank Operator...")
    eigenvalues = cp.linalg.eigvalsh(A_Final)
    eig_cpu = cp.asnumpy(eigenvalues)
    
    # Aggressive VRAM Cleanup
    del A_Final
    del eigenvalues
    cp.get_default_memory_pool().free_all_blocks()
    gc.collect()
    
    # Plotting
    ax = axes[idx // 2, idx % 2]
    ax.hist(eig_cpu, bins=250, color='#993c1d', alpha=0.8, edgecolor='black', linewidth=0.2)
    ax.set_title(f"Coupling λ = {lam}", fontsize=14)
    ax.set_xlabel("Eigenvalue", fontsize=11)
    ax.set_ylabel("Density", fontsize=11)
    
    # Zoom in on the active thermalized spectrum
    ax.set_xlim([np.percentile(eig_cpu, 1), np.percentile(eig_cpu, 99)])
    ax.grid(True, linestyle='--', alpha=0.6)

plt.tight_layout()
plt.subplots_adjust(top=0.88)
plt.show()
