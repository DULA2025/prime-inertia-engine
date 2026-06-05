"""
=========================================================================
  DULA PRIME INERTIA ENGINE: MATRIX DIAGONALIZATION FORGE (V2)
=========================================================================
  This script executes exact symbolic, numerical, and GPU-accelerated 
  diagonalization, now featuring exact SymPy types and Spectral Plotting.
"""

import numpy as np
import sympy as sp
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

try:
    import cupy as cp
    HAS_GPU = True
except ImportError:
    HAS_GPU = False

# =====================================================================
# 1. EXACT SYMBOLIC DIAGONALIZATION (SymPy)
# =====================================================================
def exact_diagonalize(sym_matrix):
    print("\n[*] Executing Exact Symbolic Diagonalization...")
    A = sp.Matrix(sym_matrix)
    
    # P is the matrix of eigenvectors. D is the diagonal eigenvalue matrix.
    P, D = A.diagonalize()
    
    print("[+] Exact Diagonal Matrix (D):")
    sp.pprint(D)
    print("\n[+] Exact Eigenvector Basis (P):")
    sp.pprint(P)
    
    # Symbolic simplification to guarantee absolute equality
    # sp.expand ensures any algebraic fractions/roots are properly canceled
    assert sp.simplify(A - P * D * P.inv()).is_zero_matrix, "Diagonalization failed verification."
    print("[+] Absolute symbolic verification passed. 0 floating-point error.")
    
    return P, D

# =====================================================================
# 2. NUMERICAL DIAGONALIZATION & PLOTTING (NumPy / Matplotlib)
# =====================================================================
def numerical_diagonalize(matrix_data):
    print("\n[*] Executing Standard Numerical Diagonalization (eigh)...")
    A = np.array(matrix_data, dtype=np.complex128)
    
    # eigh guarantees real eigenvalues for Hermitian matrices
    evals, evecs = np.linalg.eigh(A)
    
    print("[+] Numerical Eigenvalues (D):", np.round(evals, 4))
    return evals, evecs

def plot_spectral_geometry(evals, evecs):
    """
    Plots a dual-panel visualization of the Spectral Decomposition:
    1. A Bar chart of the Eigenvalues (the scaling factors).
    2. A 3D Quiver plot of the Eigenvectors' real projections.
    """
    print("\n[*] Rendering Spectral Geometry Plot...")
    
    # Configure Dark Mode Aesthetics
    plt.style.use('dark_background')
    fig = plt.figure(figsize=(14, 6), facecolor='#0d1117')
    
    # Panel 1: The Eigenvalues (Pure Scaling)
    ax1 = fig.add_subplot(121, facecolor='#0d1117')
    colors = ['#ff7b72', '#58a6ff', '#3fb950']
    
    bars = ax1.bar(['λ₁', 'λ₂', 'λ₃'], evals, color=colors, edgecolor='#c9d1d9', alpha=0.85)
    ax1.set_title("The Eigenvalues (Spectral Scaling)", color='#c9d1d9', pad=15)
    ax1.set_ylabel("Magnitude", color='#c9d1d9')
    ax1.grid(True, color='#21262d', linestyle='--', alpha=0.5)
    
    # Add exact values to the top of the bars
    for bar in bars:
        yval = bar.get_height()
        ax1.text(bar.get_x() + bar.get_width()/2, yval + 0.1, round(yval, 4), 
                 ha='center', va='bottom', color='white', fontweight='bold')

    # Panel 2: The Eigenvectors (Basis Real Projection)
    ax2 = fig.add_subplot(122, projection='3d', facecolor='#0d1117')
    
    # Format the 3D axes
    ax2.xaxis.set_pane_color((0.0, 0.0, 0.0, 0.0))
    ax2.yaxis.set_pane_color((0.0, 0.0, 0.0, 0.0))
    ax2.zaxis.set_pane_color((0.0, 0.0, 0.0, 0.0))
    
    # Plot the origin standard basis faintly
    ax2.plot([-1, 1], [0, 0], [0, 0], color='#30363d', linestyle=':')
    ax2.plot([0, 0], [-1, 1], [0, 0], color='#30363d', linestyle=':')
    ax2.plot([0, 0], [0, 0], [-1, 1], color='#30363d', linestyle=':')

    # Extract the real parts of the eigenvectors to plot in 3D Euclidean space
    v1 = np.real(evecs[:, 0])
    v2 = np.real(evecs[:, 1])
    v3 = np.real(evecs[:, 2])
    
    # Draw the Eigenvector arrows
    ax2.quiver(0, 0, 0, v1[0], v1[1], v1[2], color=colors[0], label='v₁ (Real Axis)', linewidth=2.5, arrow_length_ratio=0.1)
    ax2.quiver(0, 0, 0, v2[0], v2[1], v2[2], color=colors[1], label='v₂ (Real Axis)', linewidth=2.5, arrow_length_ratio=0.1)
    ax2.quiver(0, 0, 0, v3[0], v3[1], v3[2], color=colors[2], label='v₃ (Real Axis)', linewidth=2.5, arrow_length_ratio=0.1)
    
    ax2.set_xlim([-1, 1]); ax2.set_ylim([-1, 1]); ax2.set_zlim([-1, 1])
    ax2.set_title("Eigenvector Basis (Real Z[ω] Projection)", color='#c9d1d9', pad=15)
    ax2.legend(facecolor='#161b22', edgecolor='#30363d', labelcolor='white')
    
    plt.tight_layout()
    plt.savefig("dula_spectral_geometry.png", dpi=300)
    print("[+] Plot saved successfully as 'dula_spectral_geometry.png'")
    plt.show()

# =====================================================================
# 3. GPU-ACCELERATED DIAGONALIZATION (CuPy)
# =====================================================================
def gpu_diagonalize(matrix_data):
    if not HAS_GPU:
        return
    print("\n[*] Executing GPU-Accelerated Diagonalization (CUDA)...")
    A_gpu = cp.array(matrix_data, dtype=cp.complex128)
    evals_gpu, evecs_gpu = cp.linalg.eigh(A_gpu)
    print("[+] GPU Eigenvalues:", cp.round(evals_gpu, 4))

# =====================================================================
# MAIN EXECUTION
# =====================================================================
if __name__ == "__main__":
    # 1. The Exact SymPy Matrix (Notice the pure symbolic sp.I)
    test_matrix_exact = [
        [4, -1 + sp.I, 1],
        [-1 - sp.I, 4, -sp.I],
        [1, sp.I, 4]
    ]
    
    # 2. The Numerical Python Matrix (Using 1j floats for NumPy/Matplotlib)
    test_matrix_numerical = [
        [ 4,  -1+1j,  1 ],
        [-1-1j,  4,  -1j],
        [ 1,   1j,    4 ]
    ]
    
    # Execute Pure Algebra
    exact_diagonalize(test_matrix_exact)
    
    # Execute Numerical and render the Plot
    evals, evecs = numerical_diagonalize(test_matrix_numerical)
    plot_spectral_geometry(evals, evecs)
    
    # Execute CUDA if available
    gpu_diagonalize(test_matrix_numerical)
