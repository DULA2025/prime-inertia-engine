import numpy as np
from numba import njit, prange
import time

@njit(parallel=True)
def compute_collatz_statistics(max_n, max_k):
    """
    Computes the distribution of Collatz orbit lengths and net step displacements.
    
    Definitions for an integer n:
    - L(n): The total orbit length (number of steps to reach 1).
    - S(n): The net step displacement, defined as (odd steps) - (even steps).
    - phi(n): The congruence class of the displacement, S(n) mod 6.
    
    Returns:
    - phase_counts: A 6 x (max_k + 1) matrix where phase_counts[phi, k] represents
      the number of integers n <= max_n with L(n) = k and phi(n) = phi.
    - equilibrium_counts: A 1D array where equilibrium_counts[k] represents 
      the number of integers with L(n) = k and exactly S(n) = 0.
    """
    phase_counts = np.zeros((6, max_k + 1), dtype=np.uint64)
    equilibrium_counts = np.zeros(max_k + 1, dtype=np.uint64)
    
    for n in prange(1, max_n + 1):
        m = n
        steps = 0
        net_displacement = 0
        
        # Compute the Collatz trajectory to 1
        while m > 1:
            if m % 2 == 0:
                m = m // 2
                net_displacement -= 1
            else:
                m = 3 * m + 1
                net_displacement += 1
            steps += 1
            
        # Record statistics if within the specified depth limit
        if steps <= max_k:
            if net_displacement == 0:
                equilibrium_counts[steps] += 1
                
            phase = net_displacement % 6
            phase_counts[phase, steps] += 1
            
    return phase_counts, equilibrium_counts

if __name__ == "__main__":
    N_MAX = 100_000_000  # Size of the integer ensemble
    K_MAX = 100          # Maximum orbit length to track
    
    print(f"Computing Collatz displacement classes for N = {N_MAX}...")
    start_time = time.time()
    
    phase_counts, equilibrium_counts = compute_collatz_statistics(N_MAX, K_MAX)
    
    print(f"Computation complete in {time.time() - start_time:.2f} seconds.\n")
    
    # 1. Output the 6 Congruence Classes (phi = 0 to 5)
    for phi in range(6):
        seq = phase_counts[phi, 1:K_MAX+1]
        non_zero_indices = np.nonzero(seq)[0]
        
        print(f"--- Congruence Class phi ≡ {phi} (mod 6) ---")
        if len(non_zero_indices) > 0:
            last_idx = non_zero_indices[-1]
            seq_trimmed = seq[:last_idx+1]
            poly_terms = [f"{c}q^{k+1}" for k, c in enumerate(seq_trimmed) if c > 0]
            print(" + ".join(poly_terms[:15]) + (" + ..." if len(poly_terms) > 15 else ""))
        else:
            print("0")
        print()
        
    # 2. Output the Exact Equilibrium States (S(n) = 0)
    print("--- Equilibrium States (S(n) = 0) ---")
    eq_seq = equilibrium_counts[1:K_MAX+1]
    eq_non_zero = np.nonzero(eq_seq)[0]
    if len(eq_non_zero) > 0:
        last_idx = eq_non_zero[-1]
        eq_trimmed = eq_seq[:last_idx+1]
        eq_terms = [f"{c}q^{k+1}" for k, c in enumerate(eq_trimmed) if c > 0]
        print(" + ".join(eq_terms[:15]) + (" + ..." if len(eq_terms) > 15 else ""))
    else:
        print("No equilibrium states found in this depth range.")
    print()

    # 3. Mathematical Verification of the Total Inverse Tree Branching
    print("--- Total Branching per Depth (k) ---")
    total_branching = np.sum(phase_counts, axis=0)
    print(list(total_branching[1:15]))
