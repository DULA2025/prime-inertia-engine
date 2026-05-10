import numpy as np
from numba import njit, prange
import time

@njit(parallel=True)
def compute_q_series(max_n, max_k):
    # 7 geometric states: 
    # Indices 0-5: The outer hexagonal phases (n, Σ⁻, Ξ⁻, Ξ⁰, Σ⁺, p)
    # Index 6: The invariant Cartan core (Drop Condition: net_sum == 0)
    coeffs = np.zeros((7, max_k + 1), dtype=np.uint64)
    
    for n in prange(1, max_n + 1):
        m = n
        steps = 0
        net_sum = 0
        
        # Trace the trajectory
        while m > 1:
            if m % 2 == 0:
                m = m // 2
                net_sum -= 1
            else:
                m = 3 * m + 1
                net_sum += 1
            steps += 1
            
        # If the orbit length fits in our series expansion window
        if steps <= max_k:
            if net_sum == 0:
                coeffs[6, steps] += 1
            else:
                # Numba correctly evaluates negative modulo (e.g., -1 % 6 == 5)
                phase = net_sum % 6
                coeffs[phase, steps] += 1
                
    return coeffs

if __name__ == "__main__":
    N_MAX = 100_000_000  # 100 million trajectories
    K_MAX = 100          # Extract coefficients up to q^100
    
    print(f"Igniting Prime Inertia Engine for N = {N_MAX}...")
    start_time = time.time()
    
    q_coeffs = compute_q_series(N_MAX, K_MAX)
    
    print(f"Scan complete in {time.time() - start_time:.2f} seconds.\n")
    
    labels = [
        "Phase 0 (Neutron) ",
        "Phase 1 (Sigma-)  ",
        "Phase 2 (Xi-)     ",
        "Phase 3 (Xi0)     ",
        "Phase 4 (Sigma+)  ",
        "Phase 5 (Proton)  ",
        "Cartan Core (Drop)"
    ]
    
    for i in range(7):
        # Extract the sequence of coefficients from k=1 to K_MAX
        seq = q_coeffs[i, 1:K_MAX+1]
        
        # Trim trailing zeros for cleaner output
        non_zero_indices = np.nonzero(seq)[0]
        if len(non_zero_indices) > 0:
            last_idx = non_zero_indices[-1]
            seq_trimmed = seq[:last_idx+1]
        else:
            seq_trimmed = []
            
        print(f"--- {labels[i]} ---")
        if i == 6 and np.sum(seq) == 0:
            print("No drops found in this range.")
        else:
            # Print the polynomial format: C_1*q^1 + C_2*q^2 + ...
            poly_terms = [f"{c}q^{k+1}" for k, c in enumerate(seq_trimmed) if c > 0]
            if poly_terms:
                print(" + ".join(poly_terms[:15]) + (" + ..." if len(poly_terms) > 15 else ""))
            else:
                print("0")
        print()
