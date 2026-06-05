"""
=========================================================================
  DULA PRIME INERTIA ENGINE: THE DIRICHLET VOIDS (10,000 PRIMES)
=========================================================================
  Plots 10,000 primes onto the complex polar orbits of K_12 and 
  Complex Leech, revealing the absolute 1/3 physical density and 
  the geometric 'Dark Matter' voids.
"""

import numpy as np
import matplotlib.pyplot as plt

def generate_primes(n_primes):
    print(f"[*] Sifting {n_primes} primes for polar extraction...")
    primes = []
    limit = 110000 
    sieve = [True] * limit
    for p in range(2, limit):
        if sieve[p]:
            if p > 3: # Drop 2 and 3 to reveal the pure asymptotic geometry
                primes.append(p)
            if len(primes) >= n_primes:
                break
            for i in range(p * p, limit, p):
                sieve[i] = False
    return np.array(primes)

def plot_prime_orbits(primes):
    print("[*] Forging Prime Phase Orbits...")
    
    # Radius = ln(p) represents the physical expansion through time
    r = np.log(primes)
    
    # Phase calculations (Quantized to the geometric spokes)
    # K_12 (Rank 6): 12 spokes. Leech (Rank 12): 24 spokes.
    theta_k12 = (primes % 12) * (np.pi / 6)
    theta_leech = (primes % 24) * (np.pi / 12)
    
    plt.style.use('dark_background')
    fig, (ax1, ax2) = plt.subplots(1, 2, subplot_kw={'projection': 'polar'}, figsize=(16, 7), facecolor='#090a0f')
    fig.patch.set_facecolor('#090a0f')

    def style_polar_galaxy(ax, theta, radius, title, spokes, color_map):
        ax.set_facecolor('#090a0f')
        
        # Scatter the 10,000 primes
        ax.scatter(theta, radius, c=radius, cmap=color_map, s=8, alpha=0.6, zorder=3)
        
        # Format the grid to explicitly show ALL geometric spokes
        ax.set_xticks(np.linspace(0, 2*np.pi, spokes, endpoint=False))
        ax.set_xticklabels([f"{int(np.degrees(t))}°" for t in np.linspace(0, 2*np.pi, spokes, endpoint=False)], 
                           color='#58a6ff', fontsize=8, fontweight='bold')
        ax.tick_params(axis='y', colors='#30363d') # Hide radial distance numbers for clean aesthetic
        ax.set_yticklabels([])
        
        # Highlight the voids (Red gridlines) and populated spokes (Blue gridlines)
        ax.grid(True, color='#21262d', linestyle='-', linewidth=0.5, zorder=1)
        ax.spines['polar'].set_color('#30363d')
        ax.spines['polar'].set_linewidth(1.5)
        
        ax.set_title(title, color='#c9d1d9', pad=30, fontsize=14, fontweight='bold')

    style_polar_galaxy(ax1, theta_k12, r, "RANK 6: K_12 (4 Active / 8 Voids)", 12, 'magma')
    style_polar_galaxy(ax2, theta_leech, r, "RANK 12: COMPLEX LEECH (8 Active / 16 Voids)", 24, 'viridis')

    plt.suptitle("THE DIRICHLET VOIDS: 10,000 PRIMES IN EISENSTEIN PHASE SPACE", color='#ffffff', fontsize=18, fontweight='bold', y=1.05)
    plt.tight_layout()
    plt.savefig("dula_dirichlet_voids.png", dpi=400, bbox_inches='tight')
    print("[+] Generated: dula_dirichlet_voids.png")

if __name__ == "__main__":
    primes_10k = generate_primes(10000)
    plot_prime_orbits(primes_10k)
