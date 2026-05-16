
"""
dula_experiments.py
===================

Five experiments aimed at the DULA program's analytic-number-theory core:
  (a) High-precision tables of L(s, chi_3) special values and zeros
  (b) Explicit-formula numerics with the convention nailed down
  (c) Weil positivity functional on chi-twisted test functions
  (d) Selberg sieve singular-series for chi-mod-6 lane structure
  (e) Cohn-Elkies bound numerics

All for chi = unique non-trivial real character mod 3 (Legendre symbol
mod 3), odd character (chi(-1) = -1).

Output is organized so individual sections can be ported to Lean as
high-precision reference data.
"""

import sympy
import numpy as np
from mpmath import (mp, mpf, mpc, pi, gamma, dirichlet, sqrt, log, exp, 
                    j as ij, nstr, findroot, digamma, quad, sin, cos, inf,
                    fdot, polylog, zeta)

mp.dps = 35

# =============================================================================
#  Core objects
# =============================================================================

def chi(n):
    """Non-trivial real character mod 3 (Legendre symbol mod 3).
       Treated as lifted to mod 6 by chi(2k) = 0 when needed."""
    n = int(n)
    if n % 3 == 0: return 0
    return 1 if n % 3 == 1 else -1

def L_chi(s):
    """L(s, chi_3) = sum_n chi(n)/n^s, with analytic continuation."""
    return dirichlet(s, [0, 1, -1])

def Lambda_chi(s):
    """Completed L-function: Lambda(s, chi) = (3/pi)^{(s+1)/2} Gamma((s+1)/2) L(s, chi).
       Satisfies Lambda(s) = Lambda(1-s) since chi is real with W(chi) = +1."""
    q = mpf(3)
    return (q/pi)**((s+1)/2) * gamma((s+1)/2) * L_chi(s)

def Z_chi(t):
    """Real-valued function on critical line; zeros = nontrivial zeros."""
    return Lambda_chi(mpf(1)/2 + ij*t).real


def banner(title):
    bar = "=" * 78
    print(f"\n{bar}\n  {title}\n{bar}")


# =============================================================================
#  (a) High-precision reference table for L(s, chi_3)
# =============================================================================

def experiment_a():
    banner("Experiment (a):  High-precision tables for Lean reference")

    print("\n  Special values:")
    table_special = [
        ("L(-3, chi)",    L_chi(-3),  "= 0 (trivial zero, chi odd)"),
        ("L(-1, chi)",    L_chi(-1),  "= 0 (trivial zero, chi odd)"),
        ("L(0, chi)",     L_chi(0),   "= 1/3"),
        ("L'(0, chi)",    None,       "= log Γ(1/3) − log Γ(2/3) − (1/3) log 3"),
        ("L(1, chi)",     L_chi(1),   "= π / (3√3)"),
        ("L(2, chi)",     L_chi(2),   "(Catalan-like, no closed form)"),
        ("L(3, chi)",     L_chi(3),   "(no closed form)"),
        ("L(1/2, chi)",   L_chi(mpf(1)/2), "(central value)"),
    ]
    from mpmath import diff as mpdiff
    Lprime_0 = mpdiff(L_chi, 0)
    table_special[3] = ("L'(0, chi)", Lprime_0,
                        "= log Γ(1/3) − log Γ(2/3) − (1/3) log 3")
    print(f"  {'point':<14} {'value':>40}   {'identity':<48}")
    for name, val, note in table_special:
        if val is not None:
            print(f"  {name:<14} {nstr(val, 28):>40}   {note}")

    # Verify closed forms numerically
    print("\n  Closed-form verifications:")
    print(f"    π/(3√3)                            = {nstr(pi/(3*sqrt(3)), 30)}")
    print(f"    log Γ(1/3) − log Γ(2/3) − (log 3)/3 = {nstr(log(gamma(mpf(1)/3)) - log(gamma(mpf(2)/3)) - log(3)/3, 30)}")

    # Functional equation at random complex points (cross-check)
    print("\n  Functional equation Λ(s, χ) = Λ(1−s, χ):  max error over 8 points")
    test_pts = [mpc(0.3, 0), mpc(0.7, 0), mpc(0.5, 1.0), mpc(0.5, 3.5),
                mpc(0.3, 5.0), mpc(0.2, 10.0), mpc(-1.5, 7.0), mpc(2.5, -3.0)]
    errs = [abs(Lambda_chi(s) - Lambda_chi(1 - s)) for s in test_pts]
    print(f"    max |Λ(s) − Λ(1−s)|  = {nstr(max(errs), 6)}")

    return table_special


# =============================================================================
#  Helper: locate nontrivial zeros on critical line up to height T
# =============================================================================

def find_zeros(T_max, step=mpf("0.05")):
    """Sign-change + refinement to locate zeros of Z_chi(t) for t in (0, T_max)."""
    t_grid = [mpf(i) * step for i in range(int(1/float(step)), int(T_max/float(step)) + 1)]
    vals = [Z_chi(t) for t in t_grid]
    zeros = []
    for i in range(len(t_grid) - 1):
        if vals[i] * vals[i+1] < 0:
            try:
                z = findroot(Z_chi, (t_grid[i] + t_grid[i+1])/2, tol=mpf("1e-25"))
                if not any(abs(z - zz) < mpf("0.001") for zz in zeros):
                    zeros.append(z)
            except Exception:
                pass
    return sorted(zeros)


# =============================================================================
#  (b) Explicit formula numerics with correct convention
# =============================================================================

def experiment_b(zeros_list=None):
    """Verify the explicit formula for L(s, chi_3) with a compactly-supported
    test function so we can avoid convention ambiguities at infinity.

    Form used (cf. Iwaniec-Kowalski Thm 5.12, with chi odd, conductor q=3):

      sum_{nontrivial rho} h(gamma_rho)
        =  (1/(2π)) int_{-∞}^{∞} h(r) · K(r) dr
           − 2 sum_{n>=2} Λ(n) chi(n) g(log n) / sqrt(n)

    where rho = 1/2 + i*gamma_rho on the critical line (assuming RH for chi_3,
    which is empirically verified for the zeros we computed); h is the
    Fourier transform of g; Λ is the von Mangoldt function;
    K(r) = Re[ ψ((1/4) + (1/2)·(1 + i r)/1) ] − log(π/3)   [archimedean kernel]
    (the (1+...) shift uses δ=1 for chi odd).
    """
    banner("Experiment (b):  Explicit formula verification")

    # Test function: g(x) = (1 − |x|/T)_+    (triangle), with h(r) = (sin(rT/2)/(rT/2))^2 · T/2
    # Reasonable T to expose first few zeros but not blow up primes
    T = mpf(3)
    def g(x):
        ax = abs(x)
        if ax >= T: return mpf(0)
        return 1 - ax/T
    def h(r):
        if r == 0: return T/2
        return (sin(r*T/2) / (r*T/2))**2 * (T/2)

    # Zero side: sum over zeros (both ±γ for real character — h is even, so 2 * Σ over γ > 0)
    if zeros_list is None:
        zeros_list = find_zeros(mpf(200))   # all zeros up to height 200
    print(f"  Using {len(zeros_list)} zeros up to height {float(zeros_list[-1]):.1f}")

    zero_side = 2 * sum(h(g_n) for g_n in zeros_list)
    print(f"  Zero side (Σ_ρ h(γ_ρ)):         {nstr(zero_side, 18)}")

    # Archimedean side: 1/(2π) ∫ h(r) [ψ((1/4 + 1/2) + ir/2)_realpart  − log(π/3)] dr · 2
    # (factor 2 from symmetry r ↔ −r)
    # For chi odd, gamma factor uses Γ((s+1)/2), so digamma argument is (s+1)/2 = (1 + iγ)/2 + 1/2 = (2 + iγ)/2
    def arch_integrand(r):
        return h(r) * (digamma((mpc(2, r))/2).real - (log(pi) - log(3)))
    arch_side = 2 * quad(arch_integrand, [0, 50]) / (2 * pi)
    print(f"  Archimedean side:               {nstr(arch_side, 18)}")

    # Prime side: 2 Σ_{n>=2} Λ(n) χ(n) g(log n) / √n  (Λ is von Mangoldt)
    prime_side = mpf(0)
    log_cutoff = float(T) * 1.5
    n_cutoff = int(exp(mpf(log_cutoff))) + 10
    primes = list(sympy.primerange(2, n_cutoff + 1))
    for p in primes:
        lp = log(mpf(p))
        for k in range(1, int(float(log_cutoff)/float(lp)) + 2):
            n = p**k
            if log(mpf(n)) >= T: break
            cp_k = chi(p)**k
            if cp_k == 0: continue
            prime_side += cp_k * lp * g(log(mpf(n))) / sqrt(mpf(n))
    prime_side = 2 * prime_side
    print(f"  Prime side (2 · Σ Λ(n)χ(n)g(log n)/√n):  {nstr(prime_side, 18)}")

    print()
    print(f"  Zero - (Arch - Prime):  {nstr(zero_side - (arch_side - prime_side), 8)}")
    print( "  (Should be 0 by the explicit formula. Nonzero residual = truncation in zeros.)")

    return zero_side, arch_side, prime_side


# =============================================================================
#  (c) Weil positivity functional
# =============================================================================

def experiment_c(zeros_list):
    """Weil's 1952 positivity criterion (informal):

      RH for L(., chi)  ⟺  for every "nice" h, the quadratic functional
        Q(h) := sum_ρ h(γ_ρ)·h(γ_ρ_bar)
              = (1/2π) ∫ |h(r)|² K(r) dr  −  2 Σ_n Λ(n)χ(n) g_corr(n)/√n
      is non-negative.

    Numerically: pick a 1-parameter family of test functions and plot Q(α).
    For RH to hold, Q must stay ≥ 0 across the family.

    Family: g_α(x) = cos(α x) · (1 − |x|/T)_+   for α ∈ [0, 5], T = 3.
    """
    banner("Experiment (c):  Weil positivity functional for L(., χ)")

    T = mpf(3)
    def g_alpha(x, a):
        ax = abs(x)
        if ax >= T: return mpf(0)
        return cos(a*x) * (1 - ax/T)
    def h_alpha(r, a):
        # Fourier transform of g_alpha:  (1/2)[K(r-a) + K(r+a)] where K is triangle FT
        def K(rr):
            if rr == 0: return T/2
            return (sin(rr*T/2) / (rr*T/2))**2 * (T/2)
        return (K(r-a) + K(r+a)) / 2

    alphas = [mpf(k)/10 for k in range(0, 51)]
    Qs = []
    for a in alphas:
        # Zero side: |h_α(γ)|² summed over both signs of γ
        zero_part = 2 * sum(h_alpha(g_n, a)**2 for g_n in zeros_list)
        Qs.append(zero_part)
        # (For full Weil, we'd subtract arch & prime — but here we just check
        #  that the zero-side functional itself is nonneg for any α, which is
        #  automatic for real-valued h. The point is to display Q(α) shape.)

    min_Q = min(Qs)
    max_Q = max(Qs)
    print(f"  Family: g_α(x) = cos(αx)·(1−|x|/3)_+,  α ∈ [0, 5]")
    print(f"  Q(α) = Σ_ρ |ĝ_α(γ_ρ)|²  over {len(zeros_list)} zeros (positive by construction)")
    print(f"  min Q = {nstr(min_Q, 8)},  max Q = {nstr(max_Q, 8)}")
    print(f"  All Q(α) ≥ 0:  {all(q >= 0 for q in Qs)}")

    # Resonance structure: which α makes Q largest?
    Q_arr = [float(q) for q in Qs]
    a_arr = [float(a) for a in alphas]
    peaks = [(a_arr[i], Q_arr[i]) for i in range(1, len(Q_arr)-1)
             if Q_arr[i] > Q_arr[i-1] and Q_arr[i] > Q_arr[i+1]]
    print(f"\n  Local maxima of Q(α)  (resonances with γ_ρ ≈ α · T/2 = 1.5α):")
    for a_max, Q_max in peaks[:8]:
        gamma_est = 1.5 * a_max
        print(f"    α = {a_max:.2f}  →  resonance near γ ≈ {gamma_est:.2f}   Q = {Q_max:.3f}")
    print("  (Compare with low γ values: 8.04, 11.25, 15.70, 18.26, 20.46, ...)")

    return alphas, Qs


# =============================================================================
#  (d) Selberg sieve singular series for chi-mod-6 lane structure
# =============================================================================

def experiment_d():
    """Singular series constants for prime tuples respecting chi mod 6.

    Classical Hardy-Littlewood twin prime constant:
       C_2 = 2 ∏_{p>2} (1 − 1/(p−1)²)  ≈  0.6601618...

    Twin primes in the DULA lane structure split: a twin (p, p+2) with
    p > 3 has p ≡ 5 (mod 6) and p+2 ≡ 1 (mod 6).  So *all* twin primes
    are "cross-lane" pairs (5→1 mod 6) under chi.  Equivalently:
       chi(p) · chi(p+2) = -1  for every twin (p, p+2) with p > 3.

    This is a sign-determinacy.  Let's verify and compute the relevant
    chi-twisted analog of the singular series.
    """
    banner("Experiment (d):  Selberg/Hardy-Littlewood constants in DULA lanes")

    # Twin prime constant
    C2 = mpf(2)
    for p in sympy.primerange(3, 10000):
        C2 *= (1 - mpf(1)/(mpf(p)-1)**2)
    print(f"  Hardy-Littlewood twin prime constant C_2 ≈ {nstr(C2, 15)}")
    print(f"    (reference value: 0.6601618158...)")

    # Verify the chi-sign-determinacy for twin primes
    print("\n  Sign-determinacy check: chi(p)·chi(p+2) for twin primes (p, p+2), p > 3:")
    twins = []
    for p in sympy.primerange(5, 1000):
        if sympy.isprime(p+2):
            twins.append(p)
    print(f"    twin primes up to 1000: {len(twins)} pairs")
    sign_products = set(chi(p) * chi(p+2) for p in twins)
    print(f"    set of chi(p)·chi(p+2) values: {sign_products}")
    print(f"    (predicted: {{-1}})")

    # Chi-twisted Hardy-Littlewood constant for cross-lane twins
    # C_χ = 2 ∏_{p > 3} [1 − (something involving chi)]
    # More precisely: the singular series for representations
    #    π_{1,5}(x) = #{ p ≤ x : p ≡ 5 mod 6 and p+2 prime ≡ 1 mod 6 }
    # By Dirichlet density argument, all twin primes p > 3 fall into this class,
    # so the count is the same as the total twin prime count → density ~ C_2 · x/(log x)^2.

    # Twin counts in arithmetic progressions:
    twin_counts = {(5, 1): 0, (1, 5): 0, ('other', 0): 0}
    for p in twins:
        a, b = p % 6, (p+2) % 6
        if (a, b) == (5, 1):
            twin_counts[(5, 1)] += 1
        elif (a, b) == (1, 5):
            twin_counts[(1, 5)] += 1
        else:
            twin_counts[('other', 0)] += 1
    print(f"\n  Twin primes by lane structure (p, p+2) mod 6:")
    for k, v in twin_counts.items():
        print(f"    {k}: {v} pairs")

    # Triplet constant
    # Brun's constant for cousin primes (p, p+4): also p > 3 → p ≡ ±1 mod 6
    cousin_counts = {(5, 3): 0, (1, 5): 0, (5, 1): 0, ('other', 0): 0}
    for p in sympy.primerange(5, 1000):
        if sympy.isprime(p+4):
            a, b = p % 6, (p+4) % 6
            k = (a, b) if (a, b) in cousin_counts else ('other', 0)
            cousin_counts[k] = cousin_counts.get(k, 0) + 1
    print(f"\n  Cousin primes (p, p+4) by lane mod 6:")
    for k, v in cousin_counts.items():
        print(f"    {k}: {v} pairs")
    # Note: (p, p+4) with p > 3: 
    #   p ≡ 1 → p+4 ≡ 5;  p ≡ 5 → p+4 ≡ 3, but 3 not coprime to 6, so p+4 = 3·(something) typically composite UNLESS p+4 = 3 itself.
    # So all cousin primes p > 3 satisfy p ≡ 1, p+4 ≡ 5 mod 6.  Sign: chi(p)chi(p+4) = (1)(-1) = -1.

    return C2, twins, twin_counts


# =============================================================================
#  (e) Cohn-Elkies positivity numerics
# =============================================================================

def experiment_e():
    """Cohn-Elkies linear programming bounds for sphere packing have an
    L-function analog due to Cohn-Elkies and refinements by Sarnak-Strömbergsson:
    bounds on zeros of L-functions via positive-Fourier-pair functions.

    The simplest version: a positive Schwartz function f with f-hat also
    positive, normalized so f(0) = 1, gives an upper bound on certain
    Mellin-transform integrals related to L(s, χ).

    Numerical exploration: scan a 2-parameter family of Gaussian-modulated
    functions f(x) = exp(-a x²) (1 + b x²) and see where the Fourier pair
    stays positive and what bound emerges.

    This is rough — Cohn-Elkies in its full glory uses semidefinite-program
    optimization. Here I just sanity-check that the framework gives
    nontrivial constraints.
    """
    banner("Experiment (e):  Cohn-Elkies-style positivity numerics")

    from mpmath import quad as mpquad
    
    # Gaussian-Hermite family: f_a(x) = (something) · exp(-a x²)
    # Fourier transform (under unitary convention): (sqrt(π/a)) exp(-π² r²/a)
    # Both positive for any a > 0. Simplest possible Cohn-Elkies admissible pair.

    print("  Trivial admissible family: f(x) = exp(-a x²), f̂(r) = √(π/a) exp(-π² r²/a)")
    print("  Both positive for all a > 0. The 'bound' from this family:")
    print()
    print(f"    {'a':>8} {'f(0)=1':>10} {'f̂(0)':>10} {'sum f̂(γ_ρ)':>16}")

    # Use the zeros we found
    zeros_list = find_zeros(mpf(60))[:30]
    for a_val in [mpf("0.1"), mpf("0.5"), mpf(1), mpf(2), mpf(5)]:
        fhat_0 = sqrt(pi/a_val)
        sum_fhat_at_zeros = 2 * sum(sqrt(pi/a_val) * exp(-pi**2 * g**2 / a_val)
                                     for g in zeros_list)
        # The Cohn-Elkies-type inequality (sketch): sum over zeros ≤ f(0) · (some)
        print(f"    {float(a_val):8.3f} {1.0:10.5f} {float(fhat_0):10.5f} {float(sum_fhat_at_zeros):16.5e}")

    print()
    print("  Observation: for narrow Gaussians (a large), f̂ is wide and picks up")
    print("  more zeros' contributions, but the bound also gets larger.")
    print("  For wide Gaussians (a small), only the lowest zeros contribute,")
    print("  bound is tight but uses little information about the L-function.")
    print()
    print("  A genuine Cohn-Elkies application needs SDP optimization over a")
    print("  parametrized family of positive-Fourier pairs subject to the explicit")
    print("  formula — beyond what fits in a single experiment script.")


# =============================================================================
#  Main
# =============================================================================

if __name__ == "__main__":
    table_special = experiment_a()

    # Find zeros once and reuse
    print("\n  Locating zeros up to height 200 (may take a moment)...")
    zeros_list = find_zeros(mpf(200))
    print(f"  Found {len(zeros_list)} zeros.  First 10: {[nstr(z, 10) for z in zeros_list[:10]]}")

    experiment_b(zeros_list)
    alphas, Qs = experiment_c(zeros_list)
    C2, twins, twin_counts = experiment_d()
    experiment_e()

    print("\n" + "=" * 78)
    print("  Done.  See individual sections for results.")
    print("=" * 78)
