import numpy as np, mpmath as mp
X = 2_000_000
L = np.zeros(X + 1); sv = np.ones(X + 1, bool); sv[:2] = False
for p in range(2, int(X**0.5) + 1):
    if sv[p]: sv[p*p::p] = False
for p in np.nonzero(sv)[0]:
    q = p
    while q <= X: L[q] = np.log(p); q *= p
n = np.arange(X + 1)
A = np.cumsum(np.where(n > 0, L / np.maximum(n, 1), 0.0))   # sum_{m<=n} Λ(m)/m
P = np.cumsum(L)                                            # ψ(n)
g = float(mp.euler)
def mellin(s):
    # on [n, n+1): S(x) = A[n] x − P[n];  G(x) = A[n] x − P[n] − x log x + (1+γ) x;  integrate against x^{-s-1} exactly
    tot = mp.mpf(0)
    a = mp.mpf(1); 
    # vectorised exact integrals of x^{1-s-1}=x^{-s}, x^{-s-1}, x^{-s} log x on [k, k+1]
    k = np.arange(1, X, dtype=float); k1 = k + 1
    I1 = (k1**(1 - s) - k**(1 - s)) / (1 - s)                      # ∫ x^{-s}
    I0 = (k1**(-s) - k**(-s)) / (-s)                               # ∫ x^{-s-1}
    F = lambda x: x**(1 - s) * (np.log(x) / (1 - s) - 1 / (1 - s)**2)
    Il = F(k1) - F(k)                                              # ∫ x^{-s} log x
    An, Pn = A[1:X], P[1:X]
    val = (An * I1 - Pn * I0 - Il + (1 + g) * I1).sum()
    return val
for s in (2.0, 3.0, 1.5):
    lhs = mellin(s)
    z = mp.zeta(s); dz = mp.zeta(s, derivative=1)
    rhs = -(dz / z) / (s * (s - 1)) - 1 / (s - 1)**2 + (1 + g) / (s - 1)
    print("s = %.1f: integral to X = %.0e: %.8f   formula: %.8f   difference %.1e" % (s, X, lhs, float(rhs), abs(lhs - float(rhs))))
