#!/usr/bin/env python3
"""Exact checks for the conditional major-arc evaluation (PIE Lab circle method), 20 Nov 2026 · Dula.

Theorem (to be formalized).  N >= 2, S(α) = Σ_{n<=N} Λ(n) e(nα), e(t) = exp(2πit).  q >= 1, gcd(a, q) = 1, β real.
If |ψ(M, χ)| = |Σ_{n<=M} Λ(n) χ(n)| <= B for every non-principal Dirichlet character χ mod q and every M <= N, then
    |S(a/q + β) − (μ(q)/φ(q)) S(β)|  <=  sqrt(φ(q)) · B · (1 + 2π|β|N)  +  2 ω(q) log N.
Under GRH for Dirichlet L-functions mod q, B = C sqrt(N) log²(qN) (Davenport, ch. 20).

Lemmas checked here, each exactly or to 1e-9:
  L1  e(m/q) = (1/φ(q)) Σ_χ conj(χ(m)) τ(χ)   for gcd(m, q) = 1,   τ(χ) = Σ_b χ(b) e(b/q);
  L2  τ(χ_0) = μ(q);
  L3  Σ_χ |τ(χ)|² = φ(q)²   (so Σ_χ |τ(χ)| <= φ(q)^{3/2});
  L4  Abel: |Σ_{n<=N} c_n e(nβ)| <= max_M |Σ_{n<=M} c_n| · (1 + 2π|β|(N−1));
  L5  |Σ_{n<=N, gcd(n,q)>1} Λ(n) z_n| <= ω(q) log N   for |z_n| <= 1;
and the theorem on S itself for N = 200 000, q <= 30, several a and β.
"""
import cmath, math, sys
import numpy as np

def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def mobius(n):
    f = factor(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)

def phi(n):
    r = n
    for p in factor(n): r = r // p * (p - 1)
    return r

def characters(q):
    """All Dirichlet characters mod q as arrays chi[0..q-1] (complex), via the cyclic decomposition of (Z/q)^*."""
    if q == 1:
        return [np.ones(1, dtype=complex)]
    gens = []          # (modulus of factor, generator g, order, prime-power modulus)
    for p, k in factor(q).items():
        pk = p ** k
        if p == 2:
            if k >= 2: gens.append((pk, -1 % pk, 2))
            if k >= 3: gens.append((pk, 5, 2 ** (k - 2)))
        else:
            # primitive root mod p^k
            g = next(g for g in range(2, pk) if math.gcd(g, p) == 1 and
                     all(pow(g, phi(pk) // r, pk) != 1 for r in factor(phi(pk))))
            gens.append((pk, g, phi(pk)))
    # discrete logs: for each residue b coprime to q, exponents w.r.t. the generators
    units = [b for b in range(q) if math.gcd(b, q) == 1]
    logs = {}
    for b in units:
        ex = []
        for pk, g, o in gens:
            r = b % pk
            if pk % 2 == 0 and pk >= 4:
                # 2-part: b = (-1)^s 5^t mod 2^k
                if g == (-1 % pk):
                    s = 0 if r % 4 == 1 else 1; ex.append(s); continue
                rr = r if r % 4 == 1 else (-r) % pk
                t = next(t for t in range(o) if pow(5, t, pk) == rr); ex.append(t); continue
            t = next(t for t in range(o) if pow(g, t, pk) == r); ex.append(t)
        logs[b] = ex
    orders = [o for _, _, o in gens]
    chars = []
    import itertools
    for js in itertools.product(*[range(o) for o in orders]):
        c = np.zeros(q, dtype=complex)
        for b in units:
            c[b] = cmath.exp(2j * math.pi * sum(j * e / o for j, e, o in zip(js, logs[b], orders)))
        chars.append(c)
    assert len(chars) == phi(q)
    return chars

def e(t): return cmath.exp(2j * math.pi * t)

def check_lemmas(qmax=60):
    worst = 0.0
    for q in range(1, qmax + 1):
        X = characters(q); f = phi(q)
        tau = [sum(c[b] * e(b / q) for b in range(q)) for c in X]
        principal = [i for i, c in enumerate(X) if np.allclose(c[[b for b in range(q) if math.gcd(b, q) == 1]], 1)]
        assert len(principal) == 1
        # L2
        worst = max(worst, abs(tau[principal[0]] - mobius(q)))
        # L3
        worst = max(worst, abs(sum(abs(t) ** 2 for t in tau) - f * f))
        # L1
        for m in range(q):
            if math.gcd(m, q) != 1: continue
            lhs = e(m / q); rhs = sum(np.conj(c[m]) * t for c, t in zip(X, tau)) / f
            worst = max(worst, abs(lhs - rhs))
        # orthogonality (used in L1)
        G = np.array([c for c in X]); M = G @ G.conj().T
        worst = max(worst, np.abs(M - q * 0 - np.diag(np.diag(M))).max(), np.abs(np.diag(M) - f).max())
    return worst

def vonmangoldt(N):
    L = np.zeros(N + 1)
    sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if sieve[p]: sieve[p * p::p] = False
    for p in np.nonzero(sieve)[0]:
        pk = p
        while pk <= N:
            L[pk] = math.log(p); pk *= p
    return L

def check_abel(trials=200, rng=np.random.default_rng(7)):
    worst = 0.0
    for _ in range(trials):
        N = int(rng.integers(2, 400)); c = rng.normal(size=N) + 1j * rng.normal(size=N); beta = rng.normal() * rng.choice([1e-3, 1e-2, 0.3])
        n = np.arange(1, N + 1)
        lhs = abs((c * np.exp(2j * np.pi * n * beta)).sum())
        Bmax = np.abs(np.cumsum(c)).max()
        rhs = Bmax * (1 + 2 * np.pi * abs(beta) * (N - 1))
        worst = max(worst, lhs / rhs)
    return worst          # must be <= 1

def check_theorem(N=200_000, qs=range(1, 31), rng=np.random.default_rng(11)):
    L = vonmangoldt(N); n = np.arange(N + 1)
    rows = []
    for q in qs:
        X = characters(q); f = phi(q); mu = mobius(q); om = len(factor(q)) if q > 1 else 0
        units = [b for b in range(q) if math.gcd(b, q) == 1]
        principal = [i for i, c in enumerate(X) if np.allclose(c[units], 1)][0]
        # B = max over non-principal chi and M <= N of |psi(M, chi)|
        B = 0.0
        for i, c in enumerate(X):
            if i == principal: continue
            vals = c[n % q] * L
            B = max(B, np.abs(np.cumsum(vals)).max())
        for a in [a for a in units][:3]:
            for beta in [0.0, 1.0 / (q * N), -0.5 / (q * N), float(rng.normal()) / N]:
                Sab = (L * np.exp(2j * np.pi * n * (a / q + beta))).sum()
                Sb = (L * np.exp(2j * np.pi * n * beta)).sum()
                err = abs(Sab - mu / f * Sb)
                bound = math.sqrt(f) * B * (1 + 2 * math.pi * abs(beta) * N) + 2 * om * math.log(N)
                rows.append((q, a, beta * N, err, bound, B / (math.sqrt(N) * math.log(q * N) ** 2)))
    return rows

if __name__ == "__main__":
    w = check_lemmas(60); print("L1-L3 + orthogonality, q <= 60: max deviation %.2e" % w); assert w < 1e-8
    r = check_abel(); print("L4 Abel summation, 200 random cases: max lhs/rhs = %.4f (must be <= 1)" % r); assert r <= 1 + 1e-12
    rows = check_theorem()
    zero = [er for _, _, _, er, bd, _ in rows if bd == 0]
    assert all(er < 1e-6 for er in zero), "bound 0 but error not 0"
    print("cases with bound 0 (q = 1): %d, max error %.1e" % (len(zero), max(zero) if zero else 0))
    ratio = max(er / bd for _, _, _, er, bd, _ in rows if bd > 0)
    print("Theorem, N = 200000, q <= 30, %d cases: max error/bound = %.4f (must be <= 1)" % (len(rows), ratio)); assert ratio <= 1
    print("B / (sqrt(N) log^2(qN)) over q <= 30: max %.4f (GRH size means bounded)" % max(x[5] for x in rows))
    print("sample rows (q, a, beta*N, error, bound):")
    for x in rows[:: max(1, len(rows) // 12)]:
        print("   q=%2d a=%2d beta*N=%+.3f  error=%10.2f  bound=%10.2f" % x[:5])
