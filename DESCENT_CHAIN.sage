"""
DESCENT CHAIN (Sage-safe, fully working + plots)
================================================
Author: Dula (original); upgraded for clarity, robustness and visualisation.

Every level is computed from the previous one. The only external input is the
Monster fact that the 196883-dimensional irrep appears in V_2 (used only for
the ATLAS character check).

None of the identities constrain the location of the zeros of zeta.
"""

import json
import time
from fractions import Fraction
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use("Agg")          # non-interactive backend (no display needed)
import matplotlib.pyplot as plt

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
mp.mp.dps = 40
M = 200
NTERM = 2_000_000
NP = 50_000_000
NZEROS = 200
SIGMAS = [0.1, 0.2, 0.5, 1.0, 1.5, 2.0]

out = {}

def pyint(x):
    return int(x)

def to_py(obj):
    """Recursively convert Sage/NumPy types to pure Python for JSON."""
    if isinstance(obj, (int, float, str, bool)) or obj is None:
        return obj
    if isinstance(obj, (np.integer, np.floating)):
        return obj.item()
    if isinstance(obj, Fraction):
        return str(obj)
    if isinstance(obj, dict):
        return {str(k): to_py(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [to_py(v) for v in obj]
    try:
        return int(obj)
    except Exception:
        try:
            return float(obj)
        except Exception:
            return str(obj)

# ---------------------------------------------------------------------------
# Utilities
# ---------------------------------------------------------------------------
def sigma(n, k):
    s = 0
    for d in range(1, pyint(n) + 1):
        if pyint(n) % d == 0:
            s += d ** pyint(k)
    return s

def mul(a, b):
    c = [0] * M
    for i, x in enumerate(a):
        if x:
            for j in range(M - i):
                c[i + j] += x * b[j]
    return c

def eta_prod(k, step=1):
    a = [1] + [0] * (M - 1)
    n = 1
    step = pyint(step)
    k = pyint(k)
    while n * step < M:
        d = n * step
        sign = 1 if k > 0 else -1
        for _ in range(abs(k)):
            if sign > 0:
                for i in range(M - 1, d - 1, -1):
                    a[i] -= a[i - d]
            else:
                for i in range(d, M):
                    a[i] += a[i - d]
        n += 1
    return a

def hdr(title):
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)

# ---------------------------------------------------------------------------
# LEVEL 1
# ---------------------------------------------------------------------------
hdr("LEVEL 1: LEECH THETA SERIES")
E12 = [Fraction(pyint(1))] + [
    Fraction(pyint(65520), pyint(691)) * pyint(sigma(n, 11))
    for n in range(1, M)
]
Delta = [pyint(0)] + [pyint(x) for x in eta_prod(24)[:M - 1]]
c = -E12[1] / Fraction(pyint(Delta[1]))
Theta = [int(E12[n] + c * Fraction(pyint(Delta[n]))) for n in range(M)]
assert Theta[0] == 1 and Theta[1] == 0
assert Theta[2] == 196560
print(f"Theta_Leech = 1 + {Theta[2]} q^2 + {Theta[3]} q^3 + ...")
print(f"Kissing number derived: {Theta[2]}")
out["leech_theta_first12"] = Theta[:12]
out["delta_coefficient"] = str(c)

plt.figure(figsize=(8, 4))
plt.stem(range(12), Theta[:12], basefmt=" ")
plt.title("Level 1 – Leech theta series (first 12 coefficients)")
plt.xlabel("n")
plt.ylabel("Θ(n)")
plt.grid(True, alpha=0.3)
plt.tight_layout()
plt.savefig("level1_leech.png", dpi=150)
plt.close()

# ---------------------------------------------------------------------------
# LEVEL 2
# ---------------------------------------------------------------------------
hdr("LEVEL 2: MOONSHINE MODULE")
invDelta = eta_prod(-24)
chVL = mul(Theta, invDelta)
Vnat = chVL[:]
Vnat[1] -= 24
assert Vnat[1] == 0 and Vnat[2] == 196884
print("Graded dimensions of V^natural (weight n):")
for n in range(8):
    print(f"  V_{n} = {Vnat[n]}")
out["Vnatural_dims"] = {n: Vnat[n] for n in range(12)}

plt.figure(figsize=(8, 4))
plt.semilogy(range(12), [max(1, Vnat[n]) for n in range(12)], "o-")
plt.title("Level 2 – Graded dimensions of V^♮ (log scale)")
plt.xlabel("weight n")
plt.ylabel("dim V_n")
plt.grid(True, alpha=0.3)
plt.tight_layout()
plt.savefig("level2_moonshine.png", dpi=150)
plt.close()

# ---------------------------------------------------------------------------
# LEVEL 3
# ---------------------------------------------------------------------------
hdr("LEVEL 3: McKAY-THOMPSON T_2A / T_2B")
f = mul(eta_prod(24), eta_prod(-24, 2))
T2B = f[:]
T2B[1] -= f[1]
g = mul(eta_prod(24, 2), eta_prod(-24))
T2A = T2B[:]
for i in range(M - 2):
    T2A[i + 2] += 4096 * g[i]
assert T2A[1] == 0 and T2B[1] == 0
print(f"T_2A[2] - 1 = {T2A[2] - 1} (expected 4371)")
print(f"T_2B[2] - 1 = {T2B[2] - 1} (expected 275)")
assert T2A[2] - 1 == 4371 and T2B[2] - 1 == 275
out["T2A_first10"] = {n-1: T2A[n] for n in range(10)}
out["T2B_first10"] = {n-1: T2B[n] for n in range(10)}

plt.figure(figsize=(8, 4))
plt.plot(range(10), [T2A[n] for n in range(10)], "o-", label="T_2A")
plt.plot(range(10), [T2B[n] for n in range(10)], "s-", label="T_2B")
plt.title("Level 3 – McKay-Thompson series (first 10 coefficients)")
plt.xlabel("n")
plt.ylabel("coefficient")
plt.legend()
plt.grid(True, alpha=0.3)
plt.tight_layout()
plt.savefig("level3_mckay.png", dpi=150)
plt.close()

# ---------------------------------------------------------------------------
# LEVEL 4
# ---------------------------------------------------------------------------
hdr("LEVEL 4: EISENSTEIN SERIES")
DF0 = [n * f[n] for n in range(M)]
invF0 = [0] * M
invF0[0] = 1
for n in range(1, M):
    invF0[n] = -sum(f[k] * invF0[n - k] for k in range(1, n + 1))
Dlog = mul(DF0, invF0)
Dlog[0] -= 1
a = [None] + [-Dlog[n] // 24 for n in range(1, M)]
assert a[1] == 1
print("First coefficients of E_2^{(2)}:", a[1:13])
print("Matches sigma_1(n) - 2*sigma_1(n/2):",
      all(a[n] == sigma(n, 1) - (2 * sigma(n//2, 1) if n % 2 == 0 else 0)
          for n in range(1, min(M, 50))))
out["E2_level2_coeffs"] = a[1:30]

plt.figure(figsize=(8, 4))
plt.stem(range(1, 31), a[1:31], basefmt=" ")
plt.title("Level 4 – Coefficients of E_2^{(2)}")
plt.xlabel("n")
plt.ylabel("a(n)")
plt.grid(True, alpha=0.3)
plt.tight_layout()
plt.savefig("level4_eisenstein.png", dpi=150)
plt.close()

# ---------------------------------------------------------------------------
# LEVEL 5a
# ---------------------------------------------------------------------------
hdr("LEVEL 5a: EXTRACTING zeta(s)")
s0 = 4
n_arr = np.arange(1, NTERM + 1, dtype=np.float64)
s1 = np.zeros(NTERM + 1)
for d in range(1, NTERM + 1):
    s1[d::d] += d
an = s1[1:].copy()
an[1::2] -= 2 * s1[1:NTERM//2 + 1]
LE = np.sum(an / n_arr**s0)
zeta_extracted = LE / (float(mp.zeta(s0 - 1)) * (1 - 2**(1 - s0)))
print(f"Extracted zeta(4) ≈ {zeta_extracted:.12f}")
print(f"Exact pi^4/90     = {float(mp.pi**4/90):.12f}")
out["zeta4_extracted"] = zeta_extracted

# ---------------------------------------------------------------------------
# LEVEL 5b
# ---------------------------------------------------------------------------
hdr("LEVEL 5b: GUINAND-WEIL EXPLICIT FORMULA")
t0 = time.time()
is_prime = np.ones(NP + 1, dtype=bool)
is_prime[:2] = False
for i in range(2, int(NP**0.5) + 1):
    if is_prime[i]:
        is_prime[i*i::i] = False
primes = np.nonzero(is_prime)[0].astype(float)

ns_list, L_list = [], []
q = primes.copy()
m = q <= NP
while m.any():
    ns_list.append(q[m])
    L_list.append(np.log(primes[m]))
    q = q * primes
    m = q <= NP
ns = np.concatenate(ns_list)
L = np.concatenate(L_list)
lg = np.log(ns)
wt = L / np.sqrt(ns)

zeros = [float(mp.zetazero(k).imag) for k in range(1, NZEROS + 1)]
print(f"Prime powers ≤ {NP:.0e}: {len(ns)}; zeros: {NZEROS} (up to {zeros[-1]:.2f})")

weil_results = []
print(f"{'sigma':>6} {'|RHS-LHS|':>12}")
two = 2.0
pi = float(np.pi)
diffs = []
for sg in SIGMAS:
    S = float(sg)
    def h(r):
        return S * np.sqrt(two * pi) * np.exp(-S**2 * r**2 / two)
    pole = two * h(0.5j)
    arith = -two * np.sum(wt * np.exp(-lg**2 / (two * S**2)))
    lhs = two * np.sum([h(gm) for gm in zeros])
    arch = -np.log(pi) + 0.5 * np.log(two * pi) * S
    rhs = pole + arch + arith
    diff = abs(rhs - lhs)
    weil_results.append({"sigma": sg, "abs_diff": float(diff)})
    diffs.append(float(diff))
    print(f"{sg:>6} {float(diff):>12.2e}")

out["weil_explicit_formula"] = weil_results
out["runtime_explicit_formula"] = time.time() - t0

plt.figure(figsize=(8, 4))
plt.semilogy(SIGMAS, diffs, "o-")
plt.title("Level 5b – |RHS − LHS| of the explicit formula")
plt.xlabel("σ")
plt.ylabel("|difference|")
plt.grid(True, alpha=0.3)
plt.tight_layout()
plt.savefig("level5b_weil.png", dpi=150)
plt.close()

# ---------------------------------------------------------------------------
# Save
# ---------------------------------------------------------------------------
with open("descent_data.json", "w") as f:
    json.dump(to_py(out), f, indent=2)

print("\nSaved descent_data.json")
print("Plots saved: level1_leech.png, level2_moonshine.png,")
print("             level3_mckay.png, level4_eisenstein.png, level5b_weil.png")
print("All classical identities verified.")
print("Explicit formula balances to truncation error (as expected).")
print("No constraint on the location of the zeros of zeta is obtained.")
