# A Minimal Conjecture: Borcherds-Shaped Products from Primes in Arithmetic Progressions

*Statement of the version supported by the computations, with the normalization
made explicit and the claims pared to what the data carries. Intended to sit
beside the verified results, not to overclaim beyond them.*

---

## 1. Setup

Fix an integer modulus $m \ge 3$. Let

$$
S \;=\; (\mathbb{Z}/m\mathbb{Z})^{\times}
\;=\; \{\, r : 1 \le r < m,\ \gcd(r,m)=1 \,\},
\qquad |S| = \varphi(m).
$$

For large $X$, let

$$
c_X(r) \;=\; \#\{\, p \le X : p \text{ prime},\ p \nmid m,\ p \equiv r \pmod m \,\},
\qquad r \in S .
$$

Fix a positive integer $\mathrm{rank}$ (a free parameter; the originating
framework took $\mathrm{rank}=2$ for $m=3$ and $\mathrm{rank}=5$ for $m=9$).
Define the formal product

$$
\boxed{\;
P_X(q) \;=\; \prod_{r \in S} (1-q^r)^{\,c_X(r)}
\;\times\; \prod_{k=1}^{\infty} (1-q^k)^{\,\mathrm{rank}}
\;}
\qquad |q|<1 .
$$

The first factor is *data-driven* (exponents are prime counts); the second is the
chosen *imaginary-root* factor.

---

## 2. The arithmetic decomposition

Prime equidistribution (PNT in arithmetic progressions / Dirichlet) gives
$c_X(r) \sim \pi(X)/\varphi(m)$ for every $r \in S$. Write the deviation from
perfect equidistribution as

$$
c_X(r) \;=\; \frac{\pi(X)}{\varphi(m)} \;+\; \delta_r(X).
$$

* **Sum of deviations is bounded:** $\sum_{r\in S}\delta_r(X) = O(1)$, since
  $\sum_{r\in S} c_X(r) = \pi(X) - \#\{p \le X : p \mid m\}$.
* **Individual size:** unconditionally only the Siegel–Walfisz bound holds
  (no power saving: $\delta_r(X) = O\!\big(X \exp(-c\sqrt{\log X})\big)$).
  **On GRH**, $\delta_r(X) = O\!\big(X^{1/2}\log X\big)$.
* **Structure:** the $\delta_r(X)$ encode the Chebyshev bias. Its *direction*
  (quadratic non-residue classes are favored — e.g. $\delta_2 > 0 > \delta_1$ for
  $m=3$) arises from the square/non-square structure of the classes, the
  secondary term in the explicit formula, **not** from any single zero. Its
  *fluctuations* are a sum over the full ensemble of nontrivial zeros of
  $L(s,\chi \bmod m)$. The precise statement — a limiting logarithmic density —
  is the Rubinstein–Sarnak theorem, conditional on GRH and the linear
  independence of the zero ordinates.

---

## 3. The two normalization regimes

Let $N = N(X) \to \infty$. The behaviour depends on whether the **global** power
$P_X^{1/N}$ is taken, or only the data exponents $c_X(r)$ are normalized.

### Regime A — global normalization (single power $P_X^{1/N}$)

Take $N = \pi(X)/\varphi(m)$, so that $c_X(r)/N \to 1$. The **same** power divides
the imaginary-root exponent: it becomes $\mathrm{rank}/N \to 0$, and the entire
infinite factor collapses,
$\prod_{k}(1-q^k)^{\mathrm{rank}/N} \to 1$. Hence

$$
\boxed{\;
P_X(q)^{1/N} \;\longrightarrow\;
L_A(q) \;=\; \prod_{r\in S}(1-q^r)
\;}
\qquad \text{(pointwise on } |q|<1).
$$

$L_A(q)$ is a **finite polynomial** of degree $\sum_{r\in S} r$, depending only on
$m$. For $m=3$:
$L_A(q) = (1-q)(1-q^2) = 1 - q - q^2 + q^3 = (1-q)^2(1+q)$.
For $m=9$: degree $27$, beginning $1 - q - q^2 + q^3 - q^4 + 2q^6 - \cdots$.

There is **no eta factor, no $\mathrm{rank}$, and no root system** in $L_A$. The
imaginary-root factor does not survive a genuine single-power normalization.

### Regime B — selective normalization (rank exempted by hand)

Normalize only the data exponents ($c_X(r) \mapsto c_X(r)/N \to 1$) and leave
$\mathrm{rank}$ untouched. Then

$$
L_B(q) \;=\; \prod_{r\in S}(1-q^r)\;\times\;\prod_{k=1}^{\infty}(1-q^k)^{\mathrm{rank}} .
$$

This retains the root-system factor — **but only because $\mathrm{rank}$ was
exempted from the limit by fiat.** It is not a single-power normalization of
$P_X$; it is a hand-split that refuses to normalize the part it wishes to keep.

> **Consequence.** The root-system / affine structure is never *produced* by the
> limit. Under honest global normalization it washes out (Regime A); it appears
> (Regime B) only when one declines to normalize the input one inserted by hand.

---

## 4. Where the prime distribution actually enters

In **neither** limit. $L_A$ depends only on $S$ (equivalently, only on $m$);
$L_B$ depends only on $S$ and the chosen $\mathrm{rank}$. The prime distribution
enters solely through $\delta_r(X)$, in the **first correction**:

$$
P_X(q)^{1/N}
= \Big[\textstyle\prod_{r\in S}(1-q^r)\Big]\cdot
\exp\!\Big(\underbrace{\tfrac{1}{N}\textstyle\sum_{r\in S}\delta_r(X)\,\log(1-q^r)}_{\text{prime-carrying term}}
\;+\;\tfrac{\mathrm{rank}}{N}\textstyle\sum_{k}\log(1-q^k)\Big).
$$

The prime-carrying term has size $O(\delta/N) = O\!\big(\log X / X^{1/2}\big)$ on
GRH and $\to 0$. It — and only it — encodes the Chebyshev bias, i.e. the zeros of
$L(s,\chi \bmod m)$.

---

## 5. The conjecture (minimal form)

> **Conjecture (minimal, signable).**
> With notation as above, for every fixed $m \ge 3$ and fixed
> $\mathrm{rank}\in\mathbb{Z}_{>0}$:
>
> 1. **(Global limit.)** $P_X(q)^{1/N} \to \prod_{r\in S}(1-q^r)$ pointwise on
>    $|q|<1$, with $N=\pi(X)/\varphi(m)$. The limit is a finite polynomial
>    determined by $m$ alone; the imaginary-root factor does not survive.
> 2. **(Selective limit.)** If instead only the data exponents are normalized,
>    the limit is $\prod_{r\in S}(1-q^r)\cdot\prod_k(1-q^k)^{\mathrm{rank}}$; the
>    extra factor is present only by exempting $\mathrm{rank}$ from the limit.
> 3. **(Locus of arithmetic.)** The prime distribution influences $P_X$ only
>    through the deviations $\delta_r(X)=c_X(r)-\pi(X)/\varphi(m)$, entering at
>    first order via $\sum_{r\in S}\delta_r(X)\log(1-q^r)$. This correction is
>    controlled by the zeros of $L(s,\chi\bmod m)$ (square-root size on GRH;
>    Siegel–Walfisz unconditionally).

This is true, computable, and free of overclaim.

---

## 6. Honest status

* **Classical content.** The statement is a repackaging of the prime number
  theorem in arithmetic progressions with effective error terms. The
  number-theoretic substance is classical; the product is a faithful bookkeeping
  device, not a new probe of the primes.

* **"Borcherds-shaped," not a Borcherds lift.** A genuine Borcherds product
  requires the exponents to be Fourier coefficients of a (weakly holomorphic,
  vector-valued) modular form, yielding an automorphic output with a controlled
  divisor. Prime counts are not modular-form coefficients, the output here is not
  automorphic, and the imaginary-root multiplicity is chosen rather than derived.
  "Borcherds-type" must be read as *Borcherds-shaped notation*, not a Borcherds
  lift.

* **No root system in the limit.** Under honest (global) normalization the
  affine / root-system factor vanishes; the surviving object is the finite
  congruence product $\prod_{r\in S}(1-q^r)$.

* **No coupling constant anywhere.** Neither $P_X$, nor $L_A$, nor $L_B$, nor the
  correction term contains $\alpha_{\mathrm{em}}$, $\alpha_\chi$, or any
  dimensionful or running quantity. The construction does not, and structurally
  cannot, compute a physical coupling: every ingredient is an integer count, a
  residue, a rank, or $q$.

---

## 7. Computational support (already verified)

* Equidistribution: normalized exponents $c_X(r)\,\varphi(m)/\pi(X) \to 1$ for
  every $r\in S$ (checked $m=3,9$ to $X=10^6$–$10^7$).
* Coarse structure is generic: the sign/growth pattern of $P_X$'s coefficients is
  identical for prime counts, an equidistributed split, and arbitrary integers of
  the same magnitude — binomial dominance, not a prime fingerprint.
* Rank washout: $\prod_k(1-q^k)^{\mathrm{rank}/N}\to[1,0,0,\dots]$ as $N\to\infty$
  (verified to $N=10^5$).
* Locus of arithmetic: $\delta_2 > 0 > \delta_1$ for $m=3$ at every checked $X$
  (the Chebyshev bias toward the non-residue class), decaying $\sim X^{-1/2}$.

---

*Companion results that stand independently and need none of the above:
$\alpha_\chi=\pi/\log q$ as a spectral parameter; the identity
$\Theta_{\Lambda_{24}}/\Delta = j-720$ (whence $196884 = 196560 + 324$); the
Eisenstein tower and its level structure; the Lean-verified files at zero
sorries.*
