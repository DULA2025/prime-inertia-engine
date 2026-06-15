# The Eisenstein / A₂ Face: A Climb up the Γ₀(3) Weight Tower

*A map of the rung closest to the formalized DULA work. Every object below is one
you have already touched — the χ₃ grading, K₁₂, the Eisenstein-prime tower, the
complex Leech — assembled into a single ladder and extended one floor. All numbers
were verified computationally; sources of each result (classical vs. new framing)
are marked.*

---

## 0. The one object behind four faces

The primes mod 3 are organized by a single automorphic object, seen four ways:

| Face | What it is | What carries the primes |
|---|---|---|
| **Geometry** | hexagonal lattice `A₂ = ℤ[ω]` | splitting law `p ≡ 1 mod 3` |
| **Analysis** | `L(s,χ₃)` | its zeros (explicit formula) |
| **Representation theory** | `SU(2)` | Frobenius angles `θ_p` (Sato–Tate) |
| **Rigidity** | random-matrix statistics | GUE spacing of the zeros |

This note climbs the geometric/automorphic face, where the lattices are the rungs.

---

## 1. Ground floor (weight 1): A₂ sees one bit per prime

`A₂` is the ring of Eisenstein integers `ℤ[ω]`, `ω = e^{2πi/3}`. Its theta series is
the weight‑1 Eisenstein series for `Γ₀(3)`, and its representation numbers are

$$
r(n) \;=\; 6\sum_{d\mid n}\chi_3(d),
\qquad
r(p)=\begin{cases}12 & p\equiv 1 \ (3)\ \text{(split: } p=a^2+ab+b^2)\\[2pt] 0 & p\equiv 2\ (3)\ \text{(inert)}.\end{cases}
$$

*(Verified for all `n ≤ 200`.)* The Epstein zeta factors as
`∑ r(n)n^{-s} = 6·ζ(s)·L(s,χ₃)`. The lattice geometry **is** the splitting law.
At this floor a prime carries exactly one bit: `χ₃(p) ∈ {+1,−1}`.

*(Classical: `ℤ[ω]`, class number 1 of `ℚ(√−3)`.)*

---

## 2. The tower and its Eisenstein primes

The cusp spaces for `Γ₀(3)` have dimension (even `k ≥ 4`)

$$
\dim S_k(\Gamma_0(3)) = \left\lfloor k/3\right\rfloor - 1 .
$$

The **Eisenstein primes** of `S_k(Γ₀(3))` — the primes `ℓ` at which a cusp form is
congruent mod `ℓ` to the weight‑`k` Eisenstein series — are the prime factors of

$$
\operatorname{num}\!\left(\frac{(3^k-1)\,B_k}{2k}\right).
$$

**New structural fact (verified): this set splits cleanly by old/new.**

$$
\operatorname{num}\!\left(\tfrac{(3^k-1)B_k}{2k}\right)
=\underbrace{\operatorname{num}\!\left(\tfrac{B_k}{2k}\right)}_{\text{irregular primes}\,\to\,\text{OLDforms}}
\;\times\;\underbrace{\big(\text{surviving primes of }3^k-1\big)}_{\text{primitive primes}\,\to\,\text{NEWforms}}
$$

| `k` | irregular → oldforms (level‑1 Ramanujan) | primitive `3^k−1` → newforms (level‑3) |
|---|---|---|
| 6  | (none) | **13** |
| 8  | (none) | 41 |
| 10 | (none) | 11, 61 |
| 12 | **691** | **73** |
| 14 | (none) | 547, 1093 |
| 16 | 3617 | 41, 193 |
| 18 | 43867 | 13, 37, 757 |
| 20 | 283, 617 | 11, 61, 1181 |

The irregular primes (`691, 3617, 43867, …`) are Kummer's, and they attach to the
**oldforms** (the level‑1 forms re‑embedded). The primitive prime divisors of
`3^k−1` are genuinely level‑3 and attach to the **newforms**. The tower formula is
the *union*; the two families live on different forms. This is the level‑3
analogue of Ramanujan's `691`, with the level‑1 piece appearing as the oldform
contribution exactly when `S_k(SL₂(ℤ)) ≠ 0`.

*(Eisenstein‑ideal congruences are classical — Mazur, Herbrand–Ribet; the explicit
old/new split of this particular tower is the new framing.)*

---

## 3. Sixth floor (weight 6): K₁₂ and the first cusp form

`K₁₂` (Coxeter–Todd, the rank‑6 `ℤ[ω]` lattice, 12 real dimensions) sits at weight 6
— the first floor with a cusp form. The newspace is one‑dimensional, the newform

$$
f \;=\; \eta(\tau)^6\,\eta(3\tau)^6 \;=\; q\prod_{n\ge1}(1-q^n)^6(1-q^{3n})^6,
\qquad a_f(1..8)=[1,-6,9,4,6,-54,-40,168].
$$

Verified a Hecke eigenform (`a₄ = a₂² − 2⁵`, multiplicativity; `a₃ = 9 = 3²` at the
bad prime). Its **mod‑13 congruence** holds for every tested prime:

$$
a_f(p) \equiv 1 + p^5 \pmod{13}, \qquad 13 = \operatorname{num}\!\big((3^6-1)B_6/12\big).
$$

This is exactly the K₁₂ mod‑13 Eisenstein congruence, now at the level of Hecke
eigenvalues. **Sato–Tate** for `f`: `a_f(p)/(2p^{5/2}) = cos θ_p` fills the
semicircle (moments `E[cos²] = 0.244 ≈ ¼`, `E[cos⁴] = 0.118 ≈ ⅛`), uniformly over
both residue classes mod 3, and `f` is non‑CM (`a_p ≠ 0` on inert primes).

**The depth jump.** The ground floor assigns a prime one bit, `χ₃(p)`. This floor
assigns a prime a *continuous angle* `θ_p ∈ [0,π]` — the Frobenius conjugacy class
in `SU(2)`. The cusp form carries an irreducible 2‑dimensional Galois
representation; the Eisenstein/`A₂` layer is the reducible 1‑dimensional one.

---

## 4. Twelfth floor (weight 12): the complex Leech

Here `dim S_{12}(Γ₀(3)) = 3 = ⟨Δ(τ),\,Δ(3τ)⟩ \oplus ⟨g⟩`: two oldforms from `Δ`
plus one level‑3 newform `g`, with

$$
a_g(1..8) = [1,\,78,\,-243,\,4036,\,-5370,\,-18954,\,-27760,\,155064],
\qquad a_g(3) = -243 = -3^5 .
$$

Verified a Hecke eigenform. The congruences **separate exactly** as Section 2
predicts:

* `a_g(p) \equiv 1 + p^{11} \pmod{73}` — holds for all tested primes (`73 ∣ 3^{12}−1`, **new**, on `g`);
* `τ(p) \equiv 1 + p^{11} \pmod{691}` — holds (Ramanujan, **old**, on `Δ`);
* `g` does **not** satisfy the 691 congruence — 691 belongs to the oldform.

The **complex Leech lattice** (the Leech lattice with its `ℤ[ω]`‑module structure,
rank 12 over `ℤ[ω]`, 24 real dimensions) lives on this floor, with automorphism
group `6·Suz` (Suzuki sporadic group). This is the level‑3 floor directly above the
level‑1 weight‑12 world, where the verified moonshine identity
`Θ_{Λ₂₄}/Δ = j − 720` lives.

---

## 5. The unifying statement

Climbing the tower **raises the dimension of the Galois representation attached to a
prime** — from the 1‑dimensional character `χ₃` (weight 1) to irreducible
2‑dimensional representations (weights 6, 12, …), i.e. from a bit to a sphere of
angles. The **Eisenstein primes are exactly the primes `ℓ` where that
representation degenerates back down**: mod `ℓ` the 2‑dimensional `ρ_f` becomes
reducible, splitting into two characters, and the Hecke eigenvalues collapse to the
Eisenstein/`A₂` values `a_p ≡ 1 + p^{k-1}`. The whole picture is the **Eisenstein
ideal at level 3** (Mazur), graded by weight, with:

* the **ground floor** `A₂` = the reducible (character) layer;
* the **upper floors** `K₁₂`, complex Leech = the irreducible (angle) layers;
* the **Eisenstein primes** = where upper collapses to ground, split into Kummer's
  irregular primes (on oldforms) and primitive divisors of `3^k−1` (on newforms).

---

## 6. Honest boundary

The newforms `f`, `g`, their congruences, and the Eisenstein ideal are established
mathematics (LMFDB newforms `3.6.a.a`, `3.12.a.a`; Mazur; Herbrand–Ribet). The
classical input is Dirichlet, Deligne + Sato–Tate, and Kummer. **What is
organizing rather than restating** is the single ladder — `A₂` (weight 1) → `K₁₂`
(weight 6) → complex Leech (weight 12) as the `ℤ[ω]` / `Γ₀(3)` tower, with the
old/new split of the Eisenstein‑prime formula and the "information‑depth"
reading of the weight grading. There is no coupling constant anywhere in this; the
order is automorphic, and that is the kind of order it is.

---

## 7. Open / next computations

1. **Level‑3 (order‑3) moonshine — re‑examined under normalization.** Three
   candidate bridges from the weight‑12 floor to `Suz`/order‑3 moonshine:
   * **By type — NOT a wall (normalization removes it).** Dividing by `Δ` lands
     `g` in weight 0: `g/Δ = 1 + 102u + 729u²` with `u = (η(3τ)/η(τ))¹²` the
     level‑3 Hauptmodul (exact, from `h = Δu`, `Δ(3τ) = Δu²`). This is the right
     *type* to compare with a McKay–Thompson series. But `g/Δ` is a **quadratic**
     in `u`, holomorphic at the cusp; an MT series is the Hauptmodul itself
     (degree 1, `q⁻¹ + O(q)`, with a pole). The identity is a basis tautology
     (`{Δ, Δu, Δu²}` spans the space; `102, 729=3⁶` are `g`'s coordinates, not
     Monster dimensions). Verdict: not moonshine — but for a basis reason, reached
     by doing the normalization, not by a type objection. 
   * **By level — Construction A excludes `g`; actual Leech symmetry-ALLOWS it,
     coefficient uncomputed.** The ternary Golay generator (verified) is the
     construction code, not `Λ_C/θΛ_C`. Construction A from it (`A_θ(C)`, min norm
     3, kissing 72) has theta `E₁₂(3τ) − (15768/691)Δ(3τ)` — a `V₃`-image,
     **`g`-coefficient 0**, killed by 3-divisible weights. The *actual* complex
     Leech (min norm 4, kissing 196560) is a different lattice; naive `ℤ[ω]`
     constructions all collapse to min norm 3, and the genuine structure needs an
     order-3 isometry of trace `−12` (non-monomial, full `Co₀`). KEY NEW FACT:
     `g` has Atkin–Lehner `W₃ = +1` (`a₃ = −3⁵`), and the `W₃ = +1` eigenspace of
     `S₁₂(Γ₀(3))` is `⟨Δ(τ)+729Δ(3τ), g⟩`. The complex Leech is 3-modular, so its
     level-3 coset-theta cusp content is Fricke-symmetric and lies in that
     eigenspace — which *contains* `g`. So `g` is **symmetry-allowed** (unlike
     Construction A). What remains is one Siegel–Weil coefficient, needing the
     explicit min-norm-4 lattice. Status: allowed, coefficient uncomputed. ⚠
   * **The A↔B tie.** The genuine twining series for the order-3 fixed-point-free
     symmetry (frame shape `3¹²/1¹²`) is the weight-0 eta-quotient
     `u = η(3τ)¹²/η(τ)¹²` — exactly the level-3 Hauptmodul from Bridge A. Since
     `g/Δ = 1 + 102u + 729u²`, the newform `g` is `Δ` times a quadratic in the real
     moonshine function. Real identity, but a basis tautology — the same wall from
     two sides.
   * **By prime pattern — closed.** The level‑3 Eisenstein primes are not the
     Monster primes (`13, 41, 11` land; `61, 73, 547, 1093, 193, 37, 757, 1181` do
     not). No normalization changes which primes divide `3^k−1`. ✗

   **The genuine open task:** build the complex Leech `ℤ[ω]`‑Gram matrix, reduce
   mod `√−3` to its `𝔽₃` code, form the congruence theta, and test whether `g`
   occurs in its cusp part. `6·Suz = Aut(Λ_C)` is real; genuine Suzuki moonshine
   exists within Conway moonshine (weight‑0/mock, indexed by `Suz` classes, Duncan
   et al.). Whether the *arithmetic* form `g` connects to that is the open question
   — and it lives in the refined theta, not in the naive bridges.

2. **Eisenstein‑ideal depth.** The tower says *which* primes `ℓ` collapse; computing
   `ord_ℓ` of the numerator measures the *size* of the collapse (Herbrand–Ribet:
   the relevant class group / congruence module), probing the `ℤ[ω]`‑Iwasawa
   structure directly. A few lines beyond the present computation.

3. **Higher newspaces.** `dim S_{14}^{new}(Γ₀(3)) = 3`: the first floor with
   *irrational* Hecke eigenvalues (a real cubic or quadratic field), where the
   angle data acquires genuine higher‑rank arithmetic.

---

## 8. The functorial reading (Langlands intersection — verified)

Every DULA object lands on a standard functorial operation for GL₂/ℚ, approached
from the arithmetic side. Each line below is computationally confirmed.

* **GL₁ Langlands = the χ₃ grading.** `χ₃ = χ₋₃` is the quadratic character of
  `ℚ(ω)=ℚ(√−3)`; `χ₃(p)=+1` iff `p` splits in `ℤ[ω]`. The residue-mod-3 grading at
  the foundation of DULA *is* class field theory for the Eisenstein field.

* **Base change `ℚ→ℚ(ω)` = lattice complexification `ℤ→ℤ[ω]`.** Self-twist test:
  `g ≠ g⊗χ₃` (differs at `p=2`), so `g` is non-CM and `BC_{ℚ(ω)}(g)` is cuspidal.
  The real-Leech → complex-Leech passage is the automorphic base change, hinged on χ₃.

* **Adjoint / Sym² functoriality = the Eisenstein tower (congruence primes).**
  Verified Eisenstein congruences, newform by newform:
  `a_p(f) ≡ 1+p⁵ (mod 13)` (wt 6) and `a_p(g) ≡ 1+p¹¹ (mod 73)` (wt 12), all primes
  tested. Meaning: `ρ_f mod 13` and `ρ_g mod 73` are **reducible** (`1 ⊕ χ^{k-1}`) —
  the cusp form degenerates to Eisenstein mod the tower prime. Specificity confirmed:
  691 → oldform Δ, 13 → f, 73 → g (the old/new split = which form the congruence
  hits). The tower numerator `num((3ᵏ−1)Bₖ/2k)` (analytic side) = reducibility locus
  of `ρ` (Galois side): reciprocity at one prime.

* **Symmetric-power functoriality = Sato–Tate.** Moments of `a_p(g)/p^{11/2}` over
  549 primes → `0,1,0,2,0,5,0,14` (Catalan). Each even moment `2m → Catalan(m)` ⇔
  `Sym^{2m}g` automorphic with nonvanishing edge L-value (Newton–Thorne 2021). The
  semicircle is the whole tower of symmetric-power lifts behaving well.

**Net:** the DULA objects are the GL₂ functorial structures seen arithmetically.
Not new functoriality — a coherence: the framework reconstructs base change, the
adjoint, and all symmetric powers from lattice/Eisenstein-tower data.

### 8.1 The tower is the principal GL₂→GL₁⊕GL₁ degeneration locus (verified k=6..42)

Computed with PARI mf (newform Hecke char polys, integer test
`ℓ | charpoly_{T_p}(1+p^{k-1})`). For every weight tested, `num((3ᵏ−1)Bₖ/2k)`
factors **exactly and exhaustively** into two reducibility families:

* **Bernoulli-numerator primes** (`691, 43867, 103·2294797, 1721, …`) — where the
  *oldform* rep degenerates (level-1 Ramanujan-type congruences).
* **`3ᵏ−1` primes** (`13, 73, 37, 757, 41, 6481, 11, 61, 271, 547, 1093, …`) —
  where a *newform* rep degenerates: `ρ mod ℓ ≅ 1 ⊕ χ^{k-1}`, reducible.

Every tower prime is a reducibility prime; the partition is complementary and
exhaustive at all eight floors. This is the old/new = level-1/level-3 = χ₃ split,
now read as: **each tower prime is a point where a GL₂ Galois rep in `S_k(Γ₀(3))`
degenerates to `GL₁ ⊕ GL₁`, one floor per weight.** (Direction `⊇`, airtight.)

**Honest converse caveat.** The tower is NOT the *whole* reducibility locus. A
control scan (all `ℓ<200`) found a stray reducible prime `5` at `k=18,30` not in
the tower numerator. Cause: small-prime weight collapse — mod `5` the exponent
`k−1` only matters mod `ℓ−1=4`, so `1+p^{k-1}` drops to the weight-2 shape `1+p`,
admitting a lower-weight Eisenstein congruence (Serre theta-cycle). A real but
small-prime-filtration effect, not weight-`k` tower structure. (An earlier
`χ₃`-twisted-Eisenstein explanation was wrong: `B_{k,χ₃}=0` for even `k` since
`χ₃` is odd — retracted.) So the precise statement: **the tower numerator is the
*principal* (weight-genuine) GL₂→GL₁⊕GL₁ degeneration locus, Bernoulli primes on
oldforms and `3ᵏ−1` primes on newforms, modulo small-prime weight artifacts.**

### 8.2 Adjoint vs Eisenstein: 17 and 73 are different primes

`73` is NOT the adjoint/Sym² prime — that was a conflation. Two distinct congruences:
* **cusp–cusp (adjoint).** `gcd_p(a_p(g) − τ(p)) = 2·3·17`, so `g ≡ Δ` mod **17**.
  By Hida this congruence number is the algebraic part of `L(Sym²g, k−1)/`period —
  the adjoint L-value carries `17` (`ρ_g ≡ ρ_Δ`, both irreducible).
* **cusp–Eisenstein.** `gcd_p(a_p(g) − (1+p¹¹)) = 3³·73`, so `ρ_g ≡ 1 ⊕ χ¹¹` mod
  **73** — the Eisenstein ideal, not the adjoint L-value.

### 8.3 The full reducibility locus = two families (tower = large-prime half)

Scanned all `ℓ<100`, weights 4–42. The cusp–Eisenstein reducibility locus of
`S_k(Γ₀(3))` is, exactly:
* **Newform family** `{ℓ : ord_ℓ(3) | k}` (from `3ᵏ−1`): verified `61→{10,20,30,40}`,
  `73→{12,24,36}`, `67→{22}`, `13`-newform`→{6,18,30,42}` — reducible at the
  multiples of `ord_ℓ(3)` (where a cusp form realizes it).
* **Oldform/Bernoulli family** `{ℓ : ℓ | num(B_{k₀}), k₀ ≡ k mod (ℓ−1)}`
  (level-1 Eisenstein, Serre-propagated): verified for every extra —
  `5←B₁₀, 7←B₁₄,B₂₈, 11←B₂₂, 13←B₂₆`, each along its progression mod `ℓ−1`.

The DULA tower numerator `num((3ᵏ−1)Bₖ/2k)` is the **large-prime principal part**
of this union: its `/2k` normalization cancels the small primes at their primitive
weights (`5|num(B₁₀)` cancels against `2k=20`; `7|num(B₁₄)` against `2k=28`),
keeping the genuine high primes (`73, 691, 41, 43867, …`). The small primes are the
Serre weight-filtration tail of the level-1 Eisenstein family.

### 8.4 Multiplicativity vs temperedness: the mod-l degeneration on the DULA monoid

Ramanujan-Petersson (temperedness) for the actual complex eigenvalues is Deligne's
theorem: |a_p| <= 2 p^{(k-1)/2}, verified over 10^4 primes for f, g, Delta (0
violations, sup|cos th_p| -> 1 slowly per Sato-Tate). It is NOT touched by anything
below; the mod-l story is a congruence only.

Verified structural picture (g, weight 12, l=73):
* **Multiplicativity is robust:** survives mod l. On the DULA monoid (n coprime to
  6), `a_n === sigma_{k-1}(n) (mod 73)` is EXACT; it first fails at n=3,6,9,...,
  the level-3 bad prime the monoid excludes by construction. The monoid is exactly
  the clean domain of the degeneration.
* **Temperedness is fragile:** it is what breaks. The multiplicative shadow
  `sigma_{k-1}(p)=1+p^{k-1}` is non-tempered (>> 2p^{(k-1)/2}). The Hecke/Satake
  polynomial `x^2 - a_p x + p^{k-1}` factors mod l as `(x-1)(x-p^{k-1})` -- the
  tempered (circle) parameters degenerate to the Eisenstein parameters {1,p^{k-1}}.
  This is the precise sense "temperedness fails mod l" -- it is Mazur's Eisenstein
  ideal / the reducibility primes of section 8.1.
* **The +-1 grading is NOT the driver (tested, negative):** the Satake roots
  {1,p^{k-1}} mod l show no correlation with chi_3(p)=chi_6(p); p^{k-1} mod l is
  never +-1. The grading is real (= the Q(w) character threaded throughout) but it
  does not control the temperedness failure.

Net: on the DULA monoid the Hecke system degenerates mod l to a multiplicative,
non-tempered Eisenstein system -- multiplicativity invariant, temperedness the
casualty, bad prime outside the monoid. A clean framework-level statement; not an
explanation of RP in C (that is Deligne), and not driven by the +-1 grading.

### 8.5 Two kinds of mod-l shadow: Eisenstein (non-tempered) vs CM (tempered)

Ramanujan's own moduli for tau (Delta, level 1) are 2,3,5,7,23,691. Two are
structurally opposite:

* **691 (Eisenstein):** `tau(n) === sigma_11(n) (mod 691)`. rho_Delta reducible;
  the shadow sigma_11 is NON-tempered (1+p^11). This is the "temperedness fails
  mod l" type -- same family as 73 for the level-3 newform g. No +-1 structure.
* **23 (CM/dihedral):** `tau(n) === [q prod(1-q^n)(1-q^{23n})] = eta(z)eta(23z)
  (mod 23)`, a weight-1 CM form for Q(sqrt-23). Verified n<4000. `tau(p) mod 23`
  takes {0,+2,-1} by the S_3 Frobenius class:
    (p/23)=-1 inert -> 0;  (p/23)=+1, p=u^2+23v^2 -> +2;  else -> -1.
  The +-1 = the quadratic character of Q(sqrt-23); the {+2,-1} = the cubic
  class-field layer (h=3). The shadow is a weight-1 form, hence TEMPERED
  (|b(p)|<=2): temperedness is PRESERVED here, not broken.

Consequence: the "+-1 multiplicative structure" and the "temperedness failure" live
at DIFFERENT moduli with opposite behavior. +-1 is the CM type (23, tempered
shadow, rho dihedral); temperedness-failure is the Eisenstein type (691/73,
non-tempered shadow, rho reducible). They do not coincide, and neither touches RP
in C (Deligne). The CM congruence is Delta's (level-1, CM by Q(sqrt-23)); the
level-3 newform g is non-CM and has no analogue.

### 8.6 The moduli scan terminates: Serre-Swinnerton-Dyer, and the three toolkits

"Try every modulus" has a finite, complete answer (Serre-Swinnerton-Dyer 1973),
confirmed computationally for Delta: the exceptional set is exactly
{2,3,5,7,23,691}.
  * {2,3,5,7,691} REDUCIBLE  (tau(p)==p^a+p^b mod l; Eisenstein, non-tempered shadow)
  * {23}          DIHEDRAL   (CM by Q(sqrt-23); the +-1 / cubic-class-field layer;
                              tempered shadow) -- the UNIQUE dihedral prime <1000.
For every other l, the mod-l image is full ({g in GL2(F_l): det in (F_l*)^11},
Serre open-image). No congruence anywhere else. Scanning more moduli finds nothing
new -- it is a theorem, not a search.

**Three toolkits, three problems (they share objects, not methods):**
  1. Congruences / modular arithmetic  -> the mod-l GALOIS structure of rho.
     Finite, now fully mapped (Serre-SwD). Silent about |a_p| in C.
  2. Viazovska magic functions         -> PACKING / energy optimization. Leech is
     the densest packing in 24D (Cohn-Kumar-Miller-Radchenko-Viazovska 2016);
     kissing 196560 optimal earlier (Levenshtein, Odlyzko-Sloane). Shares the Leech
     and modular forms with this project; does NOT bound eigenvalues.
  3. Etale cohomology / Weil conjectures -> the COMPLEX eigenvalue bound (RP).
     Deligne. Frobenius on cohomology; purity forces the size. This is the only
     toolkit aimed at RP, and it already settled it for holomorphic forms.

Kinship worth noting (honest): Viazovska-style Fourier optimization shares positivity
+duality DNA with the explicit-formula extremal-function methods in analytic number
theory -- but those bound L-function ZEROS (RH, pair correlation), not Hecke
eigenvalue SIZE (RP). Different conjecture. The open eigenvalue frontier is the
MAASS Ramanujan / Selberg eigenvalue conjecture (Kim-Sarnak 7/64 via Sym^n
functoriality); the full bound is unsolved and uses trace formulas, not packing.

### 8.7 Where Ramanujan and Viazovska meet: the Leech theta

The Leech lattice (densest packing in 24D, Cohn-Kumar-Miller-Radchenko-Viazovska
2016) has theta series `Theta_Leech = E_12 - (65520/691) Delta`, so its vector
counts are
        r(n) = (65520/691) ( sigma_11(n) - tau(n) ),   main term - cusp error.
This carries THREE Ramanujan facts simultaneously (all verified):
  * INTEGRALITY = the mod-691 congruence. r(n) is a whole-number vector count
    only because 691 | (sigma_11(n)-tau(n)), i.e. tau === sigma_11 (mod 691).
  * RAMANUJAN CONJECTURE (RP) = the error term is negligible: main ~ n^11,
    error = tau ~ n^{11/2}, so |error|/main -> 0 (1e-6, 1e-12, 1e-17 at n=10,100,1000).
    The Leech counts hug their Eisenstein/Siegel-Weil average BECAUSE of RP.
  * THE COMPLEX EIGENVALUES (tau(n), the cusp coefficients) ARE that error term.

So Ramanujan and Viazovska genuinely meet at the Leech: shared machinery
(E_4,E_6,Delta, Ramanujan-Serre derivative, theta + mock-modular), and the Leech
theta encodes Ramanujan's congruence, conjecture, and eigenvalues.

HONEST DIRECTION / METHOD CAVEATS:
  * The flow is RP -> lattice. RP (Deligne) is the INPUT that makes the error
    small; the lattice does not prove RP. The eigenvalues appear in the Leech but
    are bounded by geometry (Deligne), not by packing arguments.
  * These are CLASSICAL theta-series facts (Siegel-Weil + Deligne), DISTINCT from
    Viazovska's magic-function method (packing-density LP bounds), which neither
    uses nor produces RP. Two different true things about the same lattice.
