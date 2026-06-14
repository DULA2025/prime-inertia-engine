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

1. **Level‑3 (order‑3) moonshine.** The complex Leech's `6·Suz`, the Suzuki chain
   inside `Co₁`, and the order‑3 conjugacy classes of the Monster all point at the
   weight‑12 level‑3 floor. *Open and uncomputed:* does the complex‑Leech theta /
   the newform `g` match a McKay–Thompson series for an order‑3 Monster element?
   This is the genuine frontier question, not a textbook fact.

2. **Eisenstein‑ideal depth.** The tower says *which* primes `ℓ` collapse; computing
   `ord_ℓ` of the numerator measures the *size* of the collapse (Herbrand–Ribet:
   the relevant class group / congruence module), probing the `ℤ[ω]`‑Iwasawa
   structure directly. A few lines beyond the present computation.

3. **Higher newspaces.** `dim S_{14}^{new}(Γ₀(3)) = 3`: the first floor with
   *irrational* Hecke eigenvalues (a real cubic or quadratic field), where the
   angle data acquires genuine higher‑rank arithmetic.
