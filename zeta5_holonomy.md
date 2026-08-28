# Arithmetic holonomy for `ζ_5(3)` — certified numerical and arithmetic ingredients

**Status report.**  This document describes the companion effort living in the
directory `Zeta5/` (Lean library `Zeta5`, built with `lake build Zeta5.AxiomAudit`).
It is completely isolated from the rest of the repository: it defines no name in,
imports nothing from, and changes nothing in, the existing modules.

Everything claimed below as *rigorous* is a `sorry`-free Lean theorem whose
`#print axioms` output is one of `[propext]` or
`[propext, Classical.choice, Quot.sound]`; the full audit is
`Zeta5/AxiomAudit.lean`.

---

## 0. Scope, and what is *not* claimed

The goal was a high-assurance verification of the numerical and arithmetic
ingredients that an arithmetic-holonomy argument for `ζ_5(3) ∉ ℚ` consumes.

Three honest caveats, stated up front.

1. **No cost/budget criterion is claimed.**  An earlier version of this report
   presented the combination `BC(φ) + max_{|z|=1} log‖ψ‖ < 3.23494` as though it
   were the criterion of the paper.  It is not, and the claim has been withdrawn
   (§5).  The quantity has been renamed `Zeta5.archCostGuess` and is no longer
   part of the headline theorem.

2. **The internal template is not the published one.**  Tasks 1–4 below are
   about data specified inside this project (`Zeta5/Template.lean`,
   `Zeta5/BostCharles.lean`, `Zeta5/Coefficients.lean`).  Separately, the
   *published* 41-coefficient template is now encoded, with its rounding bound,
   in `Zeta5/PublishedTemplate.lean`, and a certified admissibility bound is
   proved for it (§5a).  The genuine auxiliary map `φ = t ∘ ψ`, with `t` the
   Hauptmodul of `X₀(5)`, *is* now formalised and its Bost–Charles integral is
   evaluated exactly (§5b) — but this is an evaluated integral only.  **No cost
   functional and no budget comparison is claimed for it**; on the contrary,
   §5b records a normalisation discrepancy with the quoted budget.

3. **The arithmetic holonomicity theorem itself is not formalised.**  The
   implication *(archimedean data + denominator type + radius) ⟹ (ζ_5(3) ∉ ℚ)*
   is an external theorem; nothing in `Zeta5/` proves or uses it, and nothing
   here claims `ζ_5(3) ∉ ℚ`.  What is delivered is the verification of some of
   the *inputs* to such an implication.

---

## 1. Template admissibility (Task 1) — **rigorous, unconditional**

File `Zeta5/Template.lean`.  The template is the degree-40 (i.e. 41-coefficient)
Apéry–Legendre polynomial normalised by a power of the distinguished prime:

```
ψ(z) = 5^(-45) · Σ_{k=0}^{40} (-1)^k C(40,k) C(40+k,k) z^k .
```

The 41 coefficients are given explicitly as a list (`Zeta5.tmplNum`), and
`Zeta5.tmplNum_eq` proves that the list really is `k ↦ C(40,k)·C(40+k,k)`.

Because the coefficients of `ψ(-z)` are all non-negative, the maximum of `|ψ|`
on the unit circle is *attained at `z = -1`* and equals the `ℓ¹`-norm of the
coefficient vector.  This is proved in both directions:

| result | statement |
|---|---|
| `Zeta5.norm_psi_le` | `‖z‖ = 1 → ‖ψ(z)‖ ≤ tmplL1` |
| `Zeta5.psi_neg_one` | `ψ(-1) = tmplL1` |
| `Zeta5.psi_norm_isGreatest` | `tmplL1` **is** the maximum of `‖ψ‖` on `‖z‖ = 1` |

with the exact rational value (`Zeta5.tmplL1_eq`)

```
max_{|z|=1} |ψ(z)| = 378150244155138145169182750209 / 5^45
                   = 378150244155138145169182750209 / 28421709430404007434844970703125
                   ≈ 0.0133049789 .
```

Hence (`Zeta5.template_log_max_neg`, `Zeta5.template_log_max_lt`)

```
max_{|z|=1} log |ψ(z)| = log(0.01330…) < -4 < 0 ,
```

i.e. the template is admissible, with a large margin (`≈ 4.32` in log scale).
No floating-point arithmetic is involved anywhere: the comparison
`Σ_k C(40,k)C(40+k,k) < 5^45` is an exact integer computation.

## 2. Certified Bost–Charles integral (Task 2) — **rigorous, unconditional**

File `Zeta5/BostCharles.lean`.  For `f` holomorphic near the closed unit disc,

```
BC(f) = (1/2π) ∫_0^{2π} log|f(e^{iθ})| dθ = ∫_0^1 log|f(e^{2πit})| dt ,
```

which is Mathlib's `circleAverage (fun z ↦ Real.log ‖f z‖) 0 1`.

*Reusable machinery.*  For a polynomial given by a rational coefficient list
whose constant term dominates, `Σ_{k≥1}|a_k| < |a_0|`, we prove

* `Zeta5.norm_polyEval_ge_of_dominant`: `|p(z)| ≥ |a_0| − Σ_{k≥1}|a_k|` on the
  closed unit disc, hence `Zeta5.polyEval_ne_zero_of_dominant`: no zeros there;
* `Zeta5.circleAverage_log_norm_polyEval`: therefore, by Jensen's formula
  (Mathlib's `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`),
  `BC(p) = log |a_0|` **exactly**.

This is better than validated quadrature: the integral is evaluated in closed
form, so the *only* numerical error in `BC` is the error in the final logarithm,
which is itself certified.

*Applied to the auxiliary factor* `φ(z) = (5 − z)² = 25 − 10z + z²`
(dominance `10 + 1 < 25`):

```
BC(φ) = log 25 = 2 log 5           (Zeta5.BC_eq_log_25)
3.2188 < BC(φ) < 3.219             (Zeta5.BC_gt, Zeta5.BC_lt)
```

The enclosure of the logarithm is validated numerics done from first principles
in `Zeta5/LogBounds.lean`: partial sums of the exponential series
(`Real.sum_le_exp_of_nonneg`) give lower bounds for `exp`, and the explicit tail
bound `Real.exp_bound` gives upper bounds, both applied at half the target
argument so that the hypothesis `|x| ≤ 1` holds; squaring yields

```
1.6094 < log 5 < 1.6095 .
```

## 3. Denominator type (Task 3) — **rigorous given one stated analytic input**

Files `Zeta5/Coefficients.lean`, `Zeta5/DenomType.lean`.  The coefficient
sequence of the certificate is

```
b_n = 5^{3n} / D_n ,   D_n = prime-to-5 part of  lcm(1,…,n)² · lcm(1,…,⌊13n/16⌋).
```

Proved unconditionally:

* `Zeta5.bseq_den`: the fraction is in lowest terms, so `den(b_n) = D_n`;
* `Zeta5.log_bDen`, `Zeta5.log_rawDen`: the exact logarithmic bookkeeping
  `log D_n = 2 log lcm(1,…,n) + log lcm(1,…,⌊13n/16⌋) − v₅ · log 5`;
* `Zeta5.ordProj_lcmUpTo_le`: `p^{v_p(lcm(1,…,n))} ≤ max(1,n)` (proved by
  induction from `Nat.factorization_lcm`), hence `Zeta5.tendsto_five_part`: the
  `5`-adic correction is `O(log n)` and disappears from the rate.

The one external analytic input is the Chebyshev/prime-number-theorem
asymptotic, carried as the explicit hypothesis

```
ChebyshevPNT : Tendsto (fun n ↦ log lcm(1,…,n) / n) atTop (𝓝 1)
```

(it is not in Mathlib, and it is *not* introduced as an axiom — it is a
hypothesis of the theorem).  Given it,

```
Zeta5.denomType_bseq : DenomType bseq (45/16),
```

i.e. `lim (1/n) log den(b_n) = 2 + 13/16 = 45/16`.  The `13/16`-truncated third
`lcm` factor is exactly what produces the fractional part of the type, and
`Zeta5.tendsto_log_lcm_trunc` proves that it contributes `13/16`.

## 4. The `5`-adic radius (Task 4) — **rigorous, unconditional**

File `Zeta5/Radius.lean`.  The `5`-adic size of the general term is computed
exactly:

```
|b_n|₅ = 5^{-3n}                       (Zeta5.padicNorm_bseq)
|b_n zⁿ|₅ = (|z|₅ / 125)ⁿ              (Zeta5.padicNorm_bseq_mul)
```

so the terms tend to `0` precisely when `|z|₅ < 125` and blow up when
`|z|₅ > 125`:

```
Zeta5.overconv_radius_bseq : IsOverconvRadius5 bseq (5^3).
```

The overconvergence radius is therefore exactly `R₅ = 5³`, independently
confirmed from the coefficients and with no analytic input.

## 5. The withdrawn comparison — **demoted, not a criterion**

File `Zeta5/Certificate.lean`.

```
budgetInput   = 3.23494                             -- external number, quoted
archCostGuess = BC(φ) + max_{|z|=1} log|ψ(z)|       -- NOT the published cost functional
```

The Lean statements `Zeta5.archCostGuess_lt_budgetInput` (margin `> 4`) and
`Zeta5.BC_lt_budgetInput` (margin `> 0.015`) remain true statements about these
two explicitly defined real numbers, and they are kept for the record.  They are
**not** presented as an instance of the paper's criterion, and they are no
longer conjuncts of `Zeta5.zeta5_certificate`.  Two reasons:

* the **denominator type never enters** the combination `BC + log‖ψ‖_∞`, whereas
  the published arithmetic-holonomy criterion weighs the archimedean data
  against `τ` (and the `p`-adic radius).  A comparison in which `τ = 45/16` plays
  no role cannot be that criterion;
* the **template term has the wrong scaling**: `max log‖ψ‖ ≈ −4.32` for the
  internal `ψ` only because of the normalising factor `5^{-45}`.  Rescaling `ψ`
  by a constant moves this term by an arbitrary amount while changing nothing
  arithmetically, so the sum is not invariant under the relevant
  renormalisations.

## 5a. The published template — **certified admissibility bound**

File `Zeta5/PublishedTemplate.lean`.  The draft's template

```
ψ(z) = z · exp( Σ_{k=0}^{40} c_k z^k )
```

is encoded from the 41 published decimals.  They are treated as **decimal
approximations of unknown exact rationals**: each `c_k` is stored as the exact
rational `pubC k` read off the printed nine digits, together with the explicit
rounding bound

```
|c_k − pubC k| ≤ 10⁻⁹          (Zeta5.Published.Approximates)
```

and every theorem is proved for an *arbitrary* real coefficient sequence obeying
that bound, so the rounding is propagated through the estimate (it costs at most
`41·10⁻⁹`).

| result | statement |
|---|---|
| `Zeta5.Published.re_logPsi_le` | `‖z‖ = 1 → Re Σ_k c_k z^k ≤ −0.0482` |
| `Zeta5.Published.log_norm_psi_le` | hence `log ‖ψ(z)‖ ≤ −0.0482 < 0` on the unit circle |
| `Zeta5.Published.norm_psi_lt_one` | hence `‖ψ(z)‖ ≤ exp(−0.0482) < 1` |
| `Zeta5.Published.naive_l1_bound_fails` | the naive `ℓ¹` estimate gives `+0.127… > 0`, so it proves nothing |
| `Zeta5.Published.circleAverage_log_norm_psi` | **exact energy**: the circle average of `log‖ψ‖` over `\|z\| = 1` is exactly the constant term `c₀` |
| `Zeta5.Published.circleAverage_log_norm_psi_approx` | hence it is `−0.531289158` to within the rounding bound `10⁻⁹` |

The proof is exact rational arithmetic.  The plain triangle inequality on all 41
terms fails (last row above), so the head is treated exactly: on the unit circle
`Re z² = 2(Re z)² − 1`, and the resulting quadratic in `u = Re z` is maximised in
closed form (`head_quadratic_le`, maximum `0.1773600… < 0.17737`); the remaining
38 terms are bounded by their `ℓ¹`-norm `0.305637701` (`tail_abs_sum`).  Adding
`c₀ = −0.531289158` gives `−0.04828…`, and `−0.0482` is the stated bound.

The *energy* of the published template is obtained from the same Jensen
abstraction as `BC(φ)` in §2: writing `ψ(z) = z·exp(g(z))`, the factor `exp∘g` is
entire and zero-free, so the circle average of `log‖exp∘g‖` is its value at the
centre; and on the unit circle `log‖ψ‖ = log‖exp∘g‖` because `log‖z‖ = 0` there.
So the average is exactly `g(0) = c₀ = −0.531289158` (within `10⁻⁹`), with no
quadrature error.

**Limits of this item.**  This is an admissibility bound for `ψ` alone.  The
composition with the Hauptmodul is treated in §5b.

## 5b. The Hauptmodul composition `φ = t ∘ ψ`, and its exact Bost–Charles integral

Files `Zeta5/Hauptmodul.lean`, `Zeta5/HauptmodulBC.lean`, `Zeta5/EtaQuotient.lean`.

### The Hauptmodul, as a product

The Hauptmodul of `X₀(5)` is the eta quotient

```
t = (η(τ)/η(5τ))^6 = q⁻¹ ∏_{n ≥ 1} (1 − qⁿ)^6 / (1 − q^{5n})^6 ,   q = e^{2πiτ}.
```

It is treated here as a function of the nome `q` on the punctured unit disc, and
throughout via the **product**, never via the `q`-expansion `Σ aₙ qⁿ`.

| result | statement |
|---|---|
| `Zeta5.Hauptmodul.abs_log_norm_one_sub_le` | `‖w‖ ≤ ρ < 1 → \|log‖1 − w‖\| ≤ ρ/(1 − ρ)` |
| `Zeta5.Hauptmodul.summable_etaFactorLog` | absolute convergence of `Σₙ (6 log‖1 − q^{n+1}‖ − 6 log‖1 − q^{5(n+1)}‖)` for `‖q‖ ≤ ρ < 1`, with the summable majorant `12 ρ^{n+1}/(1 − ρ)` |
| `Zeta5.Hauptmodul.hasProd_etaFactor` | the product converges: it is `exp` of the summed complex logarithms |
| `Zeta5.Hauptmodul.log_norm_hauptmodul` | `0 < ‖q‖ < 1 → log‖t(q)‖ = hauptLog q`, the logarithmic series |
| `Zeta5.Hauptmodul.etaQuotient_eq_hauptmodul` | `(η(τ)/η(5τ))^6 = t(e^{2πiτ})` on the upper half plane (Mathlib has no `η`, so it is defined by its product expansion) |

### The composition is well defined

`Zeta5/PublishedTemplate.lean` gives `log‖ψ‖ ≤ −0.147` on the unit circle.  Since
`ψ(z) = z·exp(Σ_{k ≤ 40} c_k z^k)` is entire, the maximum modulus principle
extends this to the **whole closed disc**:

```
‖z‖ ≤ 1 → ‖ψ(z)‖ ≤ psiRadius = 0.864 < 1       (Zeta5.Hauptmodul.norm_psi_le_psiRadius)
ψ(0) = 0                                        (Zeta5.Hauptmodul.psi_zero)
```

(`exp(−0.147) ≤ 0.864` is proved from four terms of the exponential series.)

**How the `0.147` is certified (§5a′).**  The first version of this bound
(`re_logPsi_le`) treated the head `k = 0, 1, 2` of `Σ_k c_k z^k` exactly and the
remaining 38 coefficients by their `ℓ¹`-norm, giving `−0.0482` and the radius
`0.953`.  The *same* head-exact / tail-`ℓ¹` method with the exact head extended
to `k ≤ 20` gives `−0.147` and the radius `0.864` (`re_logPsi_le_sharp`,
`norm_psi_le_864`).  The new ingredient is how the longer head is bounded.  On
the unit circle `Re(z^k) = T_k(Re z)`, the Chebyshev polynomial — proved from
the three-term recurrence `Re(z^{n+2}) = 2 Re z · Re(z^{n+1}) − Re(z^n)`
(`re_pow_rec`) — so the head is a degree-`20` polynomial `P(u)` in `u = Re z`,
and one needs `P ≤ M'` on `[-1,1]`.  That is certified by an explicit
sum-of-squares identity of Fejér–Riesz type,

```
M' − P(u) = A(u)² + (1 − u²)·B(u)² + D(u)          (Zeta5.Published.sos_identity)
```

with `A`, `B` explicit integer polynomials and a residual `D` whose constant
term exceeds the `ℓ¹`-norm of its remaining coefficients, so `D ≥ 0` on
`[-1,1]` (`sosD_nonneg`).  The identity is checked by `ring` in exact integer
arithmetic; floating point enters only in the *search* for `A` and `B`
(spectral factorisation, `scripts/zeta5/psi_sup_certificate.py`), which the
script also re-verifies exactly.  The limit of the method, with the exact head
extended to all 41 coefficients, is the true maximum `≈ 0.836`; `0.864` is what
degree `20` yields, and each further pair of coefficients buys only about
`0.002`.
So `φ = t ∘ ψ` is defined on the punctured closed disc, with

```
log‖φ(z)‖ = logPhi z = −log‖ψ(z)‖ + Σ_{n ≥ 1} (6 log‖1 − ψ(z)ⁿ‖ − 6 log‖1 − ψ(z)^{5n}‖).
```

### The integral, exactly

Each factor `1 − ψⁿ` is holomorphic and zero-free on a neighbourhood of the
closed disc and equals `1` at the origin, so Jensen's formula (the same
abstraction as §2) gives circle average `0` for each `log‖1 − ψⁿ‖`
(`circleAverage_log_norm_one_sub_psi_pow`).  The series is dominated along the
circle by the summable majorant at `ρ = psiRadius`, so it may be integrated term
by term (`intervalIntegral_tsum_etaFactorLog`, via dominated convergence).  What
remains is the circle average of `−log‖ψ‖`, which by §5a is exactly `−c₀`:

| result | statement |
|---|---|
| `Zeta5.Hauptmodul.circleAverage_logPhi` | `BC(φ) = −c₀` **exactly** |
| `Zeta5.Hauptmodul.BC_phi_eq` | `0.53128915 < BC(φ) < 0.53128917` (rounding of the printed decimals propagated) |
| `Zeta5.Hauptmodul.circleAverage_logPhiPub` | with the printed decimals read as exact rationals, `BC(φ) = 0.531289158` |
| `Zeta5.Hauptmodul.BC_phi_inv_eq` | for the reciprocal normalisation, `BC(1/φ) = +c₀ ∈ (−0.53128917, −0.53128915)` |

There is no quadrature and no coefficient estimate of a `q`-expansion anywhere in
this evaluation.  An independent numerical quadrature gives `0.531289157999993`,
in agreement.

### The identification: Jensen mean vs. pairwise energy (resolves the discrepancy)

File `Zeta5/BostCharlesEnergy.lean`.

The discrepancy recorded below is a **confusion of two different functionals**,
not a defect of the numbers.  Precisely:

1. **The quantity computed above is the Jensen mean.**  Everything in this
   section (`circleAverage_logPhi`, `BC_phi_eq`, `circleAverage_logPhiPub`)
   evaluates the single circle average
   ```
   (1/2π) ∫₀^{2π} log‖φ(e^{iθ})‖ dθ = −c₀ = 0.531289158… ,
   ```
   i.e. the Jensen mean of `log‖φ‖`.  This is exact and unconditional.

2. **The draft's `BC(φ)` is the pairwise energy.**  It is the *double* integral
   of the logarithmic distance between boundary values,
   ```
   BC(φ) = (1/4π²) ∫₀^{2π} ∫₀^{2π} log‖φ(e^{iθ}) − φ(e^{iψ})‖ dψ dθ ,
   ```
   formalised as `Zeta5.Hauptmodul.pairwiseEnergy`.  It is **not** the Jensen
   mean, and no evaluation of it is claimed here.  The draft's numerical value
   is `1.0355`; see the next subsection for *which* normalisation of `φ` that
   value belongs to.

3. **The cost is the pairwise energy corrected by the Jensen data:**
   ```
   cost(φ) = BC(φ) − 4 c₀           (Zeta5.Hauptmodul.paperCost)
   ```
   with `c₀ = a 0` the constant coefficient of `log(ψ(z)/z)`; equivalently
   `cost(φ) = BC(φ) + 4 · (Jensen mean of log‖φ‖)`
   (`paperCost_eq_add_jensenMean`), since that mean is `−c₀`.  The correction is
   certified: `2.12515 < −4c₀ < 2.12516` (`four_c_zero_enclosure`).

4. **The budget is**
   ```
   budget = 3 (3 log 5 − 4 + 1/4) = 9 log 5 − 45/4      (Zeta5.Hauptmodul.paperBudget)
   ```
   with the certified enclosure `3.2346 < budget < 3.2355` (`paperBudget_gt`,
   `paperBudget_lt`), obtained from the `log 5` bounds of §1.  In particular the
   externally quoted number `3.23494` is simply this expression to five decimals
   (`abs_paperBudget_sub_quoted_lt`): it is no longer an unexplained input.

5. **This identification explains the `0.5313` vs. `3.23494` gap with no fudge
   factor.**  `0.5313` is the Jensen mean, a *summand-level* quantity; the number
   to be compared with the budget is `cost = BC(φ) − 4c₀`, and with the draft's
   `BC ≈ 1.0355` and the certified `−4c₀ ≈ 2.1252` this is `≈ 3.1607`, of the
   same size as `budget ≈ 3.2349`.  Nothing is rescaled, and no factor is
   inserted by hand; the earlier gap came from comparing the Jensen mean with a
   budget meant for the cost.

### Which normalisation the draft's `1.0355` refers to

Unlike the Jensen mean, the pairwise energy is **not** merely negated when `φ` is
replaced by `1/φ`.  From `log‖A⁻¹ − B⁻¹‖ = log‖A − B‖ − log‖A‖ − log‖B‖` one
gets the exact relation (proved in `Zeta5.Hauptmodul.pairwiseEnergy_inv`, with
the integrability of the two pieces carried as explicit hypotheses)

```
BC(1/F) = BC(F) − 2 · (Jensen mean of log‖F‖) ,
```

hence for the Hauptmodul composition (`pairwiseEnergy_phi_inv`)

```
BC((1/t) ∘ ψ) = BC(t ∘ ψ) + 2c₀ = BC(t ∘ ψ) − 1.06257… .
```

An **uncertified** quadrature (exploratory only; see `scripts/zeta5/bc_energy.py`)
gives `BC(t ∘ ψ) ≈ 2.0981`, so `BC((1/t) ∘ ψ) ≈ 1.0355`, which is exactly the
value printed in the draft.  So the draft's `φ` is the **reciprocal**
normalisation `(η(5τ)/η(τ))^6 ∘ ψ`, and the corresponding cost is
`Zeta5.Hauptmodul.paperCostInv`, with
`paperCostInv a = paperCost a + 2c₀` (`paperCostInv_eq`) and numerically
`≈ 1.0355 + 2.1252 = 3.1607`.  **These two numerical values are quadrature only
and are not proved.**

### First steps towards a certified enclosure

Two pieces of the route (holomorphy + divided difference + maximum modulus) are
in place:

| result | statement |
|---|---|
| `Zeta5.Hauptmodul.pairwiseEnergy_id` | `BC(id) = 0`, i.e. `(1/4π²)∫∫ log‖e^{iθ} − e^{iψ}‖ = 0`: the diagonal singularity carries no mass, so `φ(z) − φ(w) = (z − w)·φ[z,w]` may be used to remove it |
| `Zeta5.Hauptmodul.pairwiseEnergy_le_of_le` | a uniform bound on `log‖φ(e^{iθ}) − φ(e^{iψ})‖` bounds `BC(φ)` |

What is still missing is the quantitative input: a certified sup-norm bound for
the divided difference of `φ` (or of `1/φ`) on the closed bidisc, sharp enough
to land near `1.0355`.  Crude bounds are far too lossy, and no such bound is
proved here.  §5c below measures exactly *how* lossy, and concludes that
sup-norm and moderate-`p` moment bounds do not usefully reach `1.109`.

**What is still not claimed.**  Neither `pairwiseEnergy (phi a)` nor
`pairwiseEnergy (1/phi a)` is evaluated or bounded anywhere in `Zeta5/`, so
**no `cost < budget` claim is made**: `1.0355` (and `2.0981`) are numerical
targets, and a floating-point quadrature is not a proof.  The lemmas
`paperCost_lt_paperBudget_of_energy_bound` and
`paperCostInv_lt_paperBudget_of_energy_bound` record the implication that
*would* close the argument once a certified upper bound `B` with
`B + 2.12516 ≤ 3.2346` exists; their hypothesis is left open.
The conjuncts of `Zeta5.zeta5_certificate` are untouched by this module, and
nothing here bears on `ζ_5(3) ∉ ℚ`.

### 5c. How lossy is a supremum bound?  (`Zeta5/EnergyBounds.lean`)

The live target is the **reciprocal** normalisation: the budget comparison
`paperCostInv_lt_paperBudget_of_energy_bound` needs a certified
`BC((1/t) ∘ ψ) ≤ 1.10944`, and (uncertified) quadrature puts the true value at
`≈ 1.0355`, i.e. about `7 %` of headroom.  Writing `F = (1/t) ∘ ψ` and
`F(z) − F(w) = (z − w)·g(z, w)`, `pairwiseEnergy_id` gives
`BC(F) = (1/4π²)∬ log‖g‖` (`pairwiseEnergy_eq_of_factor`), so any uniform
majorant `M ≥ sup‖g‖` yields `BC(F) ≤ log M`; and, more cheaply, any majorant
`M_F ≥ sup_{|z|=1}‖F‖` yields `BC(F) ≤ log 2 + log M_F`.

**The certified crude majorant.**  `log‖1/t(q)‖ = log‖q‖ − Σₙ etaFactorLog q n`
and `|Σₙ etaFactorLog q n| ≤ Σₙ etaBound ρ n = 12ρ/(1−ρ)²`
(`tsum_etaBound`, `log_norm_hauptmodul_inv_le`).  At the certified template
radius `ρ = psiRadius` this gives `log‖F(z)‖ ≤ 5177` on the punctured closed disc
(`log_norm_phi_inv_le_crude`), hence, unconditionally,

> `Zeta5.Hauptmodul.pairwiseEnergy_phi_inv_le_crude` : `BC((1/t) ∘ ψ) ≤ 5178`.

So the crude certified `log M ≈ 5.18·10³`, against a target of `1.109`: **three
orders of magnitude off**, not a factor of two.

**The loss is structural, not an artefact of this particular majorant.**  The
bound `∏‖1 − qⁿ‖^{-6} ≤ ∏(1 − ρⁿ)^{-6}` is attained only when every power `qⁿ`
is positive real, which never happens along the image of `ψ`.  Sharpening it to
the exact product at `ρ = 0.953` (the radius certified when this measurement
was made; it is now `0.864`) still gives `log M ≈ 2.1·10²`, and even
pretending the certified radius could be pushed down to the true
`max‖ψ‖ ≈ 0.836` only gives `log M ≈ 48`.  More decisively, the *exact* suprema
are themselves far above the mean — numerically (see `scripts/zeta5/bc_sup.py`;
not a proof):

| quantity (N = 512 quadrature, **not certified**) | value | resulting bound on `BC` |
|---|---|---|
| `mean log‖g‖ = BC((1/t)∘ψ)` | `1.0356` | — (the true value) |
| `max_{\|z\|=1}‖F‖` | `52.4` | `log sup‖F(z)−F(w)‖ ≈ 3.96` |
| `max_{𝕋²}‖g‖ = max\|F'\|` | `1.47·10³` | `log sup‖g‖ ≈ 7.29` |
| `(1/p) log mean‖g‖^p`, `p = 2` (Parseval: `mean‖g‖² = Σ n\|fₙ\|²`) | — | `4.35` |
| `p = 1` / `p = 1/2` / `p = 1/4` | — | `3.45` / `2.65` / `1.98` |

Every entry exceeds the threshold `1.10944` by a factor of `1.8` to `6.6`.

> **Sup-norm and moderate-`p` moment bounds do not usefully reach `1.109`.**
> The family `M(p) = (1/p) log E|ΔF|^p` decreases to `BC` as `p → 0`, and
> already clears `1.109` near `p ≈ 0.015`.  At that point the integrand is
> nearly `1`, so certifying the moment is as hard as certifying the mean.  The
> obstruction is quantitative, not structural.

*The crossing, recorded so that the claim is falsifiable.*  Writing
`g(z,w) = (F(z) − F(w))/(z − w)` and `M(p) = (1/p) log E|g|^p`, Jensen gives
`BC(F) ≤ M(p)` for every `p > 0`, with `M` increasing and `M(p) → BC(F)` as
`p → 0+`.  Measured on a uniform `N × N` grid (`scripts/zeta5/bc_moment_crossing.py`;
floating point, **not a proof**):

| `p` | `2` | `1` | `1/2` | `1/4` | `0.1` | `0.05` | `0.03` | `0.02` | `0.015` | `0.01` |
|---|---|---|---|---|---|---|---|---|---|---|
| `M(p)` | `4.3513` | `3.4516` | `2.6509` | `1.9755` | `1.4381` | `1.2400` | `1.1588` | `1.1179` | `1.0974` | `1.0768` |

so the crossing `M(p*) = 1.10944` sits at `p* ≈ 0.0179` (`0.01787` at `N = 256`,
`0.01793` at `N = 512`), i.e. `p ≈ 0.015`–`0.02`.  At such `p` one has
`|g|^p ∈ (0.9, 1.15)` over essentially the whole torus, so the quantity being
certified, `E|g|^p = 1 + p·BC + O(p²)`, has to be pinned to relative accuracy
`≈ p·0.07 ≈ 10⁻³`: certifying the moment is exactly as hard as certifying the
mean.  The obstruction is therefore quantitative, not structural.

A similar remark applies to the sharpest estimate
that uses only the *image curve* `K = F(∂D)`: `BC(F)` is the logarithmic energy
of the push-forward measure `μ = F_*(uniform)`, which the equilibrium measure
maximises, so `BC(F) ≤ log cap(K)` — but `K` is a continuum of diameter
`≥ 52.3`, so `cap(K) ≥ diam(K)/4 ≥ 13` and that bound is already `≥ 2.57`.

Reaching `1.109` therefore requires evaluating the mean itself — a certified quadrature of a two-dimensional, logarithmically
singular integral to an absolute accuracy of about `0.07`.  That is not
attempted here.

**Consequently no `cost < budget` inequality is asserted.**  The hypothesis of
`paperCostInv_lt_paperBudget_of_energy_bound` remains open, and
`paperCost_lt_paperBudget_of_energy_bound` (the non-reciprocal variant) is a
dead branch in any case: its numerical hypothesis `B ≤ 1.109` is false for
`BC(t ∘ ψ) ≈ 2.098`.  Nothing here bears on `ζ_5(3) ∉ ℚ`.

### 5d. The regular integrand `g` after splitting the singularity (`Zeta5/DividedDifference.lean`)

Since a certified quadrature of the mean is what a `cost < budget` claim would
require (§5c), the next self-contained step is to make the integrand of that
quadrature usable.  Writing `F = (1/t) ∘ ψ` and
`g(z,w) = (F(z) − F(w))/(z − w)`, `pairwiseEnergy_eq_of_factor` reduces `BC(F)`
to `(1/4π²)∬ log‖g‖`, whose integrand is regular off the diagonal.  This module
supplies `g` and the properties of it that need no quadrature.

* **A formula for `x = 1/t` regular at the origin.**  `hauptmodulInv q
  = q·exp(−Σₙ etaFactorCLog q n)` agrees with `(t(q))⁻¹` on the punctured unit
  disc (`hauptmodulInv_eq_inv_hauptmodul`) and vanishes at `q = 0`, so
  `F = x ∘ ψ` is defined on the whole closed disc and equals `(φ a)⁻¹` there
  (`Fmap_eq_phi_inv`).
* **Explicit moduli of continuity, in three steps.**  The exponent of the eta
  quotient is Lipschitz on `‖q‖ ≤ ρ` with constant `36/(1−ρ)³`
  (`norm_tsum_etaFactorCLog_sub_le`, from `‖log(1−u) − log(1−v)‖ ≤ ‖u−v‖/(1−ρ)`
  and `‖qᵐ − q'ᵐ‖ ≤ m ρ^{m−1}‖q−q'‖`); hence `x` is Lipschitz on that disc
  (`norm_hauptmodulInv_sub_le`); and the published template is `40`-Lipschitz on
  the closed unit disc (`norm_psi_sub_le`, from the `ℓ¹` bounds
  `Σ|c_k| ≤ 1.19`, `Σ k|c_k| ≤ 4.36` with the `10⁻⁹` rounding included).
  Composing at the certified radius `ρ = psiRadius` (`0.953` when this bound
  was recorded, now `0.864`):

  > `Zeta5.Hauptmodul.norm_Fmap_sub_le` : `‖F(z) − F(w)‖ ≤ exp 5200 · ‖z − w‖`
  > on the closed unit disc.

* **Consequences for `g`.**  Because a divided difference of a Lipschitz
  function is bounded by its Lipschitz constant, `g` is bounded on the *whole*
  closed bidisc — no diagonal strip has to be removed
  (`norm_gPhiInv_le`, `norm_gPhiInv_circleMap_le`: `‖g‖ ≤ exp 5200`); it is
  continuous off the diagonal (`continuousOn_gPhiInv_offDiag`); and it satisfies
  the explicit off-strip estimate

  > `Zeta5.Hauptmodul.norm_gPhiInv_sub_le` : if `‖z − w‖ ≥ d` and `‖z' − w‖ ≥ d`
  > with `d > 0`, then
  > `‖g(z,w) − g(z',w)‖ ≤ exp 5200 · (1/d + 2/d²) · ‖z − z'‖`,

  which in angles reads `d = 2 sin(δ/2)` on the strip `δ ≤ |θ − ψ| ≤ 2π − δ`
  (`norm_circleMap_sub_circleMap`, `norm_circleMap_sub_circleMap_ge`,
  `norm_gPhiInv_circleMap_sub_le`).  `g` is symmetric (`gPhiInv_symm`), so the
  same estimate holds in the other variable.

**The constants are crude, and deliberately so.**  They all descend from the
majorant of §5c, `log‖F‖ ≤ 5178`, which is attained only at a positive real
nome; the true `max‖g‖` is `≈ 1.5·10³` (uncertified quadrature).  What is proved
here is the *structure* a later graded-grid quadrature needs — finiteness of
`‖g‖` everywhere, continuity off the diagonal and a Lipschitz remainder with an
explicit constant — not a sharp constant.  Holomorphic extension of `g` across
the diagonal is not proved, and **no cell of the integral is evaluated**: no
enclosure of `(1/4π²)∬_R log‖g‖` is claimed for any rectangle `R`, and nothing
here bears on `cost < budget` or on `ζ_5(3) ∉ ℚ`.

*Why one certified cell was not attempted here.*  A Lipschitz-remainder
enclosure of `∬_R log‖g‖` over a single rectangle costs
`(diameter of the cell) × (Lipschitz constant)` in width, so with the constant
proved above, `exp 5200`, the enclosure of any cell of usable size is vacuous.
Two ingredients are missing before a per-cell cost can honestly be measured:
(i) a certified *sharp* bound on the eta product along the image of `ψ` — the
present majorant ignores the phases and loses three orders of magnitude (§5c);
and (ii) certified evaluation of `F` at grid points, i.e. a truncation of the
infinite product with a certified tail.  Both are quantitative tasks of their
own, and neither is started here.

### The normalisation discrepancy — a diagnostic, not a fudge

*(Superseded by the identification above, which explains it; kept as a record.)*

* the earlier **placeholder** `φ(z) = (5 − z)²` (§2) gives `BC = 2 log 5 ≈ 3.2189`,
  which is close to the quoted budget `3.23494`;
* the **genuine** Hauptmodul composition gives `BC ≈ ±0.5313` (`+` for `t ∘ ψ`,
  `−` for `(1/t) ∘ ψ`), which is *not* close to that budget.

This is recorded as a diagnostic.  Possible explanations, none of them verified
here: the draft's `x` may carry a power-of-`5` factor; the cost functional may
have terms beyond `BC(φ)`; or the budget may be normalised differently.  **No
fudge factor is introduced, and no `cost < budget` claim is reinstated.**

Two further caveats.  No usable sup-norm bound for `log‖φ‖` on the circle is
proved (the naive `1 − ‖q‖ⁿ` bound is badly lossy), and nothing here bears on
`ζ_5(3) ∉ ℚ`.

`Zeta5.zeta5_certificate` bundles the five established ingredients (§§1–4 and the
evaluated integral of this section) into a single theorem whose only hypothesis
is `ChebyshevPNT`.  The fifth conjunct is an *evaluated integral about `φ` only*,
not a comparison.

## 6. Summary: what is rigorous, and what is external

| ingredient | status |
|---|---|
| internal template `ψ` admissible, `max_{\|z\|=1} log\|ψ\| < -4 < 0`, maximum computed exactly | **rigorous, unconditional** |
| `BC(φ) = log 25` (Jensen; `φ(z) = (5−z)²` zero-free in the closed disc, proved) | **rigorous, unconditional** |
| `3.2188 < BC(φ) < 3.219` (validated numerics for `log 5`) | **rigorous, unconditional** |
| `R₅ = 5³` for the coefficient sequence | **rigorous, unconditional** |
| `τ(b) = 45/16` | **rigorous given `ChebyshevPNT`** (an explicit hypothesis, not an axiom) |
| published 41-coefficient template: `max_{\|z\|=1} log‖ψ‖ ≤ −0.0482 < 0`, rounding `10⁻⁹` propagated | **rigorous, unconditional** (given the stated rounding bound on the printed decimals) |
| published template: circle average of `log‖ψ‖` is exactly `c₀` | **rigorous, unconditional** (Jensen, no quadrature) |
| `archCostGuess < 3.23494` (margin `> 4`), `BC(φ) < 3.23494` (margin `> 0.015`) | **true statements about the defined numbers, but demoted**: not the published criterion, and not part of `zeta5_certificate` |
| the number `3.23494` | **derived** in §5b as `3(3 log 5 − 4 + 1/4)` (previously quoted as an external input) |
| `log lcm(1,…,n) ∼ n` (PNT) | **external certificate** (explicit hypothesis) |
| Hauptmodul as a convergent product; `(η(τ)/η(5τ))^6 = t(q)`; `‖ψ‖ ≤ 0.864` on the closed disc (maximum modulus, from the head-exact / tail-`ℓ¹` bound with a degree-`20` exact head and a Fejér–Riesz sum-of-squares certificate; previously `0.9530`) | **rigorous, unconditional** |
| `BC(t ∘ ψ) = −c₀`, i.e. `0.53128915 < BC(φ) < 0.53128917`; `BC((1/t) ∘ ψ) = +c₀` | **rigorous, unconditional** (Jensen + term-by-term integration; no quadrature) |
| the normalisation discrepancy: genuine `BC(φ) ≈ ±0.5313` vs. placeholder `2 log 5 ≈ 3.2189` vs. quoted budget `3.23494` | **explained** (§5b, identification): `0.5313` is the *Jensen mean*, the budget is for `cost = BC(φ) − 4c₀` with `BC` the *pairwise energy*; no fudge factor |
| `budget = 3(3 log 5 − 4 + 1/4) = 9 log 5 − 45/4 ∈ (3.2346, 3.2355)`, i.e. the quoted `3.23494` | **rigorous, unconditional** (the quoted number is now derived, not external) |
| `cost(φ) = BC(φ) − 4c₀`, with `2.12515 < −4c₀ < 2.12516` | **definition + rigorous enclosure of the correction term** |
| `BC(1/F) = BC(F) − 2·(Jensen mean)`, hence `BC((1/t)∘ψ) = BC(t∘ψ) + 2c₀` | **rigorous**, under explicit integrability hypotheses |
| the pairwise energies themselves (quadrature: `BC(t∘ψ) ≈ 2.0981`, `BC((1/t)∘ψ) ≈ 1.0355`, the draft's value) | **not evaluated**; quadrature only, no `cost < budget` claim |
| `BC(F) = (1/4π²)∬ log‖g‖` for a divided-difference factorisation `F(z)−F(w) = (z−w)g(z,w)` | **rigorous**, under explicit integrability hypotheses |
| `BC((1/t) ∘ ψ) ≤ 5178` (crude certified majorant, §5c) | **rigorous, unconditional** — but three orders of magnitude above the `1.10944` needed |
| any sup-norm or moderate-`p` moment route to `BC((1/t)∘ψ) ≤ 1.10944` | **not useful** (§5c): the exact suprema give `3.96` / `7.29` and the Jensen `L^p` means `4.35` / `3.45` / `2.65` / `1.98`; the family only clears `1.109` near `p ≈ 0.015`, where certifying the moment is as hard as certifying the mean |
| `F = (1/t)∘ψ` Lipschitz on the closed unit disc with constant `exp 5200`; `g = (F(z)−F(w))/(z−w)` bounded by `exp 5200` on the closed bidisc, continuous off the diagonal, with the off-strip estimate `‖g(z,w) − g(z',w)‖ ≤ exp 5200·(1/d + 2/d²)‖z−z'‖` (§5d) | **rigorous, unconditional** — constants crude, not sharp |
| any certified enclosure of `∬_R log‖g‖` over a rectangle, and any covering of the torus | **not attempted, not claimed** |
| any cost functional for the published template, and any `cost < budget` claim | **not formalised, not claimed** |
| arithmetic holonomicity theorem, and the deduction `ζ_5(3) ∉ ℚ` | **external, not formalised**; no such claim is made anywhere in `Zeta5/` |

## 7. Reproducing

```
lake build Zeta5.Certificate         # the certificate
lake build Zeta5.PublishedTemplate   # the published-template admissibility bound
lake build Zeta5.Hauptmodul          # the Hauptmodul product and the composition
lake build Zeta5.HauptmodulBC        # the exact Bost–Charles integral of φ = t ∘ ψ
lake build Zeta5.EtaQuotient         # t = (η(τ)/η(5τ))^6
lake build Zeta5.BostCharlesEnergy   # the paper's BC / cost / budget functionals
lake build Zeta5.EnergyBounds        # the crude certified energy bound (§5c)
lake build Zeta5.DividedDifference   # the regular integrand g and its bounds (§5d)
lake build Zeta5.AxiomAudit       # + the axiom audit (prints the axiom lists)
rg -n "sorry" Zeta5/              # no occurrences (outside doc comments)
python3 scripts/zeta5/template_data.py   # regenerates the 41 coefficients and the
                                         # exact inequality Σ|numerators| < 5^45
python3 scripts/zeta5/bc_sup.py          # exploratory only (NOT a proof): the suprema
                                         # and L^p means of §5c
python3 scripts/zeta5/bc_moment_crossing.py  # the L^p crossing p* ~ 0.0179 (§5c)
```
