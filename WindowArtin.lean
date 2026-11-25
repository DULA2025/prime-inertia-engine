/-
  WindowArtin.lean — a two-sided window criterion for logarithmic-derivative Dirichlet series, and what it
  gives for an Artin L-function.  25 November 2026 · Dula.
  Goes in PieLab/ next to WindowCriterion.lean and WindowParts.lean; add `import PieLab.WindowArtin` to PieLab.lean.

  STATUS: statements only, not compiled.  Same rules as before: fix compile errors with the smallest change,
  log every statement change in CHANGES.md with the reason, and give a counterexample if a statement is false.

  Why a second criterion.  `window_criterion` (WindowCriterion.lean) is for ζ and assumes a ONE-SIDED bound
  G(x) ≤ C x^θ.  Its last step (Case B in WindowParts) needs a POSITIVE residue at a real singularity.  For
  Ψ = −L'/L the residue of Ψ(s)/(s(s−1)) at a real s₀ ∈ (0, 1) is m/(s₀(s₀ − 1)) with m = −ord_{s₀} L: positive
  at a zero of L, NEGATIVE at a pole of L.  So a one-sided bound cannot exclude a real pole.  With a two-sided
  bound ‖G(x)‖ ≤ C x^θ the positivity step is not needed, and the argument excludes zeros and poles alike.

  Setting.  `LogDerivData` packages
   * coefficients c with ‖c n‖ ≤ K Λ(n)  (for ρ: c(pᵏ) = log p · tr ρ(Frob_p^k | V^{I_p}), K = dim ρ);
   * a function Ψ with Ψ(s) = Σ c(n) n^{−s} for Re s > 1  (for ρ: Ψ = −L'/L(s, ρ));
   * an integer m(s₀)  (for ρ: m = −ord_{s₀} L(s, ρ), so m > 0 exactly at poles of L)
  such that, in Re s > 0, Ψ is analytic where m = 0 and has a simple pole of residue m(s₀) elsewhere, the
  singular set being finite in compacts.  For L(s, ρ) these fields are Brauer's induction theorem plus Hecke
  theory.  Mathlib has neither Artin L-functions nor Brauer meromorphy, and the RH archive's `continuedArtinL`
  sections are empty, so they enter as fields of the structure.

  G(x) = Σ_{n ≤ x} c(n)(x/n − 1) − Ψ(1) x, and Φ(s) = Ψ(s)/(s(s−1)) − Ψ(1)/(s−1) is its Mellin transform.
  For ρ nontrivial irreducible, Ψ(1) = −L'/L(1, ρ) is finite (L(1, ρ) ≠ 0 and no pole at 1), and Ψ(1) x is the
  main term.  (ζ is not a special case: −ζ'/ζ has a pole at 1, and WindowCriterion.lean handles it.)

  Proof outline (the WindowParts machinery, simplified):
   A  `norm_G_le`, `mellin_G`, `iteratedDeriv_Φ` (as W1: x = eᵘ, differentiate under the integral).
   B  `window_bound_two_sided`: |g| ≤ C e^{θu} on the windows and ‖g‖ ≤ C₀ eᵘ(1 + u) elsewhere, the gamma tails
      (gamma_tail_upper/lower) with k + 1 ≈ a(1 + λ)/2 · log Y, a = σ − 1 (or σ − 2 using 1 + u ≤ eᵘ):
      ‖A_k(σ + it)‖ ≤ B (σ − θ)^{−k} for all t, for infinitely many k, once σ is large.
   C  `m_eq_zero_of_one_lt`, `Φ_removable_one`, `Φ_pole`: Φ is removable at 1 and has simple poles of residue
      m(s₀)/(s₀(s₀ − 1)) ≠ 0 exactly where m ≠ 0 (Re s₀ > 0; s₀ ≠ 0, 1).
   D  `window_two_sided`: suppose m(p) ≠ 0 with Re p > θ.  Fix σ ≥ σ₀, E = σ − θ.  All poles have Re ≤ 1 < σ
      (C), and σ − Re p < E.  `Window.exists_unique_nearest` with D = E gives z₀ = σ + it with a unique nearest
      pole ρs at distance d < r < E.  On the closed disc |s − z₀| ≤ r (inside Re > θ), Φ − b/(s − ρs) extends
      analytically (removable at 1 and ρs; replace the junk values first, as in the W6 Lean note), so
      `Window.iteratedDeriv_le_of_sphere` and `Window.iteratedDeriv_simple_pole` give
      ‖A_k(z₀)‖ ≥ |b| d^{−k−1} − M r^{−k},  b = m(ρs)/(ρs(ρs − 1)) ≠ 0,
      against B E^{−k} along B's infinitely many k.  Contradiction.  No case split and no d₀ are needed,
      because the two-sided bound controls ‖A_k‖ directly.
   E  `off_line`: the functional equation moves Re s < 1/2 to Re s > 1/2.
-/
import Mathlib
import PieLab.WindowCriterion
import PieLab.WindowParts

open Complex Real MeasureTheory Set Filter Topology Metric
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace WindowArtin

/-- A logarithmic-derivative Dirichlet series with a meromorphic continuation to `Re s > 0` whose only
singularities are simple poles with integer residues `m`. -/
structure LogDerivData where
  c : ℕ → ℂ
  K : ℝ
  hc : ∀ n, ‖c n‖ ≤ K * Λ n
  Ψ : ℂ → ℂ
  hΨ : ∀ s : ℂ, 1 < s.re → Ψ s = LSeries c s
  m : ℂ → ℤ
  hm_one : m 1 = 0
  hreg : ∀ s₀ : ℂ, 0 < s₀.re → m s₀ = 0 → AnalyticAt ℂ Ψ s₀
  hpole : ∀ s₀ : ℂ, 0 < s₀.re → ∃ H : ℂ → ℂ, AnalyticAt ℂ H s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, Ψ s = (m s₀ : ℂ) / (s - s₀) + H s
  hfin : ∀ Kc : Set ℂ, IsCompact Kc → {s ∈ Kc | 0 < s.re ∧ m s ≠ 0}.Finite

namespace LogDerivData

variable (D : LogDerivData)

/-- `G(x) = Σ_{n ≤ x} c(n)(x/n − 1) − Ψ(1) x`. -/
def G (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, D.c n * ((x / n - 1 : ℝ) : ℂ) - D.Ψ 1 * x

/-- `Φ(s) = Ψ(s)/(s(s−1)) − Ψ(1)/(s−1)`, the Mellin transform of `G`. -/
def Φ (s : ℂ) : ℂ := D.Ψ s / (s * (s - 1)) - D.Ψ 1 / (s - 1)

/-- `g(u) = G(eᵘ)`. -/
def g (u : ℝ) : ℂ := D.G (Real.exp u)

/-- `A_k(z) = ∫_0^∞ uᵏ/k! · g(u) e^{−zu} du`. -/
def A (k : ℕ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), ((u ^ k / k.factorial : ℝ) : ℂ) * D.g u * Complex.exp (-z * u)

/-! ### A: size, Mellin transform, Laplace derivatives -/

/-- Chebyshev/Mertens: `Σ_{n ≤ x} Λ(n)/n ≤ log x + O(1)`. -/
theorem norm_G_le : ∃ C₀ : ℝ, ∀ x ≥ (1 : ℝ), ‖D.G x‖ ≤ C₀ * x * (1 + Real.log x) := by
  sorry

/-- As `mellin_G`: each term gives `n^{−s}/(s(s−1))`, and `∫_1^∞ x · x^{−s−1} dx = 1/(s−1)`. -/
theorem mellin_G (s : ℂ) (hs : 1 < s.re) :
    ∫ x in Ioi (1 : ℝ), D.G x * (x : ℂ) ^ (-s - 1) = D.Φ s := by
  sorry

theorem iteratedDeriv_Φ (k : ℕ) (z : ℂ) (hz : 2 < z.re) :
    iteratedDeriv k D.Φ z = (-1) ^ k * (k.factorial : ℂ) * D.A k z := by
  sorry

/-! ### B: the two-sided window bound -/

theorem window_bound_two_sided (θ lam C : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hlam : 1 < lam) (hC : 0 < C)
    (h : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Icc Y (Y ^ lam), ‖D.G x‖ ≤ C * x ^ θ) :
    ∃ σ₀ : ℝ, 2 < σ₀ ∧ ∀ σ ≥ σ₀, ∃ B : ℝ, ∃ᶠ k : ℕ in atTop, ∀ t : ℝ,
      ‖D.A k ((σ : ℂ) + t * I)‖ ≤ B * (σ - θ)⁻¹ ^ k := by
  sorry

/-! ### C: the singularities of Φ in Re s > 0 -/

/-- No poles in `Re s > 1`: there `Ψ` is the absolutely convergent `LSeries`, which is analytic. -/
theorem m_eq_zero_of_one_lt (s : ℂ) (hs : 1 < s.re) : D.m s = 0 := by
  sorry

/-- `Φ = (Ψ(s)/s − Ψ(1))/(s − 1)` near `1`, and `Ψ` is analytic at `1` (`hreg`, `hm_one`). -/
theorem Φ_removable_one : ∃ F : ℂ → ℂ, AnalyticAt ℂ F 1 ∧ ∀ᶠ s in 𝓝[≠] (1 : ℂ), F s = D.Φ s := by
  sorry

/-- At `s₀ ≠ 1` with `Re s₀ > 0`, `Φ` has a simple pole of residue `m(s₀)/(s₀(s₀−1))`
(removable when `m(s₀) = 0`). -/
theorem Φ_pole (s₀ : ℂ) (h0 : 0 < s₀.re) (h1 : s₀ ≠ 1) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H s₀ ∧ ∀ᶠ s in 𝓝[≠] s₀,
      D.Φ s = (D.m s₀ : ℂ) / (s₀ * (s₀ - 1)) / (s - s₀) + H s := by
  sorry

/-! ### D: the criterion -/

/-- **Two-sided window criterion.**  A two-sided bound on arbitrarily distant windows `[Y, Y^λ]` excludes
singularities of `Ψ`, that is zeros AND poles of `L`, to the right of `θ`. -/
theorem window_two_sided (θ lam C : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hlam : 1 < lam) (hC : 0 < C)
    (h : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Icc Y (Y ^ lam), ‖D.G x‖ ≤ C * x ^ θ) :
    ∀ s : ℂ, θ < s.re → D.m s = 0 := by
  sorry

end LogDerivData

/-! ### E: the consequence for an Artin L-function -/

/-- **Off the critical line.**  For `Ψ = −L'/L(s, ρ)`, the functional equation `Λ(s, ρ) = W Λ(1 − s, ρ̄)` and
`L(s, ρ̄) = conj L(s̄, ρ)` give `ord_s L(ρ) = ord_{1 − s̄} L(ρ)` in the strip, which is `hFE`.  A two-sided
window estimate at every exponent `1/2 + ε` then leaves no zero and no pole of `L(s, ρ)` in `Re s > 0` off
`Re s = 1/2`.  The window for `ρ̄` is not needed separately: its `G` is the complex conjugate of this one.
This says nothing ON the line, where the ghost configurations of poles/poles_note live. -/
theorem off_line (D : LogDerivData)
    (hFE : ∀ s : ℂ, 0 < s.re → s.re < 1 → D.m s = D.m (1 - (starRingEnd ℂ) s))
    (hwin : ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
      ∀ x ∈ Icc Y (Y ^ ((3 : ℝ) / 2)), ‖D.G x‖ ≤ C * x ^ ((1 : ℝ) / 2 + ε)) :
    ∀ s : ℂ, 0 < s.re → s.re ≠ 1 / 2 → D.m s = 0 := by
  sorry

end WindowArtin
