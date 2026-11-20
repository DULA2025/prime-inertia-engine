/-
  WindowCriterion.lean — a one-sided bound for a smoothed prime sum on sparse windows excludes zeros of ζ.
  20 November 2026 · Dula.

  Source: S. Allahyar, "From theta lifts to zeta zeros" (revision 2, 20 Nov 2026), Sections 2–4, the analytic
  half of L. Alpöge's announced argument.  The proof below was read line by line and is self-contained: it uses
  only the Mellin transform, a gamma-kernel tail bound, Cauchy estimates and the functional equation.
  Nothing here assumes RH or uses the arithmetic half of that argument.

  STATUS: statements only (each `sorry` is a target).  Not compiled here (this sandbox cannot install Lean or
  the Mathlib cache).

  Proof outline (lemma names below):
   1. mellin_G: for Re s > 1, ∫_1^∞ G(x) x^{-s-1} dx = −ζ'/ζ(s)/(s(s−1)) − 1/(s−1)² + (1+γ)/(s−1).  The right side
      is meromorphic in Re s > 0, holomorphic at s = 1 (the principal parts cancel), with a simple pole of
      residue h/(ρ(1−ρ)) at a zero ρ of order h in the strip; at a real zero the residue is > 0.
   2. With u = log x and g(u) = G(eᵘ): A_k(z) = (−1)^k Φ^{(k)}(z)/k! = ∫ K_k(u) g(u) e^{−itu} du,
      K_k(u) = u^k e^{−σu}/k!, for Re z = σ > 2.
   3. one_sided: since |g| + g = 2 g⁺,  |A_k(σ+it)| + A_k(σ) ≤ 2 ∫ K_k g⁺.
   4. gamma_tail: the normalised kernel a^{k+1} u^k e^{−au}/k! puts mass ≤ 2 e^{−c(k+1)} outside [U, λU] when
      k + 1 ≈ a(1+λ)U/2; so the bound on the window gives |A_k(σ+it)| + A_k(σ) ≤ B E^{−k} with E = σ − θ.
   5. a pole within distance d < E of some σ + it forces |A_k| ≥ |b| d^{−k−1} − O(r^{−k}) (Cauchy), a
      contradiction; if the nearest pole is real, its positive residue gives the same at t = 0.
   6. reflection: the functional equation moves zeros with Re < 1/2 to Re > 1/2.
-/
import Mathlib

open Complex Real MeasureTheory Set Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace Window

/-- `S(x) = Σ_{n ≤ x} Λ(n) (x/n − 1)`. -/
def S (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)

/-- `G(x) = S(x) − x log x + (1 + γ) x`. -/
def G (x : ℝ) : ℝ := S x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

/-! ### The lemmas -/

/-- Size: `|G(x)| ≤ C₀ x (1 + log² x)` for `x ≥ 1`. -/
theorem abs_G_le : ∃ C₀ : ℝ, ∀ x ≥ (1 : ℝ), |G x| ≤ C₀ * x * (1 + Real.log x ^ 2) := by
  sorry

/-- Step 1: the Mellin transform of `G`. -/
theorem mellin_G (s : ℂ) (hs : 1 < s.re) :
    ∫ x in Ioi (1 : ℝ), (G x : ℂ) * (x : ℂ) ^ (-s - 1)
      = -(deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) - 1 / (s - 1) ^ 2
          + (1 + Real.eulerMascheroniConstant) / (s - 1) := by
  sorry

/-- Step 3: the one-sided comparison (`K ≥ 0`, `g` real). -/
theorem one_sided (K g : ℝ → ℝ) (hK : ∀ u, 0 ≤ K u) (t : ℝ)
    (hint : Integrable (fun u => K u * g u) (volume.restrict (Ioi 0))) :
    ‖∫ u in Ioi (0 : ℝ), (K u * g u : ℂ) * Complex.exp (-(t * u) * Complex.I)‖
        + ∫ u in Ioi (0 : ℝ), K u * g u
      ≤ 2 * ∫ u in Ioi (0 : ℝ), K u * max (g u) 0 := by
  sorry

/-- Step 4: tails of the gamma kernel.  For `0 < r < 1` and the density of shape `n` and rate 1,
the mass below `n r` is at most `exp(−n (r − 1 − log r))`, and likewise above `n r` for `r > 1`. -/
theorem gamma_tail_upper (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 1 < r) :
    ∫ v in Ioi ((n : ℝ) * r), v ^ (n - 1) * Real.exp (-v) / (n - 1).factorial
      ≤ Real.exp (-(n : ℝ) * (r - 1 - Real.log r)) := by
  sorry

theorem gamma_tail_lower (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    ∫ v in Ioc (0 : ℝ) ((n : ℝ) * r), v ^ (n - 1) * Real.exp (-v) / (n - 1).factorial
      ≤ Real.exp (-(n : ℝ) * (r - 1 - Real.log r)) := by
  sorry

/-- Step 6: reflection of zeros in the strip. -/
theorem zero_reflect (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  sorry

/-! ### The theorems -/

/-- **Window criterion** (Allahyar, Theorem 3.1, for ζ).  A one-sided bound on arbitrarily distant windows
`[Y, Y^λ]` excludes zeros to the right of `θ`. -/
theorem window_criterion (θ lam C : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hlam : 1 < lam) (hC : 0 < C)
    (h : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Icc Y (Y ^ lam), G x ≤ C * x ^ θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  sorry

/-- **The reduction of RH** (Allahyar, Theorem 1.2).  The arithmetic window estimate implies Mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis_of_window_estimate
    (h : ∃ A ≥ (0 : ℝ), ∃ ε₀ > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ Y₀ ≥ (2 : ℝ), ∃ Y ≥ Y₀,
      ∀ x ∈ Icc Y (Y ^ ((3 : ℝ) / 2)), G x ≤ x ^ ((1 : ℝ) / 2 + A * ε)) :
    RiemannHypothesis := by
  sorry

end Window
