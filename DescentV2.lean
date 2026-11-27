/-
  DescentV2.lean — the 26D descent's analytic endpoint, restated so that it can be finished. 27 November 2026 · Dula.

  STATUS: statements only, not compiled (no Lean here). Target: Lean v4.35.0 with the Mathlib commit pinned by
  lsernau/grh-lean (56a00585…), so that `riemannHypothesis : RiemannHypothesis` can be imported.

  Why a V2 (details in README.md in this folder):
   * The archive's `WeilDistribution` (Main_aristotle/Main.lean) is not Weil's functional. On g⋆g with
     g(x) = exp(−x²/2) it equals −0.887 (and −47.03 for exp(−x²/8)), while Weil's functional, the sum over the
     zeros, is positive. So `WeilPositivity` there is false, and `WeilCriterion` (WeilPositivity ↔ RH) is a false
     statement once RH is known. Its `sorry` can never be filled, and every theorem using it is unsound.
   * The archive's `spectral_strand_nonneg` is false (−10.15 at g = φ(x−16)+φ(x+16)−2φ(x), φ = exp(−x²/9)).
   * `Conjecture_A_Weak`, `Conjecture_A_Strong` are provable with Φ := 0 (the strong form never uses its g), and
     `Conjecture_A'` is equivalent to WeilPositivity. None of them carries descent content. With RH imported,
     `conjecture_a_strong_implies_rh` and `offcritical_zero_breaks_positivity` close vacuously.

  What V2 does:
   1. Weil's test class: even, smooth, compactly supported (needed: the polar term is ∫ g(x) e^{±x/2} dx, which
      diverges for some Schwartz functions).
   2. `weilW`: the Guinand–Weil functional in the Iwaniec–Kowalski normalisation. The identity
      Σ_ρ h(γ_ρ) = weilW g was checked numerically to 1e−32 (explicit_formula_check.log).
   3. `explicit_formula` is the one hard target (classical, Weil 1952). From it, `weil_positive_of_RH` follows,
      and with the imported RH it becomes the unconditional `weil_positive`. That is the descent's endpoint
      (Weil positivity, for every test function, including any family projected from Cohn–Elkies functions),
      now a theorem relative to the imported proof.
   4. Conjecture A is restated as what it really is: a harmonic-analysis question about dilates, independent of RH.
-/
import Mathlib
-- import GRH.Main   -- lsernau/grh-lean: provides `riemannHypothesis : RiemannHypothesis` (module name to check)

open Real Complex MeasureTheory Set Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace DescentV2

/-! ### 1. Weil's test functions -/

/-- Even, smooth, compactly supported real test functions. -/
structure TestFn where
  g : ℝ → ℝ
  smooth : ContDiff ℝ ⊤ g
  compact : HasCompactSupport g
  even : ∀ x, g (-x) = g x

/-- `h(z) = ∫ g(x) e^{ixz} dx`, entire in `z` for compactly supported `g`. -/
def fourierExt (g : ℝ → ℝ) (z : ℂ) : ℂ := ∫ x : ℝ, (g x : ℂ) * Complex.exp (I * (x : ℂ) * z)

/-- The digamma function `ψ = Γ'/Γ`. -/
def psi (z : ℂ) : ℂ := deriv Complex.Gamma z / Complex.Gamma z

/-- The autocorrelation `(φ ⋆ φ)(x) = ∫ φ(t) φ(t + x) dt` (for even real `φ` this is `φ ⋆ φ*`). -/
def autoFun (φ : TestFn) : ℝ → ℝ := fun x => ∫ t : ℝ, φ.g t * φ.g (t + x)

theorem autoFun_smooth (φ : TestFn) : ContDiff ℝ ⊤ (autoFun φ) := by sorry      -- convolution of C_c^∞ is C^∞
theorem autoFun_compact (φ : TestFn) : HasCompactSupport (autoFun φ) := by sorry -- support ⊆ supp φ − supp φ
theorem autoFun_even (φ : TestFn) (x : ℝ) : autoFun φ (-x) = autoFun φ x := by sorry -- shift t ↦ t + x

def auto (φ : TestFn) : TestFn := ⟨autoFun φ, autoFun_smooth φ, autoFun_compact φ, autoFun_even φ⟩

/-- For real `t`: `h_{φ⋆φ}(t) = |h_φ(t)|²` (substitute `y = t' + x`; `h_φ(−t) = conj h_φ(t)` for real `φ`). -/
theorem fourierExt_auto (φ : TestFn) (t : ℝ) :
    fourierExt (autoFun φ) t = ((Complex.normSq (fourierExt φ.g t) : ℝ) : ℂ) := by sorry

/-! ### 2. Weil's functional -/

/-- Weil's functional, Guinand–Weil explicit formula, Iwaniec–Kowalski normalisation:
`W(g) = h(i/2) + h(−i/2) − g(0) log π + (1/2π) ∫ h(t) Re ψ(1/4 + it/2) dt − 2 Σ Λ(n) n^{−1/2} g(log n)`. -/
def weilW (g : ℝ → ℝ) : ℝ :=
  (fourierExt g (I / 2) + fourierExt g (-I / 2)).re
    - g 0 * Real.log Real.pi
    + (1 / (2 * π)) * ∫ t : ℝ, (fourierExt g t).re * (psi (1 / 4 + I * (t : ℂ) / 2)).re
    - 2 * ∑' n : ℕ, Λ n / Real.sqrt n * g (Real.log n)

/-! ### 3. The explicit formula and Weil positivity -/

/-- Non-trivial zeros of `ζ`: they all lie in the strip `0 < Re s < 1`. -/
def NontrivialZero (s : ℂ) : Prop := riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- **The explicit formula** (Weil 1952; Iwaniec–Kowalski Thm 5.12). The hard target: needs the zero counting
`N(T + 1) − N(T) ≪ log T` and a contour shift for `ξ'/ξ`. Zeros are counted with multiplicity; for
`ρ = ½ + iγ`, `γ = (ρ − ½)/i`. -/
theorem explicit_formula (φ : TestFn) :
    HasSum (fun ρ : {s : ℂ // NontrivialZero s} =>
        (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * fourierExt φ.g ((ρ.1 - 1 / 2) / I))
      (weilW φ.g : ℂ) := by
  sorry

/-- RH ⟹ Weil positivity. From `explicit_formula` applied to `auto φ`: under RH every `γ` is real, so every term is
`m · |h_φ(γ)|² ≥ 0` (`fourierExt_auto`). -/
theorem weil_positive_of_RH (hRH : RiemannHypothesis) (φ : TestFn) : 0 ≤ weilW (autoFun φ) := by
  sorry

/-- The converse (Weil 1952 / Bombieri 2000), for completeness: positivity for all test functions ⟹ RH. Not needed
for the descent's endpoint once RH is imported. -/
theorem RH_of_weil_positive (h : ∀ φ : TestFn, 0 ≤ weilW (autoFun φ)) : RiemannHypothesis := by
  sorry

/-- **The descent's endpoint, unconditional relative to the imported proof.** Uncomment with the grh-lean import:

theorem weil_positive (φ : TestFn) : 0 ≤ weilW (autoFun φ) :=
  weil_positive_of_RH riemannHypothesis φ

In particular `0 ≤ weilW (autoFun (Φ f))` for every test function `Φ f` produced from a Cohn–Elkies function. -/
theorem weil_positive_family {ι : Type*} (Φ : ι → TestFn) (hRH : RiemannHypothesis) (i : ι) :
    0 ≤ weilW (autoFun (Φ i)) :=
  weil_positive_of_RH hRH (Φ i)

/-! ### 4. Conjecture A, as a question about dilates (independent of RH) -/

/-- The paper's Conjecture 5.1: no non-zero continuous linear functional on Schwartz space kills every dilate
`ξ ↦ F(λξ)`, `λ > 0`, of the Fourier profile `F` of the Leech Cohn–Elkies function. Equivalent (Hahn–Banach) to
density of the span of the dilates. With RH a theorem, this no longer bears on RH; it is a question in harmonic
analysis (a Wiener-type problem on the multiplicative group, governed by the zeros of the Mellin transform of `F`).
`dil` is the dilation operator, specified by `hdil`. -/
def ConjectureA (F : SchwartzMap ℝ ℝ)
    (dil : {x : ℝ // 0 < x} → SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ)
    (_hdil : ∀ l G x, dil l G x = G (l.1 * x)) : Prop :=
  ∀ T : SchwartzMap ℝ ℝ →L[ℝ] ℝ, (∀ l, T (dil l F) = 0) → T = 0

end DescentV2
