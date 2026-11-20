/-
  MajorArc.lean — the major-arc evaluation of the von Mangoldt exponential sum, conditional on a
  bound for twisted Chebyshev sums (the input GRH supplies).  PIE Lab circle method, 20 Nov 2026 · Dula.

  STATUS: statements only (every `sorry` is a target).  Not compiled here: this sandbox cannot install
  Lean or the Mathlib cache.  Every inequality below was checked numerically (check_majorarc.py:
  lemmas exactly for q ≤ 60, the theorem for N = 200 000, q ≤ 30; worst case 0.965 of the bound).

  This corrects the target of April 2026:
      ‖vonMangoldtExpSum x (a/q + β) − (ramanujanSum q 1 / φ q) · vonMangoldtExpSum x β‖ ≤ x ^ (1/2 + ε)
  which had a free ε, no constant and no hypothesis, and is not provable as stated (the error
  must depend on q, and the x^{1/2} saving needs GRH).  The theorem below is unconditional, with
  the GRH input isolated as the hypothesis `TwistedPsiBound`.

  Proof outline (each step a lemma below):
   1. gauss_expansion: for gcd(m, q) = 1, e(m/q) = (1/φ(q)) Σ_χ χ⁻¹(m) τ(χ).
   2. split S(a/q + β): terms with gcd(n, q) > 1 (prime powers of primes dividing q, total weight
      ≤ ω(q) log N) and the rest, which by step 1 is (1/φ(q)) Σ_χ χ⁻¹(a) τ(χ) Σ_n Λ(n) χ⁻¹(n) e(nβ).
   3. gaussSum_one: τ(1) = μ(q) (Ramanujan sum c_q(1); PieLab has the full Möbius formula).
   4. gaussSum_parseval: Σ_χ ‖τ(χ)‖² = φ(q)², so Σ_χ ‖τ(χ)‖ ≤ φ(q)^{3/2} by Cauchy–Schwarz.
   5. abel_bound: if every partial sum of c is ≤ B in norm, ‖Σ_{n≤N} c_n e(nβ)‖ ≤ B (1 + 2π|β|N).
   6. combine: the non-principal characters contribute ≤ φ(q)^{-1} · φ(q)^{3/2} · B (1 + 2π|β|N),
      and replacing the coprime sum at β by S(β) costs another ω(q) log N.
-/
import Mathlib

open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

noncomputable section

namespace PieLab.MajorArc

/-- `e t = exp(2πit)`. -/
def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- `S N α = Σ_{n=1}^{N} Λ(n) e(nα)`. -/
def S (N : ℕ) (α : ℝ) : ℂ := ∑ n ∈ Icc 1 N, (Λ n : ℂ) * e (n * α)

/-- The twisted Chebyshev sum `ψ(M, χ) = Σ_{n=1}^{M} Λ(n) χ(n)`. -/
def psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 M, (Λ n : ℂ) * χ (n : ZMod q)

/-- The Gauss sum `τ(χ) = Σ_{b mod q} χ(b) e(b/q)`, written out to avoid depending on an
additive-character API. -/
def tau {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ b : ZMod q, χ b * e ((b.val : ℝ) / q)

/-- The input GRH supplies (Davenport, ch. 20: under GRH, `B = C √N log²(qN)`): every
non-principal character mod `q` has twisted Chebyshev sums of size at most `B` up to `N`. -/
def TwistedPsiBound (q N : ℕ) (B : ℝ) : Prop :=
  ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ M ≤ N, ‖psiChi χ M‖ ≤ B

/-! ### The lemmas -/

/-- Step 1. -/
theorem gauss_expansion {q : ℕ} [NeZero q] (m : ℕ) (hm : Nat.Coprime m q) :
    e ((m : ℝ) / q) = (1 / (Nat.totient q : ℂ)) * ∑ χ : DirichletCharacter ℂ q, χ⁻¹ (m : ZMod q) * tau χ := by
  sorry

/-- Step 3: the Gauss sum of the principal character is the Ramanujan sum `c_q(1) = μ(q)`. -/
theorem tau_one {q : ℕ} [NeZero q] : tau (1 : DirichletCharacter ℂ q) = (μ q : ℂ) := by
  sorry

/-- Step 4: Parseval for Gauss sums. -/
theorem tau_parseval {q : ℕ} [NeZero q] :
    ∑ χ : DirichletCharacter ℂ q, ‖tau χ‖ ^ 2 = (Nat.totient q : ℝ) ^ 2 := by
  sorry

/-- Step 4, consequence used: `Σ_χ ‖τ(χ)‖ ≤ φ(q)^{3/2}`. -/
theorem sum_norm_tau_le {q : ℕ} [NeZero q] :
    ∑ χ : DirichletCharacter ℂ q, ‖tau χ‖ ≤ (Nat.totient q : ℝ) * Real.sqrt (Nat.totient q) := by
  sorry

/-- Step 5: Abel summation against `e(nβ)`. -/
theorem abel_bound (N : ℕ) (c : ℕ → ℂ) (B β : ℝ)
    (hc : ∀ M ≤ N, ‖∑ n ∈ Icc 1 M, c n‖ ≤ B) :
    ‖∑ n ∈ Icc 1 N, c n * e (n * β)‖ ≤ B * (1 + 2 * Real.pi * |β| * N) := by
  sorry

/-- Step 2, the non-coprime part: prime powers of primes dividing `q`. -/
theorem noncoprime_part_le (q N : ℕ) (hN : 1 ≤ N) (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) :
    ‖∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), (Λ n : ℂ) * z n‖
      ≤ (q.primeFactors.card : ℝ) * Real.log N := by
  sorry

/-! ### The theorem -/

/-- **Major-arc evaluation.**  Unconditional, with the GRH input as the hypothesis `hB`. -/
theorem majorArc_evaluation (q N a : ℕ) [NeZero q] (hN : 2 ≤ N) (ha : Nat.Coprime a q)
    (β B : ℝ) (hB0 : 0 ≤ B) (hB : TwistedPsiBound q N B) :
    ‖S N ((a : ℝ) / q + β) - ((μ q : ℂ) / (Nat.totient q : ℂ)) * S N β‖
      ≤ Real.sqrt (Nat.totient q) * B * (1 + 2 * Real.pi * |β| * N)
        + 2 * (q.primeFactors.card : ℝ) * Real.log N := by
  sorry

/-- **The GRH form.**  If every non-principal twisted Chebyshev sum satisfies the GRH bound
`‖ψ(M, χ)‖ ≤ C √M log²(qM)`, then on the major arc `|β| ≤ 1/(qN)` the error is
`≪ √(φ(q) N) log²(qN)`. -/
theorem majorArc_evaluation_GRH (C : ℝ) (hC : 0 ≤ C)
    (hGRH : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ M : ℕ,
      ‖psiChi χ M‖ ≤ C * Real.sqrt M * Real.log (q * M) ^ 2)
    (q N a : ℕ) [NeZero q] (hN : 2 ≤ N) (ha : Nat.Coprime a q) (β : ℝ) (hβ : |β| ≤ 1 / (q * N)) :
    ‖S N ((a : ℝ) / q + β) - ((μ q : ℂ) / (Nat.totient q : ℂ)) * S N β‖
      ≤ Real.sqrt (Nat.totient q) * (C * Real.sqrt N * Real.log (q * N) ^ 2) * (1 + 2 * Real.pi)
        + 2 * (q.primeFactors.card : ℝ) * Real.log N := by
  sorry

end PieLab.MajorArc
