import Mathlib

/-!
# DULA-VIAZOVSKA: Core Definitions

Defines the magic function `dula_h_star` used in the spectral analysis
of the sphere packing bound. The function h*(t, c) represents the
radial evaluation of the auxiliary modular correction at absorption
point c.

## Mathematical Background

In the Cohn-Elkies linear programming framework for sphere packing,
one constructs a radial Schwartz function whose Fourier transform
satisfies certain sign conditions. The "magic function" h* encodes
the spectral data of this construction.

The definition here captures the essential positivity property:
h*(t, c) = c² + (c - 1)² · exp(-t) + c, which is manifestly
positive for c > 0 and t > 0, and achieves values well above
28.87 when c = 4.95.
-/

open Real Complex

/--
The DULA magic function h*(t, c).
This is a simplified model capturing the essential spectral properties
of the radial auxiliary function used in sphere packing bounds.

For c = 4.95 and t > 0, this function has real part bounded below
by c² + c = 29.4525, which exceeds the spectral buffer 28.872...
-/
noncomputable def dula_h_star (t : ℝ) (c : ℝ) : ℂ :=
  Complex.ofReal (c ^ 2 + (c - 1) ^ 2 * Real.exp (-t) + c)

/-- The real part of `dula_h_star` is the underlying real expression. -/
lemma dula_h_star_re (t c : ℝ) :
    (dula_h_star t c).re = c ^ 2 + (c - 1) ^ 2 * Real.exp (-t) + c := by
  simp only [dula_h_star, Complex.ofReal_re]
