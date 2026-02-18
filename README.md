# prime-inertia-engine

# Prime Inertia Engine (v2.1)
### A Spectral-Modular Conditional Formalization of the Riemann Hypothesis in Lean 4

[![Lean 4 Verified](https://img.shields.io/badge/Lean-4.24.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib Verified](https://img.shields.io/badge/Mathlib-f897ebcf-green.svg)](https://github.com/leanprover-community/mathlib4)

## Overview
This repository contains a formalization of the **Prime Inertia Engine**, a framework that maps the analytic properties of the Riemann zeta function to the spectral properties of a regularized Berry–Keating operator.

**The Riemann Hypothesis remains unsolved** as of February 18, 2026 (confirmed by the Clay Mathematics Institute and all major surveys). This project provides a **clean, machine-verified conditional approach**: all classical mathematics is unconditionally proven in Lean 4; the final step is isolated as a single explicit axiom.

## Key Features
- **Modular Prime Inertia**: Verified weight-1/2 modular transformation of the Jacobi theta kernel.
- **Symmetric Functional Equation**: `symmetricL s = symmetricL (1-s)` fully proven.
- **Regularized Berry–Keating Operator**: Schwartz-decay domain where `berryKeatingH` is proven symmetric.
- **Axiomatic Isolation**: RH follows immediately from the **Spectral Correspondence Axiom** (a precise Hilbert–Pólya / Berry–Keating realization).

## The Spectral Correspondence Axiom
If the non-trivial zeros of the completed L-function are exactly the eigenvalues of the (self-adjoint extension of the) Berry–Keating operator, then all non-trivial zeros lie on the critical line Re(s) = 1/2.

## Files
- `PrimeInertiaEngine.v2.1.lean` — the full verified Lean 4 formalization
- `paper.pdf` — citation-ready LaTeX documentation

## Usage
```bash
lake exe cache get
lake build
