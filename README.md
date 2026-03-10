# The Prime Inertia Engine (PIE): Classical Fluid Analogue

## 1. System Definition
The Prime Inertia Engine (PIE) visualization is a 3D projection of a classical, non-relativistic vector field. It models a linear biharmonic fluid subjected to discrete point forcing. It does not represent quantum gravity, general relativity, or spacetime curvature.

## 2. The Action Functional
The system is governed by a well-defined action functional on a Sobolev space (e.g., $H^2(\mathbb{R}^{24}, \mathbb{R}^{24})$), using Radon measures (Dirac deltas) to anchor discrete prime nodes within a continuous bulk:

$$S[\mathbf{u}] = \int_{\mathbb{R}^{24}} \left[ \frac{1}{2} |\nabla \mathbf{u}|^2 + M_{\rm vac} |\Delta \mathbf{u}|^2 + \left( \sum_{p \text{ prime}} \chi_6(p) \log p \, \boldsymbol{\delta}^{24}(x - \mathbf{x}_p) \right) \cdot \mathbf{u}(x) \right] d^{24}x$$

* $\mathbf{x}_p$: A fixed embedding mapping primes to distinct coordinates.
* $\chi_6(p)$: The Modulo 6 Dirichlet character, acting as a binary phase switch ($+1$ for $p \equiv 1 \pmod 6$, $-1$ for $p \equiv 5 \pmod 6$).
* The sieve strictly evaluates primes $p \ge 5$, explicitly excluding 2 and 3.

## 3. Euler-Lagrange Mechanics
Applying the variational principle ($\delta S = 0$) yields the following fourth-order partial differential equation:

$$2 M_{\rm vac} \Delta^2 \mathbf{u} - \Delta \mathbf{u} = -\sum_{p \text{ prime}} \chi_6(p) \log p \, \boldsymbol{\delta}^{24}(x - \mathbf{x}_p)$$

## 4. Computational Realization (PIE 3D)
The WebGL simulation serves as a direct, real-time solver for this PDE, projected into 3D Euclidean space:
* **Viscous Drag ($-\Delta \mathbf{u}$):** Implemented as standard Laplacian damping on particle velocities.
* **Hyperviscous Regulator ($-2 M_{\rm vac} \Delta^2 \mathbf{u}$):** A fourth-order damping term controlled by the $M_{\rm vac}$ parameter. This physically demonstrates how high-frequency regularization prevents the discrete Dirac singularities (the prime nodes) from causing computational blow-up.
* **Visual Architecture:** Primes are rendered distinctly (Cyan for $+1$, Orange for $-1$) to illustrate the phase opposition driving the fluid advection.

**Research Status:** This simulation is a rigorously defined classical fluid analogue. The question of whether the geometric constraints observed in this model correlate to the analytic zero-free regions of $L$-functions (via the Rankin-Selberg program) remains an open, unproven research inquiry.
