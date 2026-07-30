# The Prime Inertia Engine (PIE)

> **Classical Fluid Analogue · 26-Dimensional Projection · Biharmonic Regularization**

[![WebGL](https://img.shields.io/badge/WebGL-Simulation-00f7ff?style=flat-square&logo=webgl)](https://github.com/DULA2025/prime-inertia-engine/blob/main/Prime%20Inertia%20Engine%20(3D).html)
[![CodePen](https://img.shields.io/badge/CodePen-Live%20Demo-47CF73?style=flat-square&logo=codepen)](https://codepen.io/DULA2025/pen/LERMgxv)
[![Manifold](https://img.shields.io/badge/Manifold-R²⁶-ff9100?style=flat-square)](#)
[![License](https://img.shields.io/badge/License-Research-lightgrey?style=flat-square)](#)

---

## 1. System Definition

The **Prime Inertia Engine (PIE)** visualization is a 3D projection of a classical, non-relativistic vector field. It models a **linear biharmonic fluid** subjected to discrete point forcing at prime-labeled nodes.

> **Note:** This system is a rigorously defined *classical fluid analogue*.  
> It does **not** represent quantum gravity, general relativity, or spacetime curvature.

---

## 2. The Action Functional

The dynamics are governed by a well-defined action on a Sobolev space  
`H²(ℝ²⁶, ℝ²⁶)`, using Radon measures (Dirac deltas) to anchor discrete prime nodes inside a continuous 26-dimensional bulk:

```text
S[u] = ∫_{ℝ²⁶} [ ½ |∇u|² + M_vac |Δu|²
                 + ( Σ_{p prime} χ₆(p) log p · δ²⁶(x − x_p) ) · u(x) ] d²⁶x
```

Compact form:

$$
S[\mathbf{u}] = \int_{\mathbb{R}^{26}} \left( \frac{1}{2}|\nabla\mathbf{u}|^2 + M_{\rm vac}|\Delta\mathbf{u}|^2 + \mathbf{f}\cdot\mathbf{u} \right)\,d^{26}x
$$

where the forcing density is

$$
\mathbf{f}(x) = \sum_{p\ \rm prime} \chi_6(p)\,\log p\ \boldsymbol{\delta}^{26}(x-\mathbf{x}_p)
$$

### Key Parameters

| Symbol | Meaning |
|--------|---------|
| **x_p** | Fixed embedding of primes into ℝ²⁶ (construction ℝ¹,¹ × Λ₂₄ ⊗ ℝ) |
| **χ₆(p)** | Mod-6 Dirichlet character (binary phase switch) |
| | 🟢 **+1** when p ≡ 1 (mod 6) |
| | 🟠 **−1** when p ≡ 5 (mod 6) |
| **Sieve** | Only primes p ≥ 5 (2 and 3 excluded) |

### Arithmetic Viscosity (corrected)

The hyperviscous coefficient is fixed by modular arithmetic at the fixed point τ = i:

$$
M_{\rm vac} = \ln 2 \cdot \ln 3 \cdot e^{-2\pi} \approx 0.00142206
$$

This value replaces earlier inconsistent numerical claims and is the default viscosity used in all current WebGL solvers.

---

## 3. Euler–Lagrange Mechanics

Stationarity of the action (δS = 0) yields the fourth-order linear PDE

$$
2\,M_{\rm vac}\,\Delta^{2}\mathbf{u} - \Delta\mathbf{u} = -\sum_{p\ \rm prime}\chi_6(p)\,\log p\ \boldsymbol{\delta}^{26}(x-\mathbf{x}_p)
$$

- **−Δu** — ordinary viscous drag  
- **2 M_vac Δ²u** — biharmonic (hyperviscous) regularizer that damps the highest modes and keeps the Dirac nodes from producing finite-time blow-up

---

## 4. Computational Realization

True 26-dimensional space cannot be rendered directly. The engine therefore **projects** the vector field into ordinary 3-D Euclidean space, treating the remaining dimensions as internal topological offsets.

### Core WebGL Engine

| Component | Implementation |
|-----------|----------------|
| Viscous drag (−Δu) | Laplacian damping on particle / grid velocities |
| Hyperviscosity (2 M_vac Δ²u) | Fourth-order term controlled by the corrected M_vac |
| Prime nodes | Colored by χ₆: **cyan** (+1), **orange** (−1) |
| Live demo | [GitHub HTML](https://github.com/DULA2025/prime-inertia-engine/blob/main/Prime%20Inertia%20Engine%20(3D).html) · [CodePen](https://codepen.io/DULA2025/pen/LERMgxv) |

### Hybrid & Lattice Demonstrations

Additional interactive solvers explore the same biharmonic regularization in classical CFD settings (von Kármán wakes, cube / sphere obstacles, D2Q9 / D3Q19 lattices):

- **Hybrid GPGPU 3-D Kármán** — CPU projection Navier–Stokes + WebGL2 particle advection, interactive cube / sphere, professional CFD colormap  
- **Improved PIE Kármán** — 64×32×32 grid, 1 M GPU particles, corrected M_vac, draggable obstacle  
- **Lattice-Boltzmann** — full D2Q9 (2-D) and D3Q19 (3-D) BGK solvers with bounce-back obstacles  

These demos illustrate how a small, modularly-derived hyperviscosity stabilizes discrete forcing and produces coherent vortical structures.

---

## 5. Research Status

This repository contains:

- a **classical fluid analogue** whose mathematics is fully specified,
- Lean 4 formalizations of the DULA grading and related arithmetic statements,
- interactive WebGL / GPGPU visualizations of the projected biharmonic dynamics.

Whether the geometric constraints observed in the model correlate with analytic zero-free regions of L-functions (via the Rankin–Selberg program), or whether the spectral correspondence axioms formalized in the Lean sources imply the Riemann Hypothesis, remains an **open, unproven research inquiry**.

---

## Repository Layout (selected)

```text
Prime Inertia Engine (3D).html   # primary WebGL particle engine
*.lean                           # DULA / spectral formalizations
README.md                        # this file
```

---

## License & Citation

Intended for research and educational use.  
If you build upon the classical fluid analogue or the corrected M_vac formula, please cite this repository.

```text
DULA2025, Prime Inertia Engine (PIE),
https://github.com/DULA2025/prime-inertia-engine
```
# 🌌 The Prime Inertia Engine (PIE)

> **Classical Fluid Analogue · 26-Dimensional Projection · Biharmonic Regularization**

[![WebGL](https://img.shields.io/badge/WebGL-Simulation-00f7ff?style=flat-square&logo=webgl)](https://github.com/DULA2025/prime-inertia-engine/blob/main/Prime%20Inertia%20Engine%20(3D).html)
[![CodePen](https://img.shields.io/badge/CodePen-Live%20Demo-47CF73?style=flat-square&logo=codepen)](https://codepen.io/DULA2025/pen/LERMgxv)
[![Manifold](https://img.shields.io/badge/Manifold-%E2%84%9D%C2%B2%E2%81%B6-ff9100?style=flat-square)](#)
[![License](https://img.shields.io/badge/License-Research-lightgrey?style=flat-square)](#)

---

## 📐 1. System Definition

The **Prime Inertia Engine (PIE)** visualization is a 3D projection of a classical, non-relativistic vector field. It models a **linear biharmonic fluid** subjected to discrete point forcing at prime-labeled nodes.

> **Note:** This system is a rigorously defined *classical fluid analogue*.  
> It does **not** represent quantum gravity, general relativity, or spacetime curvature.

---

## ⚙️ 2. The Action Functional

The dynamics are governed by a well-defined action on a Sobolev space  
\( H^2(\mathbb{R}^{26},\mathbb{R}^{26}) \), using Radon measures (Dirac deltas) to anchor discrete prime nodes inside a continuous 26-dimensional bulk:

$$
S[\mathbf{u}] = \int_{\mathbb{R}^{26}} \Biggl[
  \frac12 |\nabla\mathbf{u}|^2
  + M_{\mathrm{vac}} |\Delta\mathbf{u}|^2
  + \Biggl( \sum_{p\,\mathrm{prime}} \chi_6(p)\,\log p\;
    \boldsymbol{\delta}^{26}(x-\mathbf{x}_p) \Biggr)\cdot\mathbf{u}(x)
\Biggr]\,d^{26}x
$$

### Key Parameters

| Symbol | Meaning |
|--------|---------|
| \(\mathbf{x}_p\) | Fixed embedding of primes into \(\mathbb{R}^{26}\) (construction \(\mathbb{R}^{1,1}\times\Lambda_{24}\otimes\mathbb{R}\)) |
| \(\chi_6(p)\) | Mod-6 Dirichlet character (binary phase switch) |
| | 🟢 \(+1\) when \(p\equiv 1\pmod6\) |
| | 🟠 \(-1\) when \(p\equiv 5\pmod6\) |
| Sieve | Only primes \(p\ge 5\) (2 and 3 excluded) |

### Arithmetic Viscosity (corrected)

The hyperviscous coefficient is fixed by modular arithmetic at the fixed point \(\tau=i\):

$$
M_{\mathrm{vac}} \;=\; \ln 2\cdot\ln 3\cdot e^{-2\pi}
\;\approx\; 0.00142206
$$

This value replaces earlier inconsistent numerical claims and is the default viscosity used in all current WebGL solvers.

---

## 🧮 3. Euler–Lagrange Mechanics

Stationarity of the action (\(\delta S=0\)) yields the fourth-order linear PDE

$$
2\,M_{\mathrm{vac}}\,\Delta^{2}\mathbf{u}
-\Delta\mathbf{u}
=-\sum_{p\,\mathrm{prime}}\chi_6(p)\,\log p\;
\boldsymbol{\delta}^{26}(x-\mathbf{x}_p).
$$

- \(-\Delta\mathbf{u}\) — ordinary viscous drag  
- \(2M_{\mathrm{vac}}\Delta^{2}\mathbf{u}\) — biharmonic (hyperviscous) regularizer that damps the highest modes and keeps the Dirac nodes from producing finite-time blow-up

---

## 💻 4. Computational Realization

True 26-dimensional space cannot be rendered directly. The engine therefore **projects** the vector field into ordinary 3-D Euclidean space, treating the remaining dimensions as internal topological offsets.

### Core WebGL Engine

| Component | Implementation |
|-----------|----------------|
| Viscous drag \(-\Delta\mathbf{u}\) | Laplacian damping on particle / grid velocities |
| Hyperviscosity \(2M_{\mathrm{vac}}\Delta^{2}\mathbf{u}\) | Fourth-order term controlled by the corrected \(M_{\mathrm{vac}}\) |
| Prime nodes | Colored by \(\chi_6\): **cyan** (\(+1\)), **orange** (\(-1\)) |
| Live demo | [GitHub HTML](https://github.com/DULA2025/prime-inertia-engine/blob/main/Prime%20Inertia%20Engine%20(3D).html) · [CodePen](https://codepen.io/DULA2025/pen/LERMgxv) |

### Hybrid & Lattice Demonstrations

Additional interactive solvers explore the same biharmonic regularization in classical CFD settings (von Kármán wakes, cube / sphere obstacles, D2Q9 / D3Q19 lattices):

- **Hybrid GPGPU 3-D Kármán** — CPU projection Navier–Stokes + WebGL2 particle advection, interactive cube / sphere, professional CFD colormap  
- **Improved PIE Kármán** — 64×32×32 grid, 1 M GPU particles, corrected \(M_{\mathrm{vac}}\), draggable obstacle  
- **Lattice-Boltzmann** — full D2Q9 (2-D) and D3Q19 (3-D) BGK solvers with bounce-back obstacles  

These demos illustrate how a small, modularly-derived hyperviscosity stabilizes discrete forcing and produces coherent vortical structures.

---

## 🔬 5. Research Status

This repository contains:

- a **classical fluid analogue** whose mathematics is fully specified,
- Lean 4 formalizations of the DULA grading and related arithmetic statements,
- interactive WebGL / GPGPU visualizations of the projected biharmonic dynamics.

Whether the geometric constraints observed in the model correlate with analytic zero-free regions of \(L\)-functions (via the Rankin–Selberg program), or whether the spectral correspondence axioms formalized in the Lean sources imply the Riemann Hypothesis, remains an **open, unproven research inquiry**.

---

## 📁 Repository Layout (selected)

```
Prime Inertia Engine (3D).html   # primary WebGL particle engine
*.lean                           # DULA / spectral formalizations
README.md                        # this file
```

---

## 📜 License & Citation

Intended for research and educational use.  
If you build upon the classical fluid analogue or the corrected \(M_{\mathrm{vac}}\) formula, please cite this repository.

```
DULA2025, Prime Inertia Engine (PIE),
https://github.com/DULA2025/prime-inertia-engine
```
# 🌌 The Prime Inertia Engine (PIE)
> **Classical Fluid Analogue | 26-Dimensional Projection | Biharmonic Regularization**

[![WebGL](https://img.shields.io/badge/WebGL-Simulation-00f7ff?style=flat-square&logo=webgl)](https://github.com/DULA2025/prime-inertia-engine/blob/main/Prime%20Inertia%20Engine%20(3D).html)
[![Manifold](https://img.shields.io/badge/Manifold-%E2%84%9D%C2%B2%E2%81%B6-ff9100?style=flat-square)](#)

## 📐 1. System Definition
The **Prime Inertia Engine (PIE)** visualization is a 3D projection of a classical, non-relativistic vector field. It models a linear biharmonic fluid subjected to discrete point forcing. 

*Note: This system is a rigorously defined classical fluid analogue. It does not represent quantum gravity, general relativity, or spacetime curvature.*

---

## ⚙️ 2. The Action Functional
The system is governed by a well-defined action functional on a Sobolev space (e.g., $H^2(\mathbb{R}^{26}, \mathbb{R}^{26})$), using Radon measures (Dirac deltas) to anchor discrete prime nodes within a continuous 26-dimensional bulk:

$$S[\mathbf{u}] = \int_{\mathbb{R}^{26}} \left[ \frac{1}{2} |\nabla \mathbf{u}|^2 + M_{\rm vac} |\Delta \mathbf{u}|^2 + \left( \sum_{p \text{ prime}} \chi_6(p) \log p \, \boldsymbol{\delta}^{26}(x - \mathbf{x}_p) \right) \cdot \mathbf{u}(x) \right] d^{26}x$$

### Key Parameters:
* **$\mathbf{x}_p$**: A fixed embedding mapping primes to distinct coordinates within the $\mathbb{R}^{26}$ manifold ($\mathbb{R}^{1,1} \times \Lambda_{24} \otimes \mathbb{R}$).
* **$\chi_6(p)$**: The Modulo 6 Dirichlet character, acting as a binary phase switch:
    * 🟢 **$+1$** for $p \equiv 1 \pmod 6$
    * 🟠 **$-1$** for $p \equiv 5 \pmod 6$
* **Sieve Constraint**: The system strictly evaluates primes $p \ge 5$, explicitly excluding 2 and 3.

---

## 🧮 3. Euler-Lagrange Mechanics
Applying the variational principle ($\delta S = 0$) yields the following fourth-order partial differential equation:

$$2 M_{\rm vac} \Delta^2 \mathbf{u} - \Delta \mathbf{u} = -\sum_{p \text{ prime}} \chi_6(p) \log p \, \boldsymbol{\delta}^{26}(x - \mathbf{x}_p)$$

---

## 💻 4. Computational Realization (PIE 3D)
The WebGL simulation serves as a direct, real-time solver for this PDE. Because true 26D space cannot be visualized directly, the engine projects the vector field into a 3D Euclidean observable space, treating the remaining 23 dimensions as internal topological offsets.

* 🌊 **Viscous Drag ($-\Delta \mathbf{u}$)**: Implemented as standard Laplacian damping on particle velocities to maintain laminar stability.
* 🛡️ **Hyperviscous Regulator ($-2 M_{\rm vac} \Delta^2 \mathbf{u}$)**: A fourth-order damping term controlled by the $M_{\rm vac}$ parameter. This physically demonstrates how high-frequency regularization—combined with the internal compactified dimensions—prevents the discrete Dirac singularities (the prime nodes) from causing computational blow-up.
* 🎨 **Visual Architecture**: Primes are rendered distinctly (**Cyan** for $+1$, **Orange** for $-1$) to illustrate the phase opposition driving the fluid advection.

---

## 🔬 Research Status
> This simulation is a rigorously defined classical fluid analogue. The question of whether the geometric constraints observed in this model correlate to the analytic zero-free regions of $L$-functions (via the Rankin-Selberg program) remains an open, unproven research inquiry.

🔗 **Live Simulation:** [View the 3D Engine on GitHub](https://github.com/DULA2025/prime-inertia-engine/blob/main/Prime%20Inertia%20Engine%20(3D).html)# The Prime Inertia Engine (PIE): Classical Fluid Analogue

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


** SEE link: https://github.com/DULA2025/prime-inertia-engine/blob/main/Prime%20Inertia%20Engine%20(3D).html

** SEE Live here: https://codepen.io/DULA2025/pen/LERMgxv
