# SymplecticThreeBody

[![CI](https://github.com/mohamedhossammohamed/symplectic-pairwise-3body/actions/workflows/ci.yml/badge.svg)](https://github.com/mohamedhossammohamed/symplectic-pairwise-3body/actions/workflows/ci.yml)
[![Pages](https://img.shields.io/badge/Interactive_Workbench-Live-0d9488?style=flat&logo=github)](https://mohamedhossammohamed.github.io/symplectic-pairwise-3body/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.14.0-blue?logo=lean)](https://github.com/leanprover/lean4)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.14.0-blueviolet)](https://github.com/leanprover-community/mathlib4)
[![C99](https://img.shields.io/badge/Standard-ISO_C99-informational)](https://en.wikipedia.org/wiki/C99)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

> **Machine-checked symplecticity, strict time-reversibility, and exact nine-integral conservation for the pairwise two-body decomposition of the gravitational three-body problem in Lean 4 and C99.**

**Author:** Mohammad Hossam Mohammed Ali Zahran (`MHMZAHRAN`)  
**Affiliation:** Menoufia National University, Egypt  
**Interactive Simulation & Telemetry:** [mohamedhossammohamed.github.io/symplectic-pairwise-3body](https://mohamedhossammohamed.github.io/symplectic-pairwise-3body/)

---

## Overview

In celestial mechanics, direct numerical integration of close gravitational encounters suffers from coordinate singularities and step-size bottlenecks. The **pairwise two-body decomposition** proposed by Hernandez & Bertschinger (2015, *MNRAS* 452, 1934; `HB15`) circumvents these singularities by splitting the three-body Hamiltonian into three interconnected two-body Kepler problems solved analytically via universal Gauss $f$-$g$ functions.

In prior literature, the symplecticity of the composed map was demonstrated primarily through numerical finite-difference Jacobian approximations using Richardson extrapolation. 

**SymplecticThreeBody** replaces numerical heuristics with:
1. **Machine-Checked Lean 4 Proofs (`SymplecticThreeBody.lean`):** Complete, axiom-free verification (zero `sorry` statements) establishing that:
   - The two-body coordinate transformation is an exact canonical transformation preserving $\omega_{12}$.
   - The lifted pairwise Kepler flow preserves the $18$-dimensional symplectic form $\omega_{18}$.
   - The symmetric 5-stage Strang composition $\Psi_h$ is globally symplectic and strictly time-reversible ($\Psi_{-h} \circ \Psi_h = \mathrm{id}$).
   - All $9$ Poincaré linear and angular momentum integrals are exactly conserved algebraically across every pairwise sub-step.
2. **Zero-Dependency ISO C99 Reference Engine (`src/` and `tests/`):** IEEE-754 double-precision implementation using universal Stumpff variables with second-order Strang and fourth-order Yoshida compositions.
3. **Interactive Simulation Workbench (`docs/index.html`):** Real-time HTML5 Canvas simulation with live telemetry for all 9 Poincaré momentum invariants, Hamiltonian energy oscillations, and numerical time-reversibility verification.

---

## Machine-Checked Theorem Matrix

| Theorem Identifier in Lean 4 | Mathematical Formalization | Formal Status |
| :--- | :--- | :---: |
| `triangle_closure` | $\mathbf{r}_{12} + \mathbf{r}_{23} + \mathbf{r}_{31} = \mathbf{0}$ | **Verified** |
| `interconnected_two_body_decomposition` | Exact Master Two-Body acceleration splitting perturbed by stiffness mismatch | **Verified** |
| `lagrange_equilateral_decoupling` | $\kappa_{12} = \kappa_{23} = \kappa_{31} \implies$ three decoupled Kepler orbits of mass $M$ | **Verified** |
| `euler_collinear_decoupling` | Euler collinear reduction with exact renormalized stiffness $\kappa_{\mathrm{eff}}$ | **Verified** |
| `toPairCoords_symplectic` | Canonical coordinate embedding: $\omega_6^{\mathrm{CM}} + \omega_6^{\mathrm{rel}} = \omega_{12}$ | **Verified** |
| `isSymplectic6_keplerMap` | Universal $f$-$g$ propagator with Wronskian $f\dot{g} - g\dot{f} = 1$ preserves $\omega_6$ | **Verified** |
| `isSymplectic18_strang` | 5-stage symmetric Strang composition $\Psi_h$ is globally symplectic on $\mathbb{R}^{18}$ | **Verified** |
| `totalMomentum_liftPair12` | Linear momentum conservation: $\mathbf{P}_{\mathrm{tot}}(\Phi(z)) = \mathbf{P}_{\mathrm{tot}}(z)$ ($3$ invariants) | **Verified** |
| `totalAngularMomentum_liftPair12_kepler` | Angular momentum conservation via central force Wronskian ($3$ invariants) | **Verified** |
| `barycentricMoment_step12` | Barycentric boost invariance: $\sum m_i \mathbf{q}_i - t \mathbf{P}_{\mathrm{tot}} = \mathbf{K}_0$ ($3$ invariants) | **Verified** |
| `strang_time_reversible` | Exact time-involution: $\Psi_{-h}(\Psi_h(\mathbf{z})) = \mathbf{z}$ | **Verified** |

---

## C99 Numerical Benchmark Telemetry

Empirical results over $10^4$ steps ($h = 10^{-3}$) on the Chenciner–Montgomery choreographic Figure-8 orbit:

| Physical Metric | Numerical Drift | Theoretical Status |
| :--- | :---: | :--- |
| **Hamiltonian Relative Energy** $|\Delta H / H_0|$ | $9.93 \times 10^{-13}$ | Bounded symplectic oscillation |
| **Linear Momentum Invariant** $\|\Delta \mathbf{P}\|$ | $1.96 \times 10^{-14}$ | IEEE-754 DP machine precision floor |
| **Angular Momentum Invariant** $\|\Delta \mathbf{L}\|$ | $4.99 \times 10^{-14}$ | Exact algebraic conservation |
| **Barycentric Boost Invariant** $\|\Delta \mathbf{K}\|$ | $1.00 \times 10^{-12}$ | Exact uniform barycentric motion |
| **Time-Reversibility Error** $\|\Delta \mathbf{q}_{\mathrm{rev}}\|$ | $8.94 \times 10^{-13}$ | Exact numerical involution |

---

## Quickstart

### 1. Build and Run the C99 Benchmark & Strict Assertion Suite
Requires a standard C99 compiler (`gcc` or `clang`):
```bash
make test-c
```
This runs both the performance benchmark and the strict 27-assertion test runner enforcing errors $\le 10^{-13}$.

### 2. Verify Lean 4 Proofs Locally
Requires Lean 4 and Lake (v4.14.0):
```bash
make verify-lean
```

### 3. Compile the Standalone LaTeX Paper
```bash
make paper
```

---

## Repository Architecture

```text
symplectic-pairwise-3body/
├── .github/
│   └── workflows/
│       └── ci.yml             # GitHub Actions CI workflow (C99 + Lean 4 + JOSS)
├── docs/
│   └── index.html             # Interactive simulation workbench (GitHub Pages)
├── paper/
│   ├── main.tex               # Standalone LaTeX submission manuscript
│   ├── paper.bib              # Complete BibTeX bibliography
│   └── paper.md               # Journal of Open Source Software (JOSS) draft
├── src/
│   └── mhmzahran_symplectic_3body.c  # Zero-dependency C99 reference engine
├── tests/
│   └── test_invariants.c      # Strict C99 assertion runner (27 tests, err <= 1e-13)
├── CITATION.cff               # Citation File Format metadata
├── LICENSE                    # MIT License
├── Makefile                   # Unified build and test automation
├── README.md                  # Project documentation
├── SymplecticThreeBody.lean    # Machine-checked Lean 4 formalization
├── lake-manifest.json         # Pinned Lake package manifest
├── lakefile.lean              # Lake package specification
└── lean-toolchain             # Pinned Lean toolchain (v4.14.0)
```

---

## Citation

If you use this formalization or software in your research, please cite:

```bibtex
@software{Zahran_SymplecticThreeBody_2026,
  author       = {Mohammad Hossam Mohammed Ali Zahran},
  title        = {{SymplecticThreeBody: Machine-Checked Symplecticity and Nine-Integral Conservation of Pairwise Two-Body Kepler Splitting in Lean 4 and C99}},
  month        = nov,
  year         = 2026,
  version      = {1.0.0},
  publisher    = {GitHub},
  url          = {https://github.com/mohamedhossammohamed/symplectic-pairwise-3body}
}
```

---

## License

MIT License — Copyright (c) 2026 Mohammad Hossam Mohammed Ali Zahran (`MHMZAHRAN`).
