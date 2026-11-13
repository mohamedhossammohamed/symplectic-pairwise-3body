---
title: 'SymplecticThreeBody: Machine-Checked Symplecticity and Nine-Integral Conservation of Pairwise Two-Body Kepler Splitting in Lean 4 and C99'
tags:
  - C99
  - Lean 4
  - celestial mechanics
  - three-body problem
  - symplectic integration
  - formal verification
authors:
  - name: Mohammad Hossam Mohammed Ali Zahran
    affiliation: 1
affiliations:
  - name: Faculty of Medicine, Menoufia National University, Egypt
    index: 1
date: 11 November 2026
bibliography: paper.bib
---

# Summary

The gravitational three-body problem is a foundational non-integrable dynamical system in celestial mechanics and astrophysics. To integrate close binary encounters without coordinate singularities, pairwise Keplerian splitting decomposes the $N$-body Hamiltonian into a sum of analytically solvable two-body problems [@GoncalvesFerrari2014; @Hernandez2015].

`SymplecticThreeBody` provides the first complete, axiom-free (`sorry`-free) machine-checked formalization in the **Lean 4** theorem prover [@Moura2021]—paired with a zero-dependency ISO C99 reference implementation—proving that decomposing the three-body problem into three interconnected two-body problems yields an exact canonical transformation that preserves the $18$-dimensional symplectic $2$-form $\omega_{18}$, satisfies strict time-reversibility, and algebraically conserves all $9$ classical Poincaré integrals of motion across every pairwise step.

# Statement of Need

In @Hernandez2015, the symplecticity of the symmetric pairwise two-body Kepler map (`HB15`) was demonstrated *numerically* by computing finite-difference approximations of the $6N \times 6N$ Jacobian matrix $J$ and applying Richardson extrapolation to verify $J^{\mathsf{T}} \Omega J = \Omega$. `SymplecticThreeBody` replaces numerical Jacobian heuristics with formal machine-checked proofs in Lean 4 (`SymplecticThreeBody.lean`) alongside an ISO C99 verification suite (`src/mhmzahran_symplectic_3body.c` and `tests/test_invariants.c`) using universal Stumpff functions [@Yoshida1990; @Hairer2006; @Chenciner2000; @Mathlib2020].

# References
