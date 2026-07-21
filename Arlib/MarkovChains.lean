/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.MarkovChains

Finite Markov chains: the functional-analytic toolkit behind mixing-time
analysis, and worked analyses of specific chains.

The area is deliberately split in two, and the split is the organising principle
of everything here:

* **`Techniques/`** — general machinery that applies to any finite chain.
  Kernels and chains, the `L²(μ)` calculus, the Dirichlet form, the Poincaré
  inequality, decay of variance and of χ²-divergence, total variation and
  mixing time, laziness.
* **`Chains/`** — analyses of *particular* chains.  These are not examples in
  the pedagogical sense; they are the objects the general theory exists to say
  something about, and they keep the general definitions honest by being
  instantiated against them.

The development follows Chen, Štefankovič and Vigoda, *Spectral Independence and
Local-to-Global Techniques for Optimal Mixing of Markov Chains*.

One convention is worth stating up front because it shapes every proof: **the
spectral gap is defined variationally**, by the Poincaré inequality
`γ · Var_μ(f) ≤ ℰ_P(f)`, and never as `1 - λ₂`.  Eigenvalues, and the spectral
theorem for self-adjoint operators, appear nowhere in this area — every result
that a textbook would derive from the spectral decomposition is instead obtained
from an elementary variational or discriminant argument.  This is what keeps the
whole area free of Mathlib's spectral-theory API and of the finite-dimensional
real-symmetric-diagonalization machinery that would otherwise be needed.

## Modules

### Techniques

* `Techniques.Chain` — `FinDist`, `FinKernel`, `FinChain`, the actions `act` and
  `push`, composition and iteration, `Stationary`, `Reversible`.
* `Techniques.Bilinear` — Cauchy–Schwarz for a positive semidefinite symmetric
  bilinear form, proved by the discriminant trick.
* `Techniques.Functional` — the `L²(μ)` calculus: `Ex`, `ip`, `Var`, the pair
  form of the variance, `relDensity` and `chiSq`.
* `Techniques.Dirichlet` — the Dirichlet form, its pair form, the two-sided
  bound `|⟪f, P f⟫_μ| ≤ ⟪f, f⟫_μ`, `SpectralGapAtLeast` (the Poincaré
  inequality) and `NonnegDefinite` (positive semidefiniteness).
* `Techniques.SpectralGap` — from the numerical-range bound to the operator
  bound `⟪P f, P f⟫_μ ≤ c² ⟪f, f⟫_μ`, and hence geometric decay of `Var` and of
  `chiSq`.
* `Techniques.TotalVariation` — total variation distance, its event
  characterisation, the data-processing inequality, mixing time, and the
  Cauchy–Schwarz bridge `(2 · d_TV)² ≤ χ²`.
* `Techniques.Lazy` — the lazy chain `½(I + P)`; the library's supply of
  positive semidefinite chains, and the capstone decay estimate.

### Chains

* `Chains.Metropolis` — the Metropolis–Hastings construction: how to manufacture
  a chain reversible with respect to a prescribed target.
* `Chains.TwoState` — the two-state chain, computed exactly; the calibration
  example against which the general theorems are checked.
-/

import Arlib.MarkovChains.Techniques.Bilinear
import Arlib.MarkovChains.Techniques.Chain
import Arlib.MarkovChains.Techniques.Functional
import Arlib.MarkovChains.Techniques.Dirichlet
import Arlib.MarkovChains.Techniques.SpectralGap
import Arlib.MarkovChains.Techniques.TotalVariation
import Arlib.MarkovChains.Techniques.Lazy
import Arlib.MarkovChains.Techniques.Mixture
import Arlib.MarkovChains.Techniques.Adjoint
import Arlib.MarkovChains.Techniques.Levels
import Arlib.MarkovChains.Techniques.Comparison
import Arlib.MarkovChains.Techniques.Conductance
import Arlib.MarkovChains.Techniques.Coupling
import Arlib.MarkovChains.Techniques.MixingTime
import Arlib.MarkovChains.Chains.Metropolis
import Arlib.MarkovChains.Chains.TwoState
import Arlib.MarkovChains.Chains.IndependentSampler
import Arlib.MarkovChains.Chains.SpinSystem
import Arlib.MarkovChains.Chains.Glauber
import Arlib.MarkovChains.Chains.Pinning
