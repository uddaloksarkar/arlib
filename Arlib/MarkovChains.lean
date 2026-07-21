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

### Techniques — the `L²` core

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

### Techniques — distance, mixing, and sources of positivity

* `Techniques.TotalVariation` — total variation distance, its event
  characterisation, the data-processing inequality, mixing time, and the
  Cauchy–Schwarz bridge `(2 · d_TV)² ≤ χ²`.
* `Techniques.MixingTime` — `T_mix(ε) ≤ (2/γ) · ln(1 / (2ε√μ_min))`.
* `Techniques.Coupling` — couplings, and total variation distance as exactly the
  minimum disagreement probability.
* `Techniques.Lazy` — the lazy chain `½(I + P)`: positive semidefiniteness at the
  cost of halving the gap.
* `Techniques.Mixture` — mixtures and uniform averages of kernels; positive
  semidefiniteness is inherited, free.
* `Techniques.Adjoint` — mutually adjoint kernel pairs.  Reversibility *and*
  positive semidefiniteness of both composites, free, from one identity.
* `Techniques.Comparison` — transfer of a Poincaré inequality along a comparison
  of Dirichlet forms.
* `Techniques.Conductance` — the easy direction of Cheeger's inequality.

### Techniques — the local-to-global machinery

* `Techniques.Levels` — weighted simplicial complexes: the level distributions
  and the up/down operators, adjoint by construction.
* `Techniques.LocalWalk` — links (conditioning does not leave the category) and
  the local walk.
* `Techniques.LevelVariance` — the law of total variance for a bare kernel, and
  hence the one-step identity
  `Var_{π_{k+1}}(g) = Var_{π_k}(U g) + ℰ_{downUp}(g)`.
* `Techniques.LocalToGlobal` — the guarded link distribution, and the exact
  decomposition `Var_{π_n}(f) = Σ_{k<n} ℰ_{downUp_k}(f^{(k+1)})` obtained by
  telescoping that identity down the levels.
* `Techniques.Transport` — μ-almost-everywhere agreement of chains, and
  transport of the whole `L²` theory along an injective embedding of state
  spaces.

### Techniques — entropy

* `Techniques.Entropy` — `Ent`, entropy production, the modified log-Sobolev
  inequality, `klDiv`.  Also `NaiveModLogSobolev`, retained as a documented
  warning: it is vacuous, because its two sides scale differently.
* `Techniques.EntropyVariational` — Young's inequality for entropy, the Gibbs
  variational principle, `Ent ≤ Var / E`, and hence `KL ≤ χ²`.

### Techniques — spectral independence, without eigenvalues

* `Techniques.PsdOrder` — quadratic forms of a plain `ι → ι → ℝ` and the PSD
  ordering `PsdLe`.  No `Matrix`, no spectrum.
* `Techniques.SpectralIndependence` — the covariance form of the indicator
  vector, with `quadForm (Cov μ) a = Var μ (fun σ => ∑ v, a (v, σ v))`, and
  spectral independence *defined* as the PSD ordering `Cov ⪯ η · diag(marg)` —
  the eigenvalue-free equivalent of `λ_max(Ψ) ≤ η`.
* `Techniques.LocalSpectralIndependence` — the payoff: spectral independence
  implies a Poincaré inequality for the local walk at any pinning, matching the
  monograph's `γ_k ≥ 1 − η/(n−k−1)` with no slack.  The monograph proves this
  with `λ_max(Ψ)` and a block-matrix argument; here it is an exact identity
  `ℰ_Q(f) = m/(m−1)·Var_π(f) − quadForm (Cov μ) f̃ / (m(m−1))`.

### Chains

* `Chains.Metropolis` — the Metropolis–Hastings construction: how to manufacture
  a chain reversible with respect to a prescribed target.
* `Chains.TwoState` — the two-state chain, computed exactly; the calibration
  example against which the general theorems are checked.
* `Chains.IndependentSampler` — the library's extreme case: Dirichlet form equal
  to the variance, Poincaré constant exactly `1`, mixes in one step.
* `Chains.SpinSystem` — configurations, the partition function, the Gibbs
  measure, local partition functions.
* `Chains.Glauber` — single-site heat-bath updates and the Glauber dynamics;
  positive semidefinite by self-adjoint idempotence.
* `Chains.BlockDynamics` — heat-bath block dynamics, with Glauber as the
  singleton-block case.
* `Chains.GlauberTensorization` — approximate tensorization of variance, in both
  directions, and an end-to-end mixing bound.
* `Chains.Pinning` — pinnings and conditional Gibbs measures; a single-site
  update *is* conditioning on every other site.
* `Chains.PinnedGlauber` — conditioning does not leave the category: pinned
  marginals, `π_{η,1}`, and the local walk `Q_η`, which is shown to be the
  complex-side `localWalk` entry for entry.
* `Chains.LevelEncoding` — a spin system *is* a weighted complex over
  (site, spin) pairs; the down-up walk at the top level is the Glauber dynamics.
* `Chains.GlauberViaLevels` — transporting that encoding back, so the `Levels`
  theory applies to the Gibbs sampler.
* `Chains.HardCore` — the monograph's two running examples, hard-core and Ising,
  with explicit single-site updates.
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
import Arlib.MarkovChains.Techniques.LocalWalk
import Arlib.MarkovChains.Techniques.Entropy
import Arlib.MarkovChains.Techniques.Comparison
import Arlib.MarkovChains.Techniques.Conductance
import Arlib.MarkovChains.Techniques.Coupling
import Arlib.MarkovChains.Techniques.MixingTime
import Arlib.MarkovChains.Techniques.LevelVariance
import Arlib.MarkovChains.Techniques.LocalToGlobal
import Arlib.MarkovChains.Techniques.Transport
import Arlib.MarkovChains.Techniques.EntropyVariational
import Arlib.MarkovChains.Techniques.PsdOrder
import Arlib.MarkovChains.Techniques.SpectralIndependence
import Arlib.MarkovChains.Techniques.LocalSpectralIndependence
import Arlib.MarkovChains.Chains.Metropolis
import Arlib.MarkovChains.Chains.TwoState
import Arlib.MarkovChains.Chains.IndependentSampler
import Arlib.MarkovChains.Chains.SpinSystem
import Arlib.MarkovChains.Chains.Glauber
import Arlib.MarkovChains.Chains.Pinning
import Arlib.MarkovChains.Chains.BlockDynamics
import Arlib.MarkovChains.Chains.GlauberTensorization
import Arlib.MarkovChains.Chains.LevelEncoding
import Arlib.MarkovChains.Chains.GlauberViaLevels
import Arlib.MarkovChains.Chains.PinnedGlauber
import Arlib.MarkovChains.Chains.HardCore
