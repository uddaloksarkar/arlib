/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.MetropolisOverlapSqrt
import Arlib.MarkovChains.Continuous.MixingSqrt

/-!
# The Metropolis-filtered Gaussian ball walk on a convex body mixes in `O(n²)` steps

Two finished results sit in this library and had never been composed:

* `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge`
  (`MetropolisOverlapSqrt.lean:278`) — the conductance of `metropolisGaussian K δ σ²` with
  respect to `Arlib.uniformOn (volume.withDensity (gaussianWeight σ²)) K` is at least
  `δ·log 2/(640·σ·√n)`, given an isoperimetric hypothesis `hiso`;
* `Arlib.MarkovChains.mixesWithin_lazy_at_operative_step` (`MixingSqrt.lean:400`) and
  `Arlib.MarkovChains.mixesWithin_at_operative_step` (`:361`) — a conductance lower bound of
  that exact shape, read at the operative step `δ = σ/(8√n)`, is
  `5120²·n²·(log M + 2·log(1/ε))/(log 2)² + 1` steps to total variation `ε` from an
  `M`-warm start (four times that for the lazy chain).

This file is the composition, and nothing else.  Every declaration is a `theorem`; there is
no `def`, `structure`, `class` or `axiom` here.

## What is proved

*Side conditions (§1).*  `isProbabilityMeasure_uniformOn_gaussianWeight` and
`smallSets_uniformOn_gaussianWeight_nonempty` — the two facts about the target measure alone
that the mixing route needs, repackaged from `Arlib.isProbabilityMeasure_uniformOn` and
`Arlib.MarkovChains.exists_smallSet_uniformOn_gaussian` (`MetropolisConductance.lean:641`).

*The lazy chain (§2).*  `mixesWithin_lazy_metropolisGaussian_at_operative_step` — at
`δ = σ/(8√n)`, where `σ` cancels out of the conductance,

    4·5120²·n²·(log M + 2·log(1/ε))/(log 2)² + 1     steps suffice,

for `lazy (metropolisGaussian K δ σ²)`.  `mixesWithin_lazy_metropolisGaussian_sqrt` is the
same statement at a general step `δ ≤ σ/(8√n)`, before the cancellation.

*The plain chain (§3).*  `mixesWithin_metropolisGaussian_at_operative_step` and
`mixesWithin_metropolisGaussian_sqrt` — the same counts without the factor `4`, at the cost of
one extra binder `hpsd` (see below).

*Non-vacuity (§4).*  `exists_mixesWithin_lazy_metropolisGaussian_witness` — every binder of
both lazy theorems *except* `hiso`, satisfied simultaneously by one concrete body, with a
conclusion that is not the trivial `ε ≥ 1`.

## Which hypotheses are discharged and which are carried

**Discharged here**, so that they do *not* appear as binders:

* `IsMarkovKernel (metropolisGaussian K δ s)` — instance
  `Arlib.MarkovChains.isMarkovKernel_metropolisGaussian` (`MetropolisGaussian.lean:489`);
* `IsReversible (metropolisGaussian K δ σ²) π` — `Arlib.MarkovChains.isReversible_metropolisGaussian`
  (`MetropolisGaussian.lean:586`), which needs nothing but measurability of `K`;
* `IsProbabilityMeasure π` — `Arlib.isProbabilityMeasure_uniformOn` through
  `Arlib.MarkovChains.withDensity_gaussianWeight_ne_zero` / `_ne_top`;
* `(SmallSets π (1/2)).Nonempty` — `Arlib.MarkovChains.exists_smallSet_uniformOn_gaussian`.

**Carried as binders**, honestly:

* `hiso` — Cousins–Vempala's isoperimetric inequality for the Gaussian-restricted density, in
  the exact shape `conductance_metropolisGaussian_sharp_sqrt_ge` consumes it.  It is the
  *only* unproved binder of the lazy theorems *in this file*: everything else below is either
  discharged above, geometric data about `K` that a caller supplies, or the warm-start /
  accuracy parameters.

  ⚠ **`hiso` is now proved.**  `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`
  (`Arlib/Convexity/OneDimSharp.lean`) discharges it for convex `K` under the single extra
  hypothesis `hRσ : √3·R ≤ 2σ√n`.  The theorems of this file are therefore superseded by the
  `_of_convex` versions in `Arlib/MarkovChains/Continuous/MetropolisMixingUncond.lean`, which
  carry no `hiso` and have an unconditional non-vacuity witness.  The statements here are kept
  as the general form: a caller with a non-convex `K` and its own `hiso` can still use them.
* `hpsd : HasNonnegSpectrum (metropolisGaussian K δ σ²) π` — **plain chain only**.  It is not
  removable in general: `ConductanceToTV.lean:229–243` records the swap kernel on `Bool`,
  reversible with `Φ = 1`, whose decay bound is false.  Nothing in this repository proves it
  for `metropolisGaussian`; it would take a Metropolis-specific spectral fact.  The lazy
  theorems need no spectral hypothesis at all — `Arlib.MarkovChains.hasNonnegSpectrum_lazy`
  supplies it from reversibility — which is why the lazy version is the one that actually
  closes, at exactly four times the deadline.
* the geometry of `K` (`hK`, `hKc`, `hKR`, `hKtop`, `hK0`), the local-conductance floor
  `hell`, and the acceptance floor `hfloor` — all inherited verbatim from
  `conductance_metropolisGaussian_sharp_sqrt_ge`;
* the warm start `hM`, `hwarm` (a conductance mixing bound is always warm-start-relative) and
  the accuracy `0 < ε ≤ 1`.

## Scope: this is a Markov-chain mixing statement, and nothing more

The conclusion is `MixesWithin`: the law of the chain after `t` steps is within total
variation `ε` of its stationary law.  **It is not a running-time statement.**  In particular
it says nothing about TTC, about the charged cost model, or about any `O(m·n⁴)` bound; no
count of arithmetic operations, oracle calls or samples appears anywhere in it, and the step
count below must not be quoted as one.  Moreover, since `hiso` is a binder and is unproved
here, none of these theorems is an *unconditional* mixing bound for the Metropolis-filtered
Gaussian ball walk — they are exactly as conditional as
`conductance_metropolisGaussian_sharp_sqrt_ge` is.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The two facts about the target measure alone

`Arlib.MarkovChains.mixesWithin_of_conductance_of_stepCount` and everything above it in
`MixingSqrt.lean` need the stationary law to be a probability measure and the space to be
non-degenerate.  Both are already available for the Gaussian-restricted uniform measure; these
two theorems only put them in the shape the mixing route consumes. -/

/-- **The Gaussian-restricted uniform measure on a body of positive finite volume is a
probability measure.**  `Arlib.isProbabilityMeasure_uniformOn` with its two guards discharged
by `Arlib.MarkovChains.withDensity_gaussianWeight_ne_zero` and
`Arlib.MarkovChains.withDensity_gaussianWeight_ne_top` (`MetropolisConductance.lean:618`,
`:625`). -/
theorem isProbabilityMeasure_uniformOn_gaussianWeight
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s)) K) :=
  Arlib.isProbabilityMeasure_uniformOn _ (withDensity_gaussianWeight_ne_zero s hK0)
    (withDensity_gaussianWeight_ne_top hs hK hKtop)

/-- **The non-degeneracy hypothesis `(SmallSets π (1/2)).Nonempty`, discharged for a body of
positive finite volume.**  This is `Arlib.MarkovChains.exists_smallSet_uniformOn_gaussian`
(`MetropolisConductance.lean:641`) repackaged: membership in `SmallSets` is definitionally the
conjunction it produces. -/
theorem smallSets_uniformOn_gaussianWeight_nonempty (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {s : ℝ} (hs : 0 < s) :
    (SmallSets (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s)) K)
      (1 / 2)).Nonempty := by
  obtain ⟨S, hSm, hSpos, hShalf⟩ := exists_smallSet_uniformOn_gaussian hn hK hK0 hKtop hs
  exact ⟨S, hSm, hSpos, hShalf⟩

/-! ## 2. The lazy chain: `O(n²·(log M + log(1/ε)))` steps

This is the composition that actually closes, because
`Arlib.MarkovChains.mixesWithin_lazy_at_operative_step` assumes no spectral property. -/

/-- **The Metropolis-filtered Gaussian ball walk on a convex body mixes in `O(n²)` steps
(lazy chain).**

At the operative step `δ = σ/(8√n)` the certified conductance is `log 2/(5120·n)` — `σ` has
cancelled — and

    4·5120²·n²·(log M + 2·log(1/ε))/(log 2)² + 1

steps of `lazy (metropolisGaussian K δ σ²)` bring an `M`-warm start within total variation `ε`
of the stationary law `Arlib.uniformOn (volume.withDensity (gaussianWeight σ²)) K`.  The factor
`4` is `Arlib.MarkovChains.conductance_lazy`'s exact halving of the conductance; it is the
price of not assuming `HasNonnegSpectrum`.

The step is pinned by the equation `hδop : δ = σ/(8√n)` rather than substituted into the
statement, so that `hell`, `hfloor` and `hiso` stay readable at a plain `δ`.

Reversibility, `IsProbabilityMeasure` of the target, `IsMarkovKernel` and the non-degeneracy
hypothesis `(SmallSets π (1/2)).Nonempty` are all discharged inside; see the module docstring.
**`hiso` is the only unproved binder** — everything else is data about `K`, the two floors,
and the warm-start/accuracy parameters.

**This is not a running-time statement.**  See the module docstring. -/
theorem mixesWithin_lazy_metropolisGaussian_at_operative_step (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδop : δ = σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) →
      δ * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (metropolisGaussian K δ (σ ^ 2)))
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K)
      mu0 t (ENNReal.ofReal eps) := by
  subst hδop
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hδpos : 0 < σ / (8 * Real.sqrt n) := by positivity
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  haveI := isProbabilityMeasure_uniformOn_gaussianWeight hK hK0 hKtop hs
  exact mixesWithin_lazy_at_operative_step hn hσ
    (isReversible_metropolisGaussian hK _ _)
    (smallSets_uniformOn_gaussianWeight_nonempty (by omega) hK hK0 hKtop hs) hM hwarm heps0
    heps1
    (conductance_metropolisGaussian_sharp_sqrt_ge hn hσ hδpos le_rfl hR hK hKc hKR hKtop hK0
      hell hfloor hiso) ht

/-- **The same at a general step `δ ≤ σ/(8√n)`, before the cancellation of `σ`.**

`Arlib.MarkovChains.mixesWithin_lazy_of_conductance_sqrt` composed with
`conductance_metropolisGaussian_sharp_sqrt_ge`; the two carry the *same* step cap `hδσ`, so it
passes through for free.  The step count is

    4·(log M + 2·log(1/ε))/(δ·log 2/(640·σ·√n))² + 1,

which at `δ = σ/(8√n)` is the `4·5120²·n²·…` of
`mixesWithin_lazy_metropolisGaussian_at_operative_step`. -/
theorem mixesWithin_lazy_metropolisGaussian_sqrt (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) →
      δ * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (metropolisGaussian K δ (σ ^ 2)))
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K)
      mu0 t (ENNReal.ofReal eps) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  haveI := isProbabilityMeasure_uniformOn_gaussianWeight hK hK0 hKtop hs
  exact mixesWithin_lazy_of_conductance_sqrt hn hσ hδ hδσ
    (isReversible_metropolisGaussian hK _ _)
    (smallSets_uniformOn_gaussianWeight_nonempty (by omega) hK hK0 hKtop hs) hM hwarm heps0
    heps1
    (conductance_metropolisGaussian_sharp_sqrt_ge hn hσ hδ hδσ hR hK hKc hKR hKtop hK0 hell
      hfloor hiso) ht

/-! ## 3. The plain chain, with `hpsd` carried honestly

`Arlib.MarkovChains.mixesWithin_at_operative_step` drops the factor `4` but needs
`HasNonnegSpectrum P pi`.  That hypothesis is **not** removable — `ConductanceToTV.lean:229–243`
exhibits a reversible kernel with `Φ = 1` that never mixes — and nothing in this repository
proves it for `metropolisGaussian`.  It is therefore an explicit binder below, and these two
theorems have **two** unproved binders (`hiso` and `hpsd`) where the lazy ones have one. -/

/-- **The plain-chain counterpart of `mixesWithin_lazy_metropolisGaussian_at_operative_step`:**
`5120²·n²·(log M + 2·log(1/ε))/(log 2)² + 1` steps, one quarter of the lazy deadline, at the
cost of the spectral binder `hpsd`. -/
theorem mixesWithin_metropolisGaussian_at_operative_step (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδop : δ = σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hpsd : HasNonnegSpectrum (metropolisGaussian K δ (σ ^ 2)) (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K))
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) →
      δ * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin (metropolisGaussian K δ (σ ^ 2))
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K)
      mu0 t (ENNReal.ofReal eps) := by
  subst hδop
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hδpos : 0 < σ / (8 * Real.sqrt n) := by positivity
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  haveI := isProbabilityMeasure_uniformOn_gaussianWeight hK hK0 hKtop hs
  exact mixesWithin_at_operative_step hn hσ (isReversible_metropolisGaussian hK _ _) hpsd
    (smallSets_uniformOn_gaussianWeight_nonempty (by omega) hK hK0 hKtop hs) hM hwarm heps0
    heps1
    (conductance_metropolisGaussian_sharp_sqrt_ge hn hσ hδpos le_rfl hR hK hKc hKR hKtop hK0
      hell hfloor hiso) ht

/-- **The plain-chain counterpart of `mixesWithin_lazy_metropolisGaussian_sqrt`**, at a general
step `δ ≤ σ/(8√n)` and with the spectral binder `hpsd`. -/
theorem mixesWithin_metropolisGaussian_sqrt (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hpsd : HasNonnegSpectrum (metropolisGaussian K δ (σ ^ 2)) (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K))
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) →
      δ * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : (Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin (metropolisGaussian K δ (σ ^ 2))
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K)
      mu0 t (ENNReal.ofReal eps) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  haveI := isProbabilityMeasure_uniformOn_gaussianWeight hK hK0 hKtop hs
  exact mixesWithin_of_conductance_sqrt hn hσ hδ hδσ (isReversible_metropolisGaussian hK _ _)
    hpsd (smallSets_uniformOn_gaussianWeight_nonempty (by omega) hK hK0 hKtop hs) hM hwarm
    heps0 heps1
    (conductance_metropolisGaussian_sharp_sqrt_ge hn hσ hδ hδσ hR hK hKc hKR hKtop hK0 hell
      hfloor hiso) ht

/-! ## 4. Non-vacuity (`CLAUDE.md` §11)

Both lazy theorems quantify over a bundle: a bounded convex body of positive finite volume, a
local-conductance floor, an acceptance floor, a warm start, and an accuracy.  A green build
over an unsatisfiable bundle certifies nothing, so here is one body meeting **all of it at
once** — every binder of `mixesWithin_lazy_metropolisGaussian_at_operative_step` and of
`mixesWithin_lazy_metropolisGaussian_sqrt` *except* `hiso`, simultaneously. -/

/-- **Non-vacuity witness for the lazy theorems.**

Every hypothesis of `mixesWithin_lazy_metropolisGaussian_at_operative_step` and of
`mixesWithin_lazy_metropolisGaussian_sqrt` other than `hiso` is satisfied at

    n = 2,  K = B(0,1/2) ⊆ ℝ²,  δ = 1,  σ = 8√2 (so σ² = 128),  R = 1/2,  θ = 1/4,
    μ₀ = π,  M = 1,  ε = 1/2,

with `ε = 1/2 < 1`, so the conclusion at these parameters is not the trivial `TV ≤ 1`.

This is the body and the floor of
`Arlib.MarkovChains.exists_conductance_metropolisGaussian_sharp_sqrt_witness`
(`MetropolisOverlapSqrt.lean:344`) — `K = B(0,1/2)`, `ℓ ≡ 1/4` on `K` because `K ⊆ B(x,1)` for
every `x ∈ K`, `θ = 1/4` — at the one changed parameter that the *operative* step forces:
`σ = 8√2` rather than `16`, so that `δ = 1` is **equal** to `σ/(8√2)` and not merely below it.
The acceptance floor improves as a result, `a = e^{−1/128} ≥ 127/128`, and the floor test reads
`20·a·(1/4)·(1/4) ≥ 1.24 > 1`.  The step cap `hδσ` of the general-`δ` theorem follows from the
equation, so this one witness serves both.

The warm start is the stationary one, `μ₀ = π` with `M = 1`: it is the honest minimal choice,
and it is a genuine `IsWarm (ENNReal.ofReal 1) π π`, not a vacuous instance — `π` here really
is a probability measure (`isProbabilityMeasure_uniformOn_gaussianWeight`), which is exactly
what a positive finite `volume K` buys.

**What this does NOT certify.**  `hiso` is a binder of every theorem in this file and is not
exhibited here.  So this witness shows the theorems are not vacuous *for reasons of their
discharged hypotheses*; by itself it does **not** show they have an unconditional instance,
and it is **not** evidence for any running-time claim.

⚠ **An unconditional instance now exists.**  `hiso` is proved for convex `K`
(`Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`, `Arlib/Convexity/OneDimSharp.lean`), and
`Arlib.MarkovChains.exists_mixesWithin_lazy_metropolisGaussian_uncond_witness`
(`MetropolisMixingUncond.lean`) discharges **every** hypothesis on this same data — `n = 2`,
`K = B(0,1/2)`, `δ = 1`, `σ = 8√2` — and derives the `MixesWithin` conclusion outright.  The
"not evidence for any running-time claim" caveat stands unchanged: mixing is not a step
cost. -/
theorem exists_mixesWithin_lazy_metropolisGaussian_witness :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2))) (σ δ R θ : ℝ)
      (mu0 : Measure (EuclideanSpace ℝ (Fin 2))) (M eps : ℝ) (t : ℕ),
      0 < σ ∧ 0 < δ ∧ δ = σ / (8 * Real.sqrt ((2 : ℕ) : ℝ)) ∧
      δ ≤ σ / (8 * Real.sqrt ((2 : ℕ) : ℝ)) ∧ 0 ≤ R ∧
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧
      volume K ≠ ⊤ ∧ volume K ≠ 0 ∧
      (∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x) ∧
      1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ ∧
      IsProbabilityMeasure mu0 ∧ 1 ≤ M ∧
      IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity (gaussianWeight (σ ^ 2))) K) ∧
      0 < eps ∧ eps ≤ 1 ∧ eps < 1 ∧
      4 * (5120 ^ 2 * (((2 : ℕ)) : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2) + 1 ≤ (t : ℝ) ∧
      4 * ((Real.log M + 2 * Real.log (1 / eps))
        / (δ * Real.log 2 / (640 * σ * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2) + 1 ≤ (t : ℝ) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 (1 / 2) with hKdef
  have hcast2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσpos : (0 : ℝ) < 8 * Real.sqrt 2 := by linarith
  have hσsq : (8 * Real.sqrt 2 : ℝ) ^ 2 = 128 := by rw [mul_pow, hsq2]; norm_num
  have hspos : (0 : ℝ) < (8 * Real.sqrt 2 : ℝ) ^ 2 := by rw [hσsq]; norm_num
  -- the step `δ = 1` **is** the operative step at `σ = 8√2`
  have hδop : (1 : ℝ) = 8 * Real.sqrt 2 / (8 * Real.sqrt ((2 : ℕ) : ℝ)) := by
    rw [hcast2]; exact (div_self (ne_of_gt hσpos)).symm
  -- geometry of `K = B(0,1/2)`, verbatim from the conductance witness
  have hVpos : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hK0 : volume K ≠ 0 := (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hKtop : volume K ≠ ⊤ := measure_ball_lt_top.ne
  have hKc : Convex ℝ K := convex_ball _ _
  have hKR : ∀ x ∈ K, ‖x‖ ≤ 1 / 2 := by
    intro x hx
    rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hx
    exact hx.le
  have hell : ∀ x ∈ K, ell K (1 : ℝ) x = ENNReal.ofReal (1 / 4) := by
    intro x hx
    have hxnorm : ‖x‖ < 1 / 2 := by
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hx; exact hx
    have hsub : K ⊆ Metric.ball x 1 := by
      intro y hy
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hy
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
        _ < 1 := by linarith
    have hball : volume K
        = ENNReal.ofReal (1 / 4) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      rw [hKdef, Measure.addHaar_ball_of_pos volume 0 (by norm_num : (0:ℝ) < 1 / 2),
        finrank_euclideanSpace_fin]
      norm_num
    rw [ell_apply, Set.inter_eq_self_of_subset_right hsub, hball, volume_ball_eq x 1]
    exact ENNReal.mul_div_cancel_right hVpos hVtop
  -- the acceptance floor at `σ² = 128`: `a = e^{-1/128} ≥ 127/128`, and `20·a/16 ≥ 1.24`
  have hexpge : (127 : ℝ) / 128
      ≤ Real.exp (-(2 * (1 / 2 : ℝ) * 1 + (1 : ℝ) ^ 2) / (2 * (8 * Real.sqrt 2 : ℝ) ^ 2)) := by
    have h := Real.add_one_le_exp (-(1 : ℝ) / 128)
    have heq : -(2 * (1 / 2 : ℝ) * 1 + (1 : ℝ) ^ 2) / (2 * (8 * Real.sqrt 2 : ℝ) ^ 2)
        = -(1 : ℝ) / 128 := by rw [hσsq]; norm_num
    rw [heq]; linarith
  have hfloor : (1 : ℝ) ≤ 20
      * Real.exp (-(2 * (1 / 2 : ℝ) * 1 + (1 : ℝ) ^ 2) / (2 * (8 * Real.sqrt 2 : ℝ) ^ 2))
      * (1 / 4) * (1 / 4) := by linarith
  haveI hprob := isProbabilityMeasure_uniformOn_gaussianWeight
    (K := K) measurableSet_ball hK0 hKtop hspos
  have hwarm : IsWarm (ENNReal.ofReal 1) (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity
        (gaussianWeight ((8 * Real.sqrt 2 : ℝ) ^ 2))) K) (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity
        (gaussianWeight ((8 * Real.sqrt 2 : ℝ) ^ 2))) K) := by
    intro S _
    exact le_of_eq (by rw [ENNReal.ofReal_one, one_mul])
  obtain ⟨t, ht⟩ := exists_nat_ge (max
    (4 * (5120 ^ 2 * (((2 : ℕ)) : ℝ) ^ 2 * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ)))
      / Real.log 2 ^ 2) + 1)
    (4 * ((Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ)))
      / ((1 : ℝ) * Real.log 2 / (640 * (8 * Real.sqrt 2 : ℝ)
        * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2) + 1))
  exact ⟨K, 8 * Real.sqrt 2, 1, 1 / 2, 1 / 4, Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity
        (gaussianWeight ((8 * Real.sqrt 2 : ℝ) ^ 2))) K, 1, 1 / 2, t,
    hσpos, by norm_num, hδop, le_of_eq hδop, by norm_num, measurableSet_ball, hKc, hKR,
    hKtop, hK0, fun x hx => (hell x hx).ge, hfloor, hprob, le_rfl, hwarm, by norm_num,
    by norm_num, by norm_num, le_trans (le_max_left _ _) ht, le_trans (le_max_right _ _) ht⟩

end Arlib.MarkovChains

/-! ### Axiom audit (`CLAUDE.md` §4) -/

#print axioms Arlib.MarkovChains.isProbabilityMeasure_uniformOn_gaussianWeight
#print axioms Arlib.MarkovChains.smallSets_uniformOn_gaussianWeight_nonempty
#print axioms Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_at_operative_step
#print axioms Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_sqrt
#print axioms Arlib.MarkovChains.mixesWithin_metropolisGaussian_at_operative_step
#print axioms Arlib.MarkovChains.mixesWithin_metropolisGaussian_sqrt
#print axioms Arlib.MarkovChains.exists_mixesWithin_lazy_metropolisGaussian_witness
