/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.SpeedyGaussianMixing
import Arlib.MarkovChains.Continuous.SpeedyToGaussian

/-!
# Mixing to the **Gaussian target**, not to the speedy chain's own law

Two results compose here, and this file does nothing else:

* `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond`
  (`Arlib/Convexity/SpeedyGaussianMixing.lean`) — Cousins–Vempala's `thm:mixing`
  (`1409.6011/vol3_journal.tex:523`) applied to the unconditional conductance bound
  `Arlib.conductance_speedyMetropolisGaussian_ge_uncond`.  Its target is
  `Arlib.MarkovChains.ellGaussianProb K δ σ²`, the **speedy chain's own** stationary law,
  with density `∝ 1_K·ℓ·γ`.
* `Arlib.MarkovChains.tvLe_ellGaussianProb_uniformOn`
  (`Arlib/MarkovChains/Continuous/SpeedyToGaussian.lean`) — Cousins–Vempala's
  `lem:map-speedy-to-ball` (`vol3_journal.tex:942`), Gaussian case: the speedy law is within
  `s/(1−s)` of the **target** `∝ 1_K·γ`, under the Gaussian smoothness hypothesis
  `(1−s)·ν K ≤ ∫_K ℓ·γ`.

`Arlib.TVLe.trans` (`Arlib/Probability/TV.lean:128`) glues them, and `MixesWithin` is by
definition a `TVLe` of the iterate (`Warmness.lean:349`), so the composition is immediate.

## ⚠ The smoothness constant is carried, and it is where the value of this lives

`hsmooth` is a **hypothesis** here.  It is Cousins–Vempala's `lem:lambda-bound`
(`vol3_journal.tex:853`), and this file does not prove it.  That matters quantitatively, not
just bureaucratically:

* `Arlib.MarkovChains.gaussianSmooth_unitBall` (`SpeedyToGaussian.lean`) discharges it on the
  unit ball with `s = 1 − e^{−(1−δ)²/(2σ²)}·(1−δ)ⁿ`.  At the cooling regime's `σ² = Θ(1/n)`
  that constant is **exponentially small in `n`**, so `s/(1−s)` is exponentially large:
  finite, hence the statement is not vacuous, but quantitatively useless.
* The informative constant is CV's `1 − 32·δ^{1/2}n^{1/4}/a^{1/2}`, which comes from the
  ball-convolution smoothing of `lem:lambda-bound` and is **not in this repository**.

So the theorem below is the right *shape* — it is what `hphase_mean` and `hphase_var`
consume — and it is genuinely unconditional in every binder except `hsmooth`.

## ⚠⚠ AND THE ROUTE ITSELF IS A DEAD END FOR THE CONSTANT — read this before building on it

Discharging `hsmooth` will **not** make this bound useful, because this route is not
Cousins–Vempala's and cannot reach their constants.

* What `lem:lambda-bound` delivers is `λ ≥ 1/2` — a *constant below one*, at
  `δ ≤ min{σ,1}/(4096√n)` (`vol3_journal.tex:906`; the paper's displayed arithmetic there is
  correct, and it is **not** applied at `δ = σ/(8√n)`).  Feeding `s = 1/2` into the `s/(1−s)`
  comparison below gives a total-variation bound of `1`, which is free for probability
  measures.  No improvement in `hsmooth` short of `s = o(1)` helps, and `lem:lambda-bound`
  does not give `o(1)` at any `δ = Θ(σ/√n)`.
* Cousins–Vempala use `λ` for something else entirely: the **wasted-step count** of
  `lem:speedy-to-ball` (`:915`), `M·t/λ`.  Their speedy-to-target bridge is
  `lem:map-speedy-to-ball` (`:942`), a **rejection routine** — `c = 1 − 1/(2n)`, draw
  `u ∼ ℓ·f`, set `v = u/c`, accept with probability `f(v)/f(u)` — whose analysis rests on the
  KLS95 shell bound `∫_{μ_L ∩ cK} (1 − ℓ) ≤ ε·vol(μ_L ∩ cK)` and on `Q̂(cK) ≥ 1/2`.
* The decisive detail is the **shrink factor**: CV shrink by `1 − 1/(2n)`, where
  `(1 − 1/(2n))ⁿ → e^{−1/2} = Θ(1)`; the homothety route available here shrinks by `1 − δ`
  with `δ = Θ(σ/√n)`, where `(1−δ)ⁿ = e^{−Θ(σ√n)}`.  That substitution, and not the quality
  of any estimate, is the whole difference between a constant and an exponentially small one.

This theorem is therefore retained as a correct composition and as a record of the route, and
should **not** be quoted as progress toward a running time.  The replacement is CV's rejection
argument, which is not in this repository.

## What is proved here

* `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_target` — mixing of the lazy speedy
  Metropolis–Gaussian chain to `uniformOn (volume.withDensity (gaussianWeight σ²)) K`, at
  tolerance `ε + s/(1−s)`.

## Scope

A total-variation bound, not a running time.  The cost of one speedy step is bounded nowhere
in this repository (that is CV's `lem:speedy-to-ball`, `vol3_journal.tex:915`), so **nothing
here may be quoted as a polynomial-time claim**.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib

open MeasureTheory Arlib.MarkovChains
open scoped ENNReal

variable {n : ℕ}

/-- **The lazy speedy Metropolis–Gaussian chain mixes to the Gaussian target `∝ 1_K·γ`.**

`Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond` composed with
`Arlib.MarkovChains.tvLe_ellGaussianProb_uniformOn` through `Arlib.TVLe.trans`.

Every binder is unconditional except `hsmooth`, which is Cousins–Vempala's `lem:lambda-bound`
and is **carried, not proved** — see the module docstring for why the only constant currently
available for it is exponentially small in the cooling regime, and therefore why this bound is
of the right shape but not yet of a useful size.

The step count is that of the mixing theorem, unchanged; the transfer costs accuracy
(`ε ↦ ε + s/(1−s)`), not steps. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_target (hn : 21 ≤ n) {σ δ R : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n)
    (hνK0 : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (gaussianWeight (σ ^ 2))) K ≠ 0)
    (hνKtop : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (gaussianWeight (σ ^ 2))) K ≠ ⊤)
    {s : ℝ≥0∞}
    (hsmooth : (1 - s) * ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (σ ^ 2))) K
      ≤ ∫⁻ x in K, ell K δ x * gaussianWeight (σ ^ 2) x)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M) (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellGaussianProb K δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyMetropolisGaussian K δ (σ ^ 2)))
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (σ ^ 2))) K)
      mu0 t (ENNReal.ofReal eps + s / (1 - s)) :=
  TVLe.trans
    (mixesWithin_lazy_speedyMetropolisGaussian_uncond hn hσ hδ hδσ hK hKc hK0 hR hKR hRσ
      hM hwarm heps0 heps1 ht)
    (tvLe_ellGaussianProb_uniformOn hK hνK0 hνKtop hsmooth)

section AxiomCheck

#print axioms Arlib.mixesWithin_lazy_speedyMetropolisGaussian_target

end AxiomCheck

end Arlib
