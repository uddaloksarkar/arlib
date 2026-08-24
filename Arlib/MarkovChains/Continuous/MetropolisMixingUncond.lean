/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.MetropolisMixing
import Arlib.Convexity.OneDimSharp
import Arlib.Convexity.GaussianCooling.PhaseMeanRoute

/-!
# The Metropolis-filtered Gaussian ball walk mixes in `O(n²)` steps — with no `hiso` binder

`Arlib/MarkovChains/Continuous/MetropolisMixing.lean` proved that the Metropolis-filtered
Gaussian ball walk on a bounded convex body mixes in `O(n²·(log M + log(1/ε)))` steps, but
every theorem there carried `hiso` — Cousins–Vempala's `thm:iso` in the exact shape
`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge` consumes it — as an
**unproved binder**.  That binder has since been discharged:
`Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` (`Arlib/Convexity/OneDimSharp.lean:1040`)
proves it character for character, from the one-dimensional inequality `(1d-2)` at
`√(2/π) ≈ 0.7979 > ln 2 ≈ 0.6931`, and
`Arlib.conductance_metropolisGaussian_sharp_sqrt_ge_of_convex` (`OneDimSharp.lean:1073`) is the
conductance bound with `hiso` gone.

This file is the propagation of that discharge to the mixing statements, and nothing else.
Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here, and
every proof is a single application of the corresponding `hiso`-carrying theorem with
`Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` supplied for that binder.

## ⚠ "Unconditional" here means `hiso`-unconditional, and **nothing more**

Every theorem below still carries the local-conductance pair

    hell   : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x
    hfloor : 1 ≤ 20 · e^{-(2Rδ+δ²)/(2σ²)} · (1/4) · θ

and `Arlib/MarkovChains/Continuous/EllFloor.lean` **refutes that pair, by machine-checked
counterexample, on the class the Gaussian-cooling consumer needs**
(`Ttc/Volume/CVInstantiate.lean:148,153`: all convex `K` with `ball 0 1 ⊆ K`).  `hfloor`
forces `θ ≥ 1/5`; the cube `[-1,1]ⁿ` is in that class and has `ell ≤ 2⁻ⁿ` at its corner
(`two_pow_mul_ell_cube_corner_le_one`); hence
`metropolis_ell_floor_unsatisfiable_on_cube` — no `θ` meets both from `n = 3` on.

So these theorems apply only to bodies with **no corner at scale `δ`**, and the §4 witness is
`K = B(0,1/2) ⊆ ℝ²` with `δ = 1`, a body *contained in the proposal ball*, which violates the
consumer's `ball 0 1 ⊆ K`.  Read `AUDIT.md` §0i before quoting anything here as a step toward
a running time.  What survives on the whole class is the **average** of `ℓ`
(`isSmooth_of_ball_subset`), not its infimum.

## What is proved

*The lazy chain (§1), unconditionally.*

* `mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex` — at the operative step
  `δ = σ/(8√n)`,

      4·5120²·n²·(log M + 2·log(1/ε))/(log 2)² + 1     steps suffice;

* `mixesWithin_lazy_metropolisGaussian_sqrt_of_convex` — the same at a general step
  `δ ≤ σ/(8√n)`, before the cancellation of `σ`.

*The plain chain (§2).*  `mixesWithin_metropolisGaussian_at_operative_step_of_convex` and
`mixesWithin_metropolisGaussian_sqrt_of_convex` — the same counts without the factor `4`, at
the cost of the spectral binder `hpsd` (see below).

*The Gaussian-cooling consequence (§3).*
`mixesWithin_lazy_metropolisGaussian_coolLaw_of_convex` and
`abs_integral_phaseScore_sub_ratio_le_of_mixing_of_convex` — the phase-law forms from
`Arlib/Convexity/GaussianCooling/PhaseMeanRoute.lean`, likewise with `hiso` gone.

*Non-vacuity (§4).*  `exists_mixesWithin_lazy_metropolisGaussian_uncond_witness` — one concrete
body satisfying **every** binder of both lazy theorems of §1 simultaneously, together with the
resulting `MixesWithin` conclusion.  Since `hiso` is no longer a binder, this is a genuinely
*unconditional* instance: nothing is left over.

## The conclusions are unchanged

Each theorem below has, character for character, the conclusion of the `hiso`-carrying theorem
it replaces, and the same binders **except**:

* `hiso` is **removed**;
* `hRσ : √3·R ≤ 2σ√n` is **added** — it is the one hypothesis
  `Arlib.conductance_metropolisGaussian_sharp_sqrt_ge_of_convex` needs beyond those of
  `conductance_metropolisGaussian_sharp_sqrt_ge`, a compatibility between the bounding radius
  of `K` and the Gaussian scale.  It is implied by the usual normalisation `R ≤ σ√n`.

Nothing else moves: not the step counts, not the warm-start or accuracy binders, not the
geometry of `K`, not the two floors `hell`/`hfloor`.

## What is still carried

`hpsd : HasNonnegSpectrum (metropolisGaussian K δ σ²) π` — **plain chain only, §2**.  It is
genuinely unproved for this kernel and it is **not** removable in general:
`ConductanceToTV.lean:229–243` records the swap kernel on `Bool`, reversible with `Φ = 1`,
whose decay bound is false.  The lazy theorems of §1 need no spectral hypothesis — that is why
the lazy versions are the ones that close outright, at exactly four times the deadline.

Everything else is data a caller supplies: the geometry of `K` (`hK`, `hKc`, `hKR`, `hKtop`,
`hK0`, `hRσ`), the local-conductance floor `hell`, the acceptance floor `hfloor`, the warm
start `hM`/`hwarm`, and the accuracy `0 < ε ≤ 1`.

## Scope: this is a Markov-chain mixing statement, and nothing more

The conclusion is `MixesWithin`: the law of the chain after `t` steps is within total variation
`ε` of its stationary law.  **It is not a running-time statement.**  In particular it says
nothing about TTC, about the charged cost model, or about any `O(m·n⁴)` bound; no count of
arithmetic operations, oracle calls or samples appears anywhere in it, and the step count must
not be quoted as one.  Several layers between "this chain mixes" and any end-to-end running
time — the cost of one step, the cooling schedule's phase count, the estimator's sample
complexity, and the reduction from TTC — remain open in this repository.  Discharging `hiso`
removed the last *conditional* in the conductance-to-mixing chain; it did not shorten that
list.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The lazy chain, unconditionally

`Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_at_operative_step`
(`MetropolisMixing.lean:161`) and `..._sqrt` (`:213`) with their `hiso` binder supplied by
`Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`. -/

/-- **The Metropolis-filtered Gaussian ball walk on a bounded convex body mixes in `O(n²)`
steps (lazy chain) — no isoperimetric hypothesis.**

`Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_at_operative_step` with `hiso`
discharged by `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`.  The conclusion and every
other binder are unchanged; the single added hypothesis is `hRσ : √3·R ≤ 2σ√n`, which the
discharge needs and which `R ≤ σ√n` implies.

At the operative step `δ = σ/(8√n)` the certified conductance is `log 2/(5120·n)` — `σ` has
cancelled — and

    4·5120²·n²·(log M + 2·log(1/ε))/(log 2)² + 1

steps of `lazy (metropolisGaussian K δ σ²)` bring an `M`-warm start within total variation `ε`
of the stationary law `Arlib.uniformOn (volume.withDensity (gaussianWeight σ²)) K`.  The
factor `4` is `Arlib.MarkovChains.conductance_lazy`'s exact halving of the conductance; it is
the price of not assuming `HasNonnegSpectrum`.

**Every binder of this theorem is discharged simultaneously by
`exists_mixesWithin_lazy_metropolisGaussian_uncond_witness` (§4)**, so the statement is not
vacuous.

**This is not a running-time statement.**  See the module docstring. -/
theorem mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδop : δ = σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n)
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
      mu0 t (ENNReal.ofReal eps) :=
  mixesWithin_lazy_metropolisGaussian_at_operative_step hn hσ hδop hR hK hKc hKR hKtop hK0
    hell hfloor
    (Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo hn hσ hK hKc hKR hKtop hK0 hRσ)
    hM hwarm heps0 heps1 ht

/-- **The same at a general step `δ ≤ σ/(8√n)`, before the cancellation of `σ`.**

`Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_sqrt` with `hiso` discharged; the step
count

    4·(log M + 2·log(1/ε))/(δ·log 2/(640·σ·√n))² + 1

is unchanged, and at `δ = σ/(8√n)` it is the `4·5120²·n²·…` of
`mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex`. -/
theorem mixesWithin_lazy_metropolisGaussian_sqrt_of_convex (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n)
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
      mu0 t (ENNReal.ofReal eps) :=
  mixesWithin_lazy_metropolisGaussian_sqrt hn hσ hδ hδσ hR hK hKc hKR hKtop hK0 hell hfloor
    (Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo hn hσ hK hKc hKR hKtop hK0 hRσ)
    hM hwarm heps0 heps1 ht

/-! ## 2. The plain chain, with `hpsd` still carried honestly

`hiso` goes; `hpsd : HasNonnegSpectrum …` stays.  It is **not** removable —
`ConductanceToTV.lean:229–243` exhibits a reversible kernel with `Φ = 1` that never mixes — and
nothing in this repository proves it for `metropolisGaussian`.  These two theorems therefore
have exactly **one** unproved binder each, where before they had two. -/

/-- **The plain-chain counterpart of
`mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex`:**
`5120²·n²·(log M + 2·log(1/ε))/(log 2)² + 1` steps, one quarter of the lazy deadline, at the
cost of the spectral binder `hpsd`.  `hiso` is discharged; `hpsd` is not, and no attempt is
made here to discharge it. -/
theorem mixesWithin_metropolisGaussian_at_operative_step_of_convex (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδop : δ = σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hpsd : HasNonnegSpectrum (metropolisGaussian K δ (σ ^ 2)) (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K))
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n)
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
      mu0 t (ENNReal.ofReal eps) :=
  mixesWithin_metropolisGaussian_at_operative_step hn hσ hδop hR hK hKc hKR hKtop hK0 hell
    hfloor hpsd
    (Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo hn hσ hK hKc hKR hKtop hK0 hRσ)
    hM hwarm heps0 heps1 ht

/-- **The plain-chain counterpart of `mixesWithin_lazy_metropolisGaussian_sqrt_of_convex`**, at
a general step `δ ≤ σ/(8√n)` and with the spectral binder `hpsd` still carried. -/
theorem mixesWithin_metropolisGaussian_sqrt_of_convex (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hpsd : HasNonnegSpectrum (metropolisGaussian K δ (σ ^ 2)) (Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σ ^ 2))) K))
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n)
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
      mu0 t (ENNReal.ofReal eps) :=
  mixesWithin_metropolisGaussian_sqrt hn hσ hδ hδσ hR hK hKc hKR hKtop hK0 hell hfloor hpsd
    (Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo hn hσ hK hKc hKR hKtop hK0 hRσ)
    hM hwarm heps0 heps1 ht

/-! ## 4. Non-vacuity — now an *unconditional* instance (`CLAUDE.md` §11)

`Arlib.MarkovChains.exists_mixesWithin_lazy_metropolisGaussian_witness`
(`MetropolisMixing.lean:382`) exhibited one body meeting every binder of the two lazy mixing
theorems **except `hiso`**, and said so: it showed those theorems were not vacuous *for reasons
of their discharged hypotheses*, but not that they had an unconditional instance.

With `hiso` gone from §1, the same data closes the gap.  The one thing to check is the added
binder `hRσ : √3·R ≤ 2σ√n`, which at `R = 1/2`, `σ = 8√2`, `n = 2` reads `√3/2 ≤ 32` — true
with enormous room.  So the witness below discharges **every** hypothesis of
`mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex` and of
`mixesWithin_lazy_metropolisGaussian_sqrt_of_convex`, with nothing left over, and it therefore
carries the `MixesWithin` conclusion itself as its last conjunct. -/

/-- **Unconditional non-vacuity witness for the lazy theorems of §1.**

Every hypothesis of `mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex` and of
`mixesWithin_lazy_metropolisGaussian_sqrt_of_convex` — `hiso` is no longer among them — is
satisfied at

    n = 2,  K = B(0,1/2) ⊆ ℝ²,  δ = 1,  σ = 8√2 (so σ² = 128),  R = 1/2,  θ = 1/4,
    μ₀ = π,  M = 1,  ε = 1/2,

with `ε = 1/2 < 1`, so the conclusion at these parameters is not the trivial `TV ≤ 1`.

This is the body and the floor of
`Arlib.MarkovChains.exists_mixesWithin_lazy_metropolisGaussian_witness`
(`MetropolisMixing.lean:382`) — `K = B(0,1/2)`, `ℓ ≡ 1/4` on `K` because `K ⊆ B(x,1)` for every
`x ∈ K`, `θ = 1/4`, `σ = 8√2` so that `δ = 1` is **equal** to `σ/(8√2)` and not merely below
it, acceptance `a = e^{−1/128} ≥ 127/128` and floor test `20·a·(1/4)·(1/4) ≥ 1.24 > 1` — with
the one new binder checked: `hRσ` reads `√3·(1/2) ≤ 2·(8√2)·√2 = 32`.  The step cap `hδσ` of
the general-`δ` theorem follows from the equation, so this one witness serves both.

The warm start is the stationary one, `μ₀ = π` with `M = 1`: the honest minimal choice, and a
genuine `IsWarm (ENNReal.ofReal 1) π π` — `π` here really is a probability measure
(`isProbabilityMeasure_uniformOn_gaussianWeight`), which is exactly what a positive finite
`volume K` buys.

**What this now certifies, and what it still does not.**  Unlike its `hiso`-carrying
predecessor, this witness leaves *no* hypothesis unexhibited: the final conjunct is the
`MixesWithin` conclusion itself, obtained by applying
`mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex` to the exhibited data.  The
mixing theorems of §1 therefore have a genuine unconditional instance.  It remains **not**
evidence for any running-time claim — see the module docstring. -/
theorem exists_mixesWithin_lazy_metropolisGaussian_uncond_witness :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2))) (σ δ R θ : ℝ)
      (mu0 : Measure (EuclideanSpace ℝ (Fin 2))) (M eps : ℝ) (t : ℕ),
      0 < σ ∧ 0 < δ ∧ δ = σ / (8 * Real.sqrt ((2 : ℕ) : ℝ)) ∧
      δ ≤ σ / (8 * Real.sqrt ((2 : ℕ) : ℝ)) ∧ 0 ≤ R ∧
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧
      volume K ≠ ⊤ ∧ volume K ≠ 0 ∧
      (∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x) ∧
      1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ ∧
      Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt ((2 : ℕ) : ℝ) ∧
      IsProbabilityMeasure mu0 ∧ 1 ≤ M ∧
      IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity (gaussianWeight (σ ^ 2))) K) ∧
      0 < eps ∧ eps ≤ 1 ∧ eps < 1 ∧
      4 * (5120 ^ 2 * (((2 : ℕ)) : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2) + 1 ≤ (t : ℝ) ∧
      4 * ((Real.log M + 2 * Real.log (1 / eps))
        / (δ * Real.log 2 / (640 * σ * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2) + 1 ≤ (t : ℝ) ∧
      MixesWithin (lazy (metropolisGaussian K δ (σ ^ 2)))
        (Arlib.uniformOn
          ((volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity (gaussianWeight (σ ^ 2))) K)
        mu0 t (ENNReal.ofReal eps) := by
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
  -- the one new binder: `√3·(1/2) ≤ 2·(8√2)·√2 = 32`
  have hsqrt3 : Real.sqrt 3 ≤ 2 := by
    have h := Real.sqrt_le_sqrt (show (3 : ℝ) ≤ 4 by norm_num)
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hRσ : Real.sqrt 3 * (1 / 2 : ℝ)
      ≤ 2 * (8 * Real.sqrt 2 : ℝ) * Real.sqrt ((2 : ℕ) : ℝ) := by
    rw [hcast2]
    have hcalc : (2 : ℝ) * (8 * Real.sqrt 2) * Real.sqrt 2 = 32 := by
      have h : (2 : ℝ) * (8 * Real.sqrt 2) * Real.sqrt 2
          = 16 * Real.sqrt 2 ^ 2 := by ring
      rw [h, hsq2]; norm_num
    rw [hcalc]; linarith
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
  -- with `hiso` gone, the exhibited data yields the conclusion itself
  have hmix : MixesWithin (lazy (metropolisGaussian K (1 : ℝ) ((8 * Real.sqrt 2 : ℝ) ^ 2)))
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity
          (gaussianWeight ((8 * Real.sqrt 2 : ℝ) ^ 2))) K)
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity
          (gaussianWeight ((8 * Real.sqrt 2 : ℝ) ^ 2))) K) t (ENNReal.ofReal (1 / 2)) :=
    mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex (n := 2) (M := 1)
      (eps := 1 / 2) (θ := 1 / 4) le_rfl hσpos hδop (by norm_num) measurableSet_ball hKc hKR
      hKtop hK0 (fun x hx => (hell x hx).ge) hfloor hRσ le_rfl hwarm (by norm_num) (by norm_num)
      (le_trans (le_max_left _ _) ht)
  exact ⟨K, 8 * Real.sqrt 2, 1, 1 / 2, 1 / 4, Arlib.uniformOn
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity
        (gaussianWeight ((8 * Real.sqrt 2 : ℝ) ^ 2))) K, 1, 1 / 2, t,
    hσpos, by norm_num, hδop, le_of_eq hδop, by norm_num, measurableSet_ball, hKc, hKR,
    hKtop, hK0, fun x hx => (hell x hx).ge, hfloor, hRσ, hprob, le_rfl, hwarm, by norm_num,
    by norm_num, by norm_num, le_trans (le_max_left _ _) ht,
    le_trans (le_max_right _ _) ht, hmix⟩

end Arlib.MarkovChains

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## 3. The Gaussian-cooling consequence

`Arlib/Convexity/GaussianCooling/PhaseMeanRoute.lean` transports the mixing bound onto the
exact phase law `coolLaw` and then into approximate unbiasedness of the phase score.  Both
theorems there carry `hiso`; both lose it here.

*Layering.*  This file sits under `Arlib/MarkovChains/` and imports `Arlib/Convexity/`, which
is the direction that already holds: `Arlib/Convexity/OneDimSharp.lean` imports
`Arlib/MarkovChains/Continuous/MetropolisOverlapSqrt.lean`,
`Arlib/Convexity/IsoIndicator.lean` imports
`Arlib/MarkovChains/Continuous/MetropolisGaussian.lean`, and
`Arlib/Convexity/GaussianCooling/PhaseMeanRoute.lean` imports
`Arlib/MarkovChains/Continuous/MetropolisMixing.lean`.  Nothing imports this file, so no cycle
is created, and no `Ttc.*` module is imported. -/

/-- **The Metropolis-filtered Gaussian ball walk mixes to the phase law — no isoperimetric
hypothesis.**

`Arlib.GaussianCooling.mixesWithin_lazy_metropolisGaussian_coolLaw` with `hiso` discharged by
`Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`.  The conclusion and every other binder are
unchanged; `hRσ : √3·R ≤ 2σ√n` is added.

Still a mixing statement, not a running-time statement. -/
theorem mixesWithin_lazy_metropolisGaussian_coolLaw_of_convex (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσpos : 0 < σ) (hδop : δ = σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ MarkovChains.ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n)
    {mu0 : Measure (EuclSpace n)} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn
      ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight (σ ^ 2))) K))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2) + 1 ≤ (t : ℝ))
    {m : ℕ} {σsq : ℕ → ℝ} (hσsch : ∀ j, 0 < σsq j)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) {i : ℕ} (hi : i < m) (hs : σ ^ 2 = σsq i) :
    MarkovChains.MixesWithin
      (MarkovChains.lazy (MarkovChains.metropolisGaussian K δ (σ ^ 2)))
      (coolLaw m σsq K i) mu0 t (ENNReal.ofReal eps) :=
  mixesWithin_lazy_metropolisGaussian_coolLaw hn hσpos hδop hR hK hKc hKR hKtop hK0 hell hfloor
    (Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo hn hσpos hK hKc hKR hKtop hK0 hRσ)
    hM hwarm heps0 heps1 ht hσsch hball hi hs

/-- **Approximate unbiasedness of the phase score for the chain the algorithm runs — no
isoperimetric hypothesis.**

`Arlib.GaussianCooling.abs_integral_phaseScore_sub_ratio_le_of_mixing` with `hiso` discharged.
After the mixing theorem's step count, the law of the lazy Metropolis-filtered Gaussian ball
walk gives the phase-`i` chain ratio to within `e^{R²/(2σᵢ²)}·ε`.

This is **not** `hphase_mean`, which is an equation: `PhaseMeanRoute.lean` §4 shows no total
variation bound can give the equation.  It still carries `hwarm`. -/
theorem abs_integral_phaseScore_sub_ratio_le_of_mixing_of_convex (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσpos : 0 < σ) (hδop : δ = σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ MarkovChains.ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n)
    {mu0 : Measure (EuclSpace n)} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn
      ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight (σ ^ 2))) K))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2) + 1 ≤ (t : ℝ))
    {m : ℕ} {σsq : ℕ → ℝ} (hσsch : ∀ j, 0 < σsq j)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) {i : ℕ} (hi : i < m) (hs : σ ^ 2 = σsq i) :
    |(∫ x, phaseScore m σsq K i x
        ∂(MarkovChains.iterate
            (MarkovChains.lazy (MarkovChains.metropolisGaussian K δ (σ ^ 2))) mu0 t))
        - chain m σsq K (i + 1) / chain m σsq K i|
      ≤ Real.exp (R ^ 2 / (2 * σsq i)) * eps :=
  abs_integral_phaseScore_sub_ratio_le_of_mixing hn hσpos hδop hR hK hKc hKR hKtop hK0 hell
    hfloor
    (Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo hn hσpos hK hKc hKR hKtop hK0 hRσ)
    hM hwarm heps0 heps1 ht hσsch hball hi hs

end Arlib.GaussianCooling

/-! ### Axiom audit (`CLAUDE.md` §4) -/

#print axioms
  Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex
#print axioms Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_sqrt_of_convex
#print axioms Arlib.MarkovChains.mixesWithin_metropolisGaussian_at_operative_step_of_convex
#print axioms Arlib.MarkovChains.mixesWithin_metropolisGaussian_sqrt_of_convex
#print axioms Arlib.MarkovChains.exists_mixesWithin_lazy_metropolisGaussian_uncond_witness
#print axioms Arlib.GaussianCooling.mixesWithin_lazy_metropolisGaussian_coolLaw_of_convex
#print axioms Arlib.GaussianCooling.abs_integral_phaseScore_sub_ratio_le_of_mixing_of_convex
