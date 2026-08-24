/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.PhaseMeanApprox
import Arlib.Probability.TVTensor

/-!
# Cousins–Vempala's own route: price the sampler in *failure probability*, not in bias

This file composes three already-proved, axiom-clean facts into the end-to-end statement for
the Gaussian-cooling volume estimator when its samples come from a **finitely-run Markov
chain** rather than from the exact phase law.  Every declaration below is a `theorem`; there
is no `def`, `structure`, `class`, `axiom`, `sorry` or `native_decide` in this file, and
nothing is assumed that is not a binder of a named statement.

## §0.  Two routes, and why this one keeps the exponent

`PhaseMeanApprox.lean` §2 prices a mixing error by pushing it through the *phase mean*: a TV
bound `e` on the sampled law moves `∫ phaseScore` by at most `‖phaseScore‖_∞ · e`, and the
sup norm of the phase-`i` score on a body of radius `R` is `e^{R²/(2σᵢ²)}`.  To buy a
relative bias `η` you must therefore take

    e ≤ η · rᵢ / e^{R²/(2σᵢ²)},   i.e.   log (1/e) = R²/(2σᵢ²) + log (1/η) + log (1/rᵢ)

— which is `Arlib.GaussianCooling.log_one_div_tvBudget_exp`, proved there.  The mixing time is
`Θ(n² (log M + log(1/e)))`, so **that route pays `Θ(n² · R²/(2σᵢ²))` steps per phase**, and
`R²/(2σᵢ²)` is polynomial in `n` on any schedule that actually cools (`σ₀² ≈ 1/n`, `R ≈ n`
after rounding).  Call it **Route A**.

Cousins–Vempala do something else (`1409.6011/vol3_journal.tex:1426-1430`).  They never bound
a mean.  They couple the sampler's output to shadow variables of the *exact* law and charge
the coupling to the **failure probability**, union-bounded over all `k·m` samples at `:1021`.
Total variation transfers a probability *additively* — no sup norm anywhere — so the
per-sample budget only has to beat the *total failure budget divided by the sample count*.
Call it **Route B**; it is what this file assembles.

**The contrast, made explicit** (and it does hold — see file section 4):

* **Route A** (`PhaseMeanApprox` §2).  Admissible per-sample TV `e = η·rᵢ·e^{-R²/(2σᵢ²)}`,
  so `log(1/e) = R²/(2σᵢ²) + log(1/η) + log(1/rᵢ)`, so `Θ(n²(log M + R²/(2σᵢ²)))` steps.
* **Route B** (here, file section 4).  Admissible per-sample TV `e = ρ/(r·m)`,
  so `log(1/e) = log(r·m/ρ)`, so `Θ(n²(log M + log(r·m/ρ)))` steps.

Route A's `R²/(2σᵢ²)` is *polynomial in `n`*; Route B's `log(r·m/ρ)` is *logarithmic in the
sample count and in the inverse failure budget*.  With `r = Θ(log(1/p))`, `m = Θ(√n log n)`
that is `O(log n + log log(1/p) + log(1/ρ))`, so the per-phase cost stays `O*(n²)`.  That is
the entire reason the coupling route exists, and nothing below weakens it.

## §1.  The three inputs, all proved elsewhere and all axiom-clean

1. **Per-sample TV bound** — `Arlib.GaussianCooling.mixesWithin_lazy_metropolisGaussian_coolLaw`
   (`PhaseMeanRoute.lean:285`): the lazy Metropolis–Gaussian chain, started warm and run for
   `t ≥ 4·(5120²·n²·(log M + 2 log(1/e))/log²2) + 1` steps, is within TV `e` of the **exact
   phase law** `coolLaw`.  `MixesWithin` unfolds to `TVLe (iterate P μ₀ t) coolLaw e`, i.e.
   the *realised* law on the left — exactly the orientation §2 below consumes.
2. **Union bound** — `Arlib.tvLe_pi_pi` / `Arlib.tvLe_pi_pi_const` (`TVTensor.lean:307,317`):
   `r·m` coordinates each within `e` put the joint law within `(r·m)·e`.
   `IsProbabilityMeasure` on **all** factors is load-bearing; see that file's counterexample.
3. **Transfer to a probability** — `Arlib.GaussianCooling.measureReal_relErr_ge_of_tvLe`
   (`PhaseMeanApprox.lean:541`), packaged over the run space as
   `Arlib.le_measureReal_of_tvLe_pi_pi` (`TVTensor.lean:336`).

(2) feeds (3) with **no adapter**: `Arlib.Probability.runMeasure ν` (`RunPlumbing.lean:325`)
is *by definition* `Measure.pi fun j => Measure.pi fun i => ν j i`.

## §2.  What is proved here

* `setOf_abs_sub_le_eq_relErr` — the event-shape bridge: `|V − vol| ≤ acc·vol` is literally
  `(1−acc)·vol ≤ V ∧ V ≤ (1+acc)·vol`, which is the shape the estimator's accuracy guarantee
  produces.  Unconditional; no sign hypothesis on `vol`.
* `le_measureReal_runMeasure_of_tvLe` / `..._of_tvLe_const` — the **abstract composition**:
  per-sample TV bounds cost the success probability `∑ⱼ∑ᵢ eⱼᵢ` (resp. `(r·m)·b`) and nothing
  else.  No radius, no schedule, no bound on the estimator, no sup norm.
* `le_measureReal_runMeasure_mem_relErr_of_tvLe` — the same in the two-sided event shape.
* `le_measureReal_runMeasure_of_failure_budget` — the same with the failure budget named `ρ`.
* `le_measureReal_runMeasure_metropolisGaussian` — the **instantiation**: `ν j i` is the
  actual lazy Metropolis–Gaussian chain's law after `t` steps, `ν' j i` is `coolLaw`.
* `le_measureReal_runMeasure_metropolisGaussian_budget` — the same with the step count
  written in terms of the *total* failure budget `ρ`, exhibiting `log(r·m/ρ)`.
* `exists_couplingRoute_witness` — non-vacuity (`CLAUDE.md` §11) for the abstract layer, at a
  **strictly positive** per-sample budget and with the realised and exact laws provably
  **different**.

## §3.  The `q` is left abstract, and here is exactly what supplies it

The exact-law success probability `q` is *not* proved in `Arlib`.  It is proved on the `Ttc`
side, by

    `Ttc.CVEst.volume_accuracy_of_samples`   (`Ttc/Volume/CVEstimator.lean:582`)

which concludes, over an **arbitrary** probability space `μ`,

    `1 − p ≤ μ.real {ω | (1 − ε₀)·Vol(K) ≤ z ω ∧ z ω ≤ (1 + ε₀)·Vol(K)}`

— i.e. `q = 1 − p`, in precisely the two-sided event shape that
`le_measureReal_runMeasure_mem_relErr_of_tvLe` consumes, and instantiable at
`μ := Arlib.Probability.runMeasure ν'` with `ν' j i := coolLaw m σsq K i`.  Composing the two
is a one-line `Ttc`-side step.  **`Arlib/**` may not import `Ttc.*`** (`lakefile.toml`), so it
is not taken here and `q` stays a binder.  (`Ttc.CVEst.median_accuracy_of_samples`,
`CVEstimator.lean:545`, is the same statement before the `A m = Vol(K)` endpoint
identification, if the caller prefers to keep that idealization separate.)

## §4.  Scope, stated honestly (`CLAUDE.md` §6)

This is a statement about a **Markov-chain-driven estimator's success probability**.  It is
*not* a running-time claim about TTC, *not* an `O(m·n⁴)` claim, and *not* a proof that any
particular schedule is admissible.  The step count in file section 4 is the *hypothesis*
`ht` of the mixing theorem, carried through verbatim; nothing here proves a chain exists meeting
it on a body of interest, and nothing here bounds the cost of one Metropolis step.

The instantiation carries `hiso` (an isoperimetric inequality for the Gaussian-tilted
indicator of `K`) and `hwarm` (a warm start) as binders.  See file section 5 for what the
non-vacuity witness does and does not cover.

⚠ **`hiso` is proved.**  `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`
(`Arlib/Convexity/OneDimSharp.lean`) discharges it for convex `K` given
`hRσ : √3·R ≤ 2σ√n`.  This file predates that, so §3 and §4 below still carry it; the
`_of_convex` versions in `Arlib/Convexity/GaussianCooling/CouplingRouteUncond.lean` carry
`hRσ` instead and are the ones to prefer.  `hwarm` remains a binder on both.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## 1.  The event-shape bridge

The transfer lemma of `PhaseMeanApprox.lean` is stated on `{ω | |V ω − vol| ≤ acc·vol}`; every
accuracy guarantee in this development is stated as the two-sided conjunction.  They are the
same set, unconditionally — in particular no `0 ≤ vol` is needed, because both sides degrade
the same way when `vol < 0`. -/

/-- **The relative-error event, two ways.**  `|V − vol| ≤ acc·vol` and
`(1 − acc)·vol ≤ V ≤ (1 + acc)·vol` are the same set of points, for every real `vol` and
`acc`.  Pure `abs_le` plus arithmetic; no hypotheses. -/
theorem setOf_abs_sub_le_eq_relErr {Ω : Type*} (V : Ω → ℝ) (vol acc : ℝ) :
    {ω | |V ω - vol| ≤ acc * vol}
      = {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} := by
  ext ω
  simp only [Set.mem_setOf_eq, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

/-! ## 2.  The abstract composition: union bound, then transfer

Nothing in this section knows what a Markov chain, a convex body or a schedule is.  It is the
union bound of `vol3_journal.tex:1021` composed with the definition of total variation, over
the run space of `RunPlumbing.lean`. -/

variable {r m : ℕ} {E : Type*} [MeasurableSpace E]

/-- **Route B, abstractly: `r·m` per-sample TV bounds cost `∑ⱼ∑ᵢ eⱼᵢ` of success
probability, and nothing else.**

If the estimator `V` is `acc`-relatively accurate for `vol` with probability at least `q`
when every coordinate is drawn from its *exact* law `ν' j i`, then it is `acc`-accurate with
probability at least `q − ∑ⱼ∑ᵢ eⱼᵢ` when coordinate `(j, i)` is instead drawn from any `ν j i`
within total variation `e j i` of `ν' j i`.

There is no radius, no schedule, no sup norm of the estimator and no bound on `V` — that
absence is the whole point of the coupling route (§0).  This is
`Arlib.le_measureReal_of_tvLe_pi_pi` restated over `Arlib.Probability.runMeasure`, which is
*definitionally* the iterated `Measure.pi` that theorem is stated on. -/
theorem le_measureReal_runMeasure_of_tvLe {ν ν' : Fin r → Fin m → Measure E}
    [hν : ∀ j i, IsProbabilityMeasure (ν j i)] [hν' : ∀ j i, IsProbabilityMeasure (ν' j i)]
    {e : Fin r → Fin m → ℝ≥0∞} (h : ∀ j i, TVLe (ν j i) (ν' j i) (e j i))
    (he : (∑ j, ∑ i, e j i) ≠ ⊤)
    {V : Arlib.Probability.RunSpace E r m → ℝ} (hV : Measurable V) {vol acc q : ℝ}
    (hgood : q ≤ (Arlib.Probability.runMeasure ν').real {ω | |V ω - vol| ≤ acc * vol}) :
    q - (∑ j, ∑ i, e j i).toReal
      ≤ (Arlib.Probability.runMeasure ν).real {ω | |V ω - vol| ≤ acc * vol} :=
  Arlib.le_measureReal_of_tvLe_pi_pi h he hV hgood

/-- **Cousins–Vempala's `k·m·ν`, on the success probability.**  A *uniform* per-sample budget
`b` over `r` runs of `m` phases costs `(r·m)·b` of success probability — `:1021` with the
per-sample budget of `:212`, transferred through `:1426-1430`. -/
theorem le_measureReal_runMeasure_of_tvLe_const {ν ν' : Fin r → Fin m → Measure E}
    [hν : ∀ j i, IsProbabilityMeasure (ν j i)] [hν' : ∀ j i, IsProbabilityMeasure (ν' j i)]
    {b : ℝ≥0∞} (hb : b ≠ ⊤) (h : ∀ j i, TVLe (ν j i) (ν' j i) b)
    {V : Arlib.Probability.RunSpace E r m → ℝ} (hV : Measurable V) {vol acc q : ℝ}
    (hgood : q ≤ (Arlib.Probability.runMeasure ν').real {ω | |V ω - vol| ≤ acc * vol}) :
    q - (r * m : ℕ) * b.toReal
      ≤ (Arlib.Probability.runMeasure ν).real {ω | |V ω - vol| ≤ acc * vol} := by
  have hTV := Arlib.tvLe_pi_pi_const (ν := ν) (ν' := ν') h
  have hne : ((r * m : ℕ) * b) ≠ ⊤ := by finiteness
  have hmain := measureReal_relErr_ge_of_tvLe hTV hne hV hgood
  rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hmain

/-- **The two-sided form**, which is the shape the estimator's accuracy guarantee produces
(`Ttc.CVEst.volume_accuracy_of_samples`, §3 of the module docstring).  Same content as
`le_measureReal_runMeasure_of_tvLe_const`, moved across `setOf_abs_sub_le_eq_relErr`. -/
theorem le_measureReal_runMeasure_mem_relErr_of_tvLe {ν ν' : Fin r → Fin m → Measure E}
    [hν : ∀ j i, IsProbabilityMeasure (ν j i)] [hν' : ∀ j i, IsProbabilityMeasure (ν' j i)]
    {b : ℝ≥0∞} (hb : b ≠ ⊤) (h : ∀ j i, TVLe (ν j i) (ν' j i) b)
    {V : Arlib.Probability.RunSpace E r m → ℝ} (hV : Measurable V) {vol acc q : ℝ}
    (hgood : q ≤ (Arlib.Probability.runMeasure ν').real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol}) :
    q - (r * m : ℕ) * b.toReal ≤ (Arlib.Probability.runMeasure ν).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} := by
  rw [← setOf_abs_sub_le_eq_relErr] at hgood ⊢
  exact le_measureReal_runMeasure_of_tvLe_const hb h hV hgood

/-- **The failure budget, named.**  To lose at most `ρ` of success probability it suffices
that the per-sample budget `b` satisfy `(r·m)·b ≤ ρ` — i.e. `b ≤ ρ/(r·m)`.  This is the
inequality that determines the step count in file section 4. -/
theorem le_measureReal_runMeasure_of_failure_budget {ν ν' : Fin r → Fin m → Measure E}
    [hν : ∀ j i, IsProbabilityMeasure (ν j i)] [hν' : ∀ j i, IsProbabilityMeasure (ν' j i)]
    {b : ℝ≥0∞} (hb : b ≠ ⊤) (h : ∀ j i, TVLe (ν j i) (ν' j i) b)
    {ρ : ℝ} (hρ : (r * m : ℕ) * b.toReal ≤ ρ)
    {V : Arlib.Probability.RunSpace E r m → ℝ} (hV : Measurable V) {vol acc q : ℝ}
    (hgood : q ≤ (Arlib.Probability.runMeasure ν').real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol}) :
    q - ρ ≤ (Arlib.Probability.runMeasure ν).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} := by
  have := le_measureReal_runMeasure_mem_relErr_of_tvLe hb h hV hgood
  linarith

/-! ## 3.  The instantiation: the samples are an actual Markov chain

`ν j i` becomes the law of the lazy Metropolis–Gaussian chain for phase `i` of run `j`,
started at `mu0 j i` and run for `t` steps; `ν' j i` becomes `coolLaw m σsq K i`, the exact
phase law.  Every binder of `mixesWithin_lazy_metropolisGaussian_coolLaw` is carried through,
now quantified over the phase index where it depends on `σᵢ`.

**A single `t` serves all `r·m` samples.**  The mixing theorem's step bound
`4·(5120²·n²·(log M + 2 log(1/eps))/log²2) + 1` depends only on `(n, M, eps)` — not on `i`,
not on `σᵢ`, not on the schedule.  That is why the coupling route's cost is `r·m` times a
single per-sample cost, with no `∑ᵢ` over phase-dependent step counts.

**`hiso` is an unproved binder.**  It is proved nowhere in this repository and is not
attempted here. -/

/-- **Route B, end to end for the Gaussian-cooling estimator.**

Suppose the estimator `V` on the run space is `acc`-relatively accurate for `vol` with
probability at least `q` when every one of the `r·m` coordinates is drawn from the exact
phase law `coolLaw m σsq K i`.  Suppose each coordinate is instead produced by running the
lazy Metropolis–Gaussian chain for phase `i` — kernel
`lazy (metropolisGaussian K (δ i) (σ i ^ 2))` — from an `M`-warm start `mu0 j i` for `t`
steps, with `t` meeting the mixing theorem's bound at TV budget `eps`.

Then the **realised** run succeeds with probability at least `q − (r·m)·eps`.

The bound is additive in the number of samples and carries **no** `e^{R²/(2σᵢ²)}` — contrast
`integral_phaseScore_mem_Icc_of_mixing_steps` (`PhaseMeanApprox.lean`), which does. -/
theorem le_measureReal_runMeasure_metropolisGaussian (hn : 2 ≤ n)
    {σ δ θ : Fin m → ℝ} {R M eps : ℝ}
    (hσpos : ∀ i, 0 < σ i) (hδop : ∀ i, δ i = σ i / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ i, ∀ x ∈ K, ENNReal.ofReal (θ i) ≤ MarkovChains.ell K (δ i) x)
    (hfloor : ∀ i, 1 ≤ 20 * Real.exp (-(2 * R * δ i + δ i ^ 2) / (2 * σ i ^ 2)) * (1 / 4) * θ i)
    (hiso : ∀ i, ∀ S₁ S₂ S₃ : Set (EuclSpace n),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ i * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ i * Real.log 2 / Real.sqrt n / σ i) * Real.sqrt n
            ≤ densDist (Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2))) u v) →
      δ i * Real.log 2 / Real.sqrt n / σ i
          * ((∫ x in S₁, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
        ≤ (∫ x, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
    {mu0 : Fin r → Fin m → Measure (EuclSpace n)}
    [∀ j i, IsProbabilityMeasure (mu0 j i)] (hM : 1 ≤ M)
    (hwarm : ∀ j i, IsWarm (ENNReal.ofReal M) (mu0 j i)
      (Arlib.uniformOn ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight (σ i ^ 2))) K))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2) + 1 ≤ (t : ℝ))
    {σsq : ℕ → ℝ} (hσsch : ∀ j, 0 < σsq j) (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hs : ∀ i : Fin m, σ i ^ 2 = σsq (i : ℕ))
    {V : Arlib.Probability.RunSpace (EuclSpace n) r m → ℝ} (hV : Measurable V)
    {vol acc q : ℝ}
    (hgood : q ≤ (Arlib.Probability.runMeasure
        fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol}) :
    q - (r * m : ℕ) * eps ≤ (Arlib.Probability.runMeasure
        fun (j : Fin r) (i : Fin m) => MarkovChains.iterate
          (MarkovChains.lazy (MarkovChains.metropolisGaussian K (δ i) (σ i ^ 2)))
          (mu0 j i) t).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} := by
  haveI hprob : ∀ (_ : Fin r) (i : Fin m), IsProbabilityMeasure (coolLaw m σsq K (i : ℕ)) :=
    fun _ i => coolLaw_isProbabilityMeasure hσsch hball hKtop _
  have hmix : ∀ (j : Fin r) (i : Fin m),
      TVLe (MarkovChains.iterate
          (MarkovChains.lazy (MarkovChains.metropolisGaussian K (δ i) (σ i ^ 2)))
          (mu0 j i) t) (coolLaw m σsq K (i : ℕ)) (ENNReal.ofReal eps) := by
    intro j i
    exact mixesWithin_lazy_metropolisGaussian_coolLaw hn (hσpos i) (hδop i) hR hK hKc hKR
      hKtop hK0 (hell i) (hfloor i) (hiso i) hM (hwarm j i) heps0 heps1 ht hσsch hball
      i.isLt (hs i)
  have hmain := le_measureReal_runMeasure_mem_relErr_of_tvLe
    (ν := fun (j : Fin r) (i : Fin m) => MarkovChains.iterate
      (MarkovChains.lazy (MarkovChains.metropolisGaussian K (δ i) (σ i ^ 2))) (mu0 j i) t)
    (ν' := fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)) (hν' := hprob)
    (b := ENNReal.ofReal eps) ENNReal.ofReal_ne_top hmix hV hgood
  rwa [ENNReal.toReal_ofReal heps0.le] at hmain

/-! ## 4.  The step count, in terms of the *total* failure budget

Setting the per-sample budget to `eps = ρ/(r·m)` makes the total cost exactly `ρ`, and the
mixing theorem's `log(1/eps)` becomes `log(r·m/ρ)`.

**This is the contrast with Route A, and it holds.**  Route A must take
`log(1/e) = R²/(2σᵢ²) + log(1/η) + log(1/rᵢ)` (`log_one_div_tvBudget_exp`, proved), whose
leading term is `R²/(2σᵢ²)` — polynomial in `n` on any cooling schedule.  Route B takes
`log(1/e) = log(r·m/ρ)` — logarithmic in the sample count and in the inverse failure budget,
with **no dependence on `R`, on `σᵢ`, or on the estimator at all**.  The two `log(1/e)`
values sit in the *same* step bound `4·(5120²·n²·(log M + 2 log(1/e))/log²2) + 1`, so the
comparison is between the two arguments and nothing else. -/

/-- **Route B with the step count written from the failure budget.**  To lose at most `ρ` of
success probability across all `r·m` samples it suffices to run each chain for

    t ≥ 4·(5120²·n²·(log M + 2·log(r·m/ρ))/log²2) + 1

steps.  `log(r·m/ρ)` is logarithmic in the sample count and in `1/ρ`; compare Route A's
`R²/(2σᵢ²)`, which is polynomial in `n` (§0, and `log_one_div_tvBudget_exp`). -/
theorem le_measureReal_runMeasure_metropolisGaussian_budget (hn : 2 ≤ n)
    (hr : 0 < r) (hm : 0 < m)
    {σ δ θ : Fin m → ℝ} {R M ρ : ℝ}
    (hσpos : ∀ i, 0 < σ i) (hδop : ∀ i, δ i = σ i / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ i, ∀ x ∈ K, ENNReal.ofReal (θ i) ≤ MarkovChains.ell K (δ i) x)
    (hfloor : ∀ i, 1 ≤ 20 * Real.exp (-(2 * R * δ i + δ i ^ 2) / (2 * σ i ^ 2)) * (1 / 4) * θ i)
    (hiso : ∀ i, ∀ S₁ S₂ S₃ : Set (EuclSpace n),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ i * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ i * Real.log 2 / Real.sqrt n / σ i) * Real.sqrt n
            ≤ densDist (Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2))) u v) →
      δ i * Real.log 2 / Real.sqrt n / σ i
          * ((∫ x in S₁, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
        ≤ (∫ x, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (MarkovChains.gaussianWeightReal (σ i ^ 2)) x)
    {mu0 : Fin r → Fin m → Measure (EuclSpace n)}
    [∀ j i, IsProbabilityMeasure (mu0 j i)] (hM : 1 ≤ M)
    (hwarm : ∀ j i, IsWarm (ENNReal.ofReal M) (mu0 j i)
      (Arlib.uniformOn ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight (σ i ^ 2))) K))
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ (r * m : ℕ))
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2
        * (Real.log M + 2 * Real.log ((r * m : ℕ) / ρ)) / Real.log 2 ^ 2) + 1 ≤ (t : ℝ))
    {σsq : ℕ → ℝ} (hσsch : ∀ j, 0 < σsq j) (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hs : ∀ i : Fin m, σ i ^ 2 = σsq (i : ℕ))
    {V : Arlib.Probability.RunSpace (EuclSpace n) r m → ℝ} (hV : Measurable V)
    {vol acc q : ℝ}
    (hgood : q ≤ (Arlib.Probability.runMeasure
        fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol}) :
    q - ρ ≤ (Arlib.Probability.runMeasure
        fun (j : Fin r) (i : Fin m) => MarkovChains.iterate
          (MarkovChains.lazy (MarkovChains.metropolisGaussian K (δ i) (σ i ^ 2)))
          (mu0 j i) t).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} := by
  have hrm : (0 : ℝ) < (r * m : ℕ) := by
    have : 0 < r * m := Nat.mul_pos hr hm
    exact_mod_cast this
  set eps : ℝ := ρ / (r * m : ℕ) with heps_def
  have heps0 : 0 < eps := div_pos hρ0 hrm
  have heps1 : eps ≤ 1 := (div_le_one hrm).2 hρ1
  have hlog : Real.log (1 / eps) = Real.log ((r * m : ℕ) / ρ) := by
    rw [heps_def, one_div_div]
  have ht' : 4 * (5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2) + 1 ≤ (t : ℝ) := by rwa [hlog]
  have hmain := le_measureReal_runMeasure_metropolisGaussian hn hσpos hδop hR hK hKc hKR
    hKtop hK0 hell hfloor hiso hM hwarm heps0 heps1 ht' hσsch hball hs hV hgood
  have hcost : ((r * m : ℕ) : ℝ) * eps = ρ := by
    rw [heps_def, mul_div_cancel₀ _ hrm.ne']
  rw [hcost] at hmain
  exact hmain

/-! ## 5.  Non-vacuity (`CLAUDE.md` §11)

§2 quantifies over a bundle: `r·m` pairs of probability measures, a per-sample budget `b`,
a measurable estimator, and an exact-law success probability `q`.  A green build over an
unsatisfiable bundle certifies nothing, and a bundle satisfiable only at `b = 0` (the sampled
law *is* the exact law, so the theorem says nothing about sampling) would certify almost
nothing.  The witness below is neither: the realised and exact laws are **provably different
measures**, the budget is `1/4 > 0`, the total cost `(r·m)·b = 1/4` is strictly below `1`,
and the exact-law success probability is `1 > 1/2`.

**What this does not certify.**  §3's `le_measureReal_runMeasure_metropolisGaussian` and §4's
budget form additionally carry `hiso`, `hell`, `hfloor` and `hwarm`, and no witness for those
is offered *here*.

⚠ **The chain layer is now certified too.**
`Arlib.GaussianCooling.exists_couplingRoute_chain_witness`
(`Arlib/Convexity/GaussianCooling/CouplingRouteUncond.lean`) discharges **every** hypothesis
of the budget form — `hell`, `hfloor`, `hwarm`, `hball` and `hRσ` — on a single body.  The
obstacle recorded below dissolved once it was noticed that the mixing witness's mechanism
(take `δ ≥ diam K`, so `ell K δ x = vol K / vol (ball x δ)` exactly) is **scale-invariant**:
rescaling `B(0,1/2), δ = 1` to `K = B(0,1), δ = 2` makes `hball` literally `subset_rfl`,
keeps `ell = 1/4` exactly, and reproduces the same acceptance exponent `−1/128`, so the floor
still clears at `≈ 1.24 > 1`.  The earlier note below tried to reuse `B(0,1/2)` unrescaled.

(Superseded.)  `PhaseMeanRoute.lean` §6 records why the existing
`Arlib.MarkovChains.exists_mixesWithin_lazy_metropolisGaussian_witness` (on `B(0,1/2) ⊆ ℝ²`)
cannot serve *as-is*: its body does not contain the unit ball, so it is not simultaneously a
witness for `chain_pos`/`coolLaw_isProbabilityMeasure`, which §3 needs. -/

/-- The `3/4`-biased coin is a probability measure.  (Restated locally: `TVTensor.lean`'s
copy is `private`.) -/
private theorem isProbabilityMeasure_coin :
    IsProbabilityMeasure
      ((3 / 4 : ℝ≥0∞) • Measure.dirac true + (1 / 4 : ℝ≥0∞) • Measure.dirac false) := by
  constructor
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [ENNReal.div_add_div_same, show (3 : ℝ≥0∞) + 1 = 4 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- The `3/4`-biased coin gives mass exactly `3/4` to `{true}`. -/
private theorem coin_singleton_true :
    ((3 / 4 : ℝ≥0∞) • Measure.dirac true + (1 / 4 : ℝ≥0∞) • Measure.dirac false)
      ({true} : Set Bool) = 3 / 4 := by
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton (true : Bool))]
  rw [Set.indicator_of_mem (Set.mem_singleton _), Set.indicator_of_notMem (by simp),
    Pi.one_apply, mul_one, mul_zero, add_zero]

/-- **Non-vacuity of the abstract coupling-route composition.**  Every binder of
`le_measureReal_runMeasure_mem_relErr_of_tvLe` is met at once, at a **strictly positive**
per-sample budget `b = 1/4`, with the realised law `ν` and the exact law `ν'` **different
measures** (they disagree on `{true}`: mass `1` versus `3/4`), a total cost
`(r·m)·b = 1/4 < 1`, and an exact-law success probability `q = 1 > 1/2`.

So the composition is not a statement about nothing, and not the exact case in disguise. -/
theorem exists_couplingRoute_witness :
    ∃ (r m : ℕ) (ν ν' : Fin r → Fin m → Measure Bool) (b : ℝ≥0∞) (q vol acc : ℝ)
      (V : Arlib.Probability.RunSpace Bool r m → ℝ),
      0 < r ∧ 0 < m ∧ 0 < b ∧ ((r * m : ℕ) : ℝ) * b.toReal < 1 ∧ 1 / 2 < q ∧
      (∀ j i, IsProbabilityMeasure (ν j i)) ∧ (∀ j i, IsProbabilityMeasure (ν' j i)) ∧
      (∀ j i, ν j i ({true} : Set Bool) ≠ ν' j i ({true} : Set Bool)) ∧
      (∀ j i, TVLe (ν j i) (ν' j i) b) ∧ Measurable V ∧
      q ≤ (Arlib.Probability.runMeasure ν').real
        {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} ∧
      q - ((r * m : ℕ) : ℝ) * b.toReal ≤ (Arlib.Probability.runMeasure ν).real
        {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} := by
  classical
  set coin : Measure Bool :=
    (3 / 4 : ℝ≥0∞) • Measure.dirac true + (1 / 4 : ℝ≥0∞) • Measure.dirac false with hcoin
  haveI hcoinP : ∀ _j _i : Fin 1, IsProbabilityMeasure coin := fun _ _ =>
    isProbabilityMeasure_coin
  haveI hdirP : ∀ _j _i : Fin 1, IsProbabilityMeasure (Measure.dirac (true : Bool)) :=
    fun _ _ => inferInstance
  have hdir : (Measure.dirac (true : Bool)) ({true} : Set Bool) = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_singleton _)
  have htoReal : ((1 : ℝ≥0∞) / 4).toReal = 1 / 4 := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one]
    norm_num
  have hne : (1 : ℝ≥0∞) ≠ 3 / 4 := by
    intro h
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_one, ENNReal.toReal_div] at h'
    norm_num at h'
  refine ⟨1, 1, fun _ _ => Measure.dirac (true : Bool), fun _ _ => coin, 1 / 4, 1, 1, 0,
    fun _ => 1, Nat.one_pos, Nat.one_pos, by norm_num, ?_, by norm_num,
    hdirP, hcoinP, ?_, ?_, measurable_const, ?_, ?_⟩
  · rw [htoReal]; norm_num
  · intro j i
    rw [hdir, hcoin, coin_singleton_true]
    exact hne
  · intro j i
    exact tvLe_bernoulli_witness
  · have hset : {ω : Arlib.Probability.RunSpace Bool 1 1 |
        (1 - (0 : ℝ)) * 1 ≤ (fun _ => (1 : ℝ)) ω ∧ (fun _ => (1 : ℝ)) ω ≤ (1 + (0 : ℝ)) * 1}
        = Set.univ := by
      ext ω; simp
    rw [hset]
    haveI : IsProbabilityMeasure
        (Arlib.Probability.runMeasure fun _ _ : Fin 1 => coin) := inferInstance
    simp
  · have hset : {ω : Arlib.Probability.RunSpace Bool 1 1 |
        (1 - (0 : ℝ)) * 1 ≤ (fun _ => (1 : ℝ)) ω ∧ (fun _ => (1 : ℝ)) ω ≤ (1 + (0 : ℝ)) * 1}
        = Set.univ := by
      ext ω; simp
    rw [hset]
    haveI : IsProbabilityMeasure (Arlib.Probability.runMeasure
        fun _ _ : Fin 1 => Measure.dirac (true : Bool)) := inferInstance
    rw [htoReal]
    simp

end Arlib.GaussianCooling

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms Arlib.GaussianCooling.setOf_abs_sub_le_eq_relErr
#print axioms Arlib.GaussianCooling.le_measureReal_runMeasure_of_tvLe
#print axioms Arlib.GaussianCooling.le_measureReal_runMeasure_of_tvLe_const
#print axioms Arlib.GaussianCooling.le_measureReal_runMeasure_mem_relErr_of_tvLe
#print axioms Arlib.GaussianCooling.le_measureReal_runMeasure_of_failure_budget
#print axioms Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian
#print axioms Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian_budget
#print axioms Arlib.GaussianCooling.exists_couplingRoute_witness
