/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.WastedSteps
import Arlib.MarkovChains.Continuous.SpeedyGaussianConductance
import Arlib.MarkovChains.Continuous.KLS97Shell

/-!
# Wasted steps, Gaussian: the speedy Metropolis–Gaussian step count converted to a
Metropolis-filtered ball-walk step count

`Arlib/MarkovChains/Continuous/WastedSteps.lean` formalises Cousins–Vempala's
`lem:speedy-to-ball` (`1409.6011/vol3_journal.tex:915`) for the **uniform** chain: the pair
`speedyWalk K δ` / `ballWalk K δ`, with local conductance `ell K δ` and stationary law
`ellProb K δ`.  The sampler actually analysed elsewhere in this repository is the **Gaussian**
one — `speedyMetropolisGaussian K δ s` / `metropolisGaussian K δ s`, with stationary law
`ellGaussianProb K δ s`.  This file supplies that analogue.

(`Arlib/MarkovChains/Continuous/SamplerStepCount.lean`'s docstring records, as of its writing,
that "no Gaussian analogue of `WastedSteps.lean` exists in this repository" and that reading
its §5 as "the ball-walk cost of the Gaussian sampler" is not licensed.  That remark is
superseded by this file *only* for the quantity bounded here; §5 of that file is still stated
over the uniform chain and nothing here changes it.  No file outside this one is edited.)

## The new ingredient: the Metropolis acceptance factor

In the uniform case a proposal that lands in `K` is accepted outright, so from `x` the ball
walk needs `Geom(ell K δ x)` steps to make one proper step and the mean cost of a speedy step
is `1/ℓ(x)`.  With a Gaussian filter a proposal inside `K` can *still* be rejected, with
probability `1 − min(1, g(y)/g(x))`.  The two rejections compose exactly:

* `Arlib.MarkovChains.ell K δ x = vol(B(x,δ) ∩ K)/vol(δBₙ)` — the proposal lands in `K`;
* `Arlib.MarkovChains.speedyMetropolisMove K δ s x` — the **mean acceptance probability over
  the accepted part `B(x,δ) ∩ K` of the proposal ball**, i.e. the chance that a proposal
  *already known to be in `K`* survives the filter;

and `metropolisMove_eq_ell_mul_speedyMetropolisMove` proves, **unconditionally**,

    metropolisMove K δ s x  =  ell K δ x · speedyMetropolisMove K δ s x.

So the expected number of `metropolisGaussian` steps per accepted move from `x` is
`1/(ℓ(x)·a(x))`, not `1/ℓ(x)`: the acceptance `a` is a second, multiplicative source of wasted
steps.  Everything below is the uniform argument with `ℓ` replaced by `ℓ·a`, plus a floor on
`a` to keep the extra factor constant.

## The floor on the acceptance, and what it costs

`Arlib.MarkovChains.metropolisAccept_ge` (`MetropolisConductanceSharp.lean`) floors the
pointwise acceptance by `e^{−(2Rδ+δ²)/(2s)}` for `‖x‖ ≤ R`; averaging it over the proposal
ball gives `acceptance_floor_le_speedyMetropolisMove`, valid at every non-stuck `x` with
`‖x‖ ≤ R`, and `ae_restrict_acceptance_floor_le_speedyMetropolisMove` upgrades that to
`volume.restrict K`-almost-everywhere using `ae_restrict_ell_ne_zero` (`δ > 0`).

**This forces a binder the uniform file does not have**: `hKR : ∀ x ∈ K, ‖x‖ ≤ R`.  The floor
degrades with `‖x‖`, so a bound on the body's radius is unavoidable; it is Cousins–Vempala's
own `R ≤ 2σ√n` regime.  In that regime
`Arlib.MarkovChains.acceptance_floor_of_cv` (`SpeedyGaussianConductance.lean`, at `s = σ²`,
`δ ≤ σ/(8√n)`, `R ≤ 2σ√n`, `n ≥ 2`) gives `e^{−(2Rδ+δ²)/(2σ²)} ≥ 3/5`, so the acceptance
inflates the step-count bound by at most **`5/3`** — a constant, independent of `n`, `δ`, `σ`
and `K`.  That is §6, `three_mul_sum_lintegral_le_five_mul_of_cv`.

## Main results

**The factorisation, and the cost of one speedy step** (deliverable 1).

* `Arlib.MarkovChains.metropolisMove_eq_ell_mul_speedyMetropolisMove` — the exact identity
  above.  No hypotheses at all.
* `Arlib.MarkovChains.metropolisGaussian_apply_singleton` — the holding mass is
  `1 − ℓ(x)·a(x)`.
* `Arlib.MarkovChains.pathMeasure_metropolisGaussian_dirac_holdsUntil` — the holding time of
  the filtered ball walk at `x` is `Geometric(ℓ(x)·a(x))`, at trajectory level.
* `Arlib.MarkovChains.lintegral_exitTime_pathMeasure_metropolisGaussian` — **the one-step
  cost**: the mean, under the *real* `metropolisGaussian` trajectory measure started at `x`,
  of the exit time `inf {i | ωᵢ ≠ x}` is exactly `(ℓ(x)·a(x))⁻¹`.

**The acceptance floor.**

* `Arlib.MarkovChains.acceptance_floor_le_speedyMetropolisMove` and
  `Arlib.MarkovChains.ae_restrict_acceptance_floor_le_speedyMetropolisMove`.

**The stationary cost.**

* `Arlib.MarkovChains.lintegral_inv_ell_mul_move_ellGaussianMeasure` —
  `∫⁻ (ℓ·a)⁻¹ dellGaussianMeasure = ∫_K g·a⁻¹`, the Gaussian analogue of
  `lintegral_inv_ell_ellMeasure`; the reweighting `ℓ·g ↦ g` is exact, the `a⁻¹` is what the
  filter leaves behind.
* `Arlib.MarkovChains.mul_mul_lintegral_inv_ell_mul_move_ellGaussianProb_le_one` —
  `a₀ · λ · ∫⁻ (ℓ·a)⁻¹ dellGaussianProb ≤ 1`.

**`lem:speedy-to-ball`, Gaussian** (deliverables 2 and 3).

* `Arlib.MarkovChains.mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le`
  — the core, `NeZero`-free form:

      a₀ · λ · ∑_{i<t} ∫⁻ (ℓ·a)⁻¹ d(iterate (speedyMetropolisGaussian K δ s) Q₀ i)  ≤  t · M.

* `Arlib.MarkovChains.sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le` —
  the divided form `∑ ≤ t·M/(a₀·λ)`.
* `Arlib.MarkovChains.mul_sum_lintegral_exitTime_iterate_speedyMetropolisGaussian_le` — the
  **trajectory form**, the same bound with the integrand replaced by the *proved* mean exit
  time of the real `metropolisGaussian` trajectory from `x`.  Costs `[NeZero n]`.
* `Arlib.MarkovChains.three_mul_sum_lintegral_le_five_mul_of_cv` — the Cousins–Vempala regime,
  with the acceptance priced at `5/3`.

**`hlam` discharged at `δ ≤ 1/(2n)`** (§7).

* `Arlib.MarkovChains.half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ` — the
  `g`-weighted average local conductance is at least `1/2` for a convex `K ⊇ B(0,1)` at step
  `δ ≤ 1/(2n)`.  **Proved, not assumed**: `KLS97Shell.lean`'s `ell_eq_one_on_shrunken` plus the
  Gaussian scaling identity, with no Lovász–Vempala smoothing lemma anywhere.
* `Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero_of_shrunken` — the guard `hZ0`, likewise
  discharged.
* `Arlib.MarkovChains.mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le_uncond`
  — `a₀ · ∑ ≤ 2·t·M`, with `hwarm` the only remaining non-geometric hypothesis.
* `Arlib.MarkovChains.three_mul_sum_lintegral_le_ten_mul_of_cv` — **both** constants proved:
  `3·∑ ≤ 10·t·M`, i.e. `∑ ≤ (10/3)·t·M`, where `10/3 = 2·(5/3)` is the proved `λ ≥ 1/2` times
  the proved acceptance floor `a ≥ 3/5`.

**Non-vacuity.**

* `Arlib.MarkovChains.exists_wastedStepsGaussian_witness`, which discharges the binders of
  §§1–6, and `Arlib.MarkovChains.exists_wastedStepsGaussian_uncond_witness`, which discharges
  those of §7.  Their hypotheses on `δ` are incompatible, so neither covers the other.

## What is assumed and not proved

* **`hlam` is a hypothesis in §§4–6, and a theorem in §7.**  In §§4–6 it is written
  multiplicatively,

      λ · (∫_K g)  ≤  ∫_K ℓ·g       (`ellGaussianMeasure K δ s Set.univ = ∫_K ℓ·g`),

  i.e. `λ ≤ (∫_K ℓ·g)/(∫_K g)`, the **`g`-weighted average local conductance** — which is
  exactly Cousins–Vempala's `λ(f)` at `f = 1_K·g`, the density of the phase being sampled.
  This is their `lem:lambda-bound` (`vol3_journal.tex:855`).  **At Cousins–Vempala's own step
  size nothing in this repository proves it** — their proof goes through Lovász–Vempala's
  smoothing lemma, and `LambdaBoundSharp.lean` carries `hLov` unproved because Mathlib has no
  convex-body surface measure — so §§4–6 carry it as an explicit binder.  It is stated
  multiplicatively so that no `ℝ≥0∞` division appears and so that it is honest at `λ = 0`;
  `mul_lintegral_gaussianWeight_le_of_le_div` converts CV's ratio form into it.

  **At the smaller step `δ ≤ 1/(2n)` it is proved** (§7,
  `half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ`, at `λ = 1/2`), by
  `KLS97Shell.lean`'s convexity argument rather than by smoothing, and §7's theorems carry no
  `λ`-binder at all.  The restriction on `δ` is genuine and is priced in `KLS97Shell.lean`'s
  docstring: it costs a factor `n` in the mixing bound.
* **`hwarm : IsWarm M Q₀ (ellGaussianProb K δ s)` is a hypothesis**, exactly as CV's
  `M(Q₀,Q) ≤ M` is.  It is checked once, at time zero; `isWarm_iterate` makes that enough.
  (`SamplerStepCount.lean` records why this binder is *not* discharged by `WarmChain.lean`'s
  `√e`: that constant warms `coolLaw i` for `coolLaw (i+1)`, and the bridge to the
  `ℓ`-weighted `ellGaussianProb` is unproved — `EllFloor.lean` rules out the obvious route.)
* **`hZ0 : ellGaussianMeasure K δ s Set.univ ≠ 0`** is a non-degeneracy guard in §§4–6, carried
  rather than derived so that those theorems need neither convexity nor boundedness of `K`;
  `ellGaussianMeasure_unitBall_ne_zero` discharges it in the witness, and
  `ellGaussianMeasure_univ_ne_zero_of_shrunken` discharges it outright in §7.

## What is *not* claimed

Read this before quoting anything below.  The first two items are inherited verbatim from
`WastedSteps.lean`; the third is new to the Gaussian chain and must not be dropped.

1. **The left-hand side is a sum of per-step conditional expectations, not a proved functional
   of a single trajectory.**  `∑_{i<t} ∫⁻ (mean holding time) dQᵢ` is precisely the quantity
   Cousins–Vempala bound by linearity of expectation, and each summand is a proved expected
   exit time of the real filtered ball walk
   (`mul_sum_lintegral_exitTime_iterate_speedyMetropolisGaussian_le`).  Identifying that sum
   with "the number of `metropolisGaussian` steps a trajectory actually takes to realise `t`
   speedy steps" needs the path-level time change `ω_t = Y_{N t}`, which is
   `TrajTransfer.lean`'s "What is not proved", item 1, and is **still unproved**.  Do not
   restate any capstone below as a statement about a single trajectory.
2. **This is a step-count statement and nothing else.**  No complexity field, no cost model and
   no running-time claim is introduced here or exists anywhere in this repository.  `t` is a
   number of speedy steps supplied by the caller; nothing here says how large it must be for
   the chain to mix.
3. **"Speedy step" here means an *accepted move* of the speedy chain, and the speedy chain has
   a holding atom of its own.**  Unlike `speedyWalk`, which moves with probability `1` off its
   stuck points, `speedyMetropolisGaussian` rejects with probability `1 − a(x)` and holds
   (`speedyMetropolisGaussian_apply_compl_singleton`; `speedyMetropolisMove_unitBall_lt_one`
   shows this is not vacuous).  The exit-time integrand `(ℓ(x)·a(x))⁻¹` counts
   `metropolisGaussian` steps until the first **accepted move** out of `x`, and the sum runs
   over `t` steps of the *kernel* `speedyMetropolisGaussian`, some of which are its own
   rejections.  So the sum is "expected filtered-ball-walk steps charged to `t` speedy-kernel
   steps", not "…per `t` distinct visited points".
4. **No bound on `M` is proved here** — see "What is assumed" above; the warm-start constant is
   a binder of *every* theorem in this file, §7's included.  A bound on `λ` *is* proved, but
   only in §7's regime `δ ≤ 1/(2n)` and only for a convex `K` containing the unit ball; §§4–6
   assume it.  The acceptance is bounded below only under `hKR`.

## Audit surface (`CLAUDE.md` §11)

* **Capstones**:
  `mul_sum_lintegral_exitTime_iterate_speedyMetropolisGaussian_le` (trajectory form),
  `mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le` (core form),
  `three_mul_sum_lintegral_le_five_mul_of_cv` (CV regime) and — the strongest —
  `three_mul_sum_lintegral_le_ten_mul_of_cv` (CV regime with `λ` and the acceptance both
  proved).  Read the types only.
* **Hypotheses carried unproved**: `hwarm` everywhere, and `hlam` in §§4–6 only; both are listed
  above with their CV provenance.  Every other binder (`hK`, `hKc`, `hball`, `hδ`, `hδn`, `hs`,
  `hR`, `hKR`, `hZ0`) is a measurability, convexity, positivity, radius or non-degeneracy guard,
  each discharged for the unit ball inside one of the two witnesses.
* **Non-vacuity**: `exists_wastedStepsGaussian_witness` (binders of §§1–6) and
  `exists_wastedStepsGaussian_uncond_witness` (binders of §7); the two ranges of `δ` are
  incompatible, so both are needed.  Unlike the uniform file's witness the bound is **not**
  attained in either — the acceptance floor `a₀ ≤ a(x)` has genuine slack — and the witnesses
  say so: it certifies satisfiability of every binder, strict positivity and
  finiteness of the left-hand side, and that the filter really does reject.
* **Semantic `def`s**: none.  This file introduces no `def`, no `structure`, no `class` and no
  named `Prop`; every hypothesis is an inline binder of the theorem that consumes it.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 0. One `ℝ≥0∞` fact

`ℝ≥0∞` division by `0` and by `⊤` both return `0`, so `a * b⁻¹ ≤ 1` from `a ≤ b` needs a case
split rather than a cancellation.  It is used twice below and is stated once here. -/

/-- **`a ≤ b` gives `a · b⁻¹ ≤ 1` in `ℝ≥0∞`**, with no positivity or finiteness hypothesis:
at `b = 0` the assumption forces `a = 0`, and at `b = ⊤` the product is `a · 0 = 0`. -/
theorem mul_inv_le_one_of_le {a b : ℝ≥0∞} (h : a ≤ b) : a * b⁻¹ ≤ 1 := by
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [le_zero_iff.1 h, zero_mul]; exact zero_le_one
  rcases eq_or_ne b ⊤ with rfl | hbtop
  · rw [ENNReal.inv_top, mul_zero]; exact zero_le_one
  calc a * b⁻¹ ≤ b * b⁻¹ := by gcongr
    _ = 1 := ENNReal.mul_inv_cancel hb0 hbtop

/-! ## 1. The acceptance factorisation

The one structural fact separating this file from `WastedSteps.lean`.  Both move
probabilities are the *same* accepted mass `N(x) = ∫_K 1[y ∈ B(x,δ)]·min(1, g(y)/g(x)) dy`
over *different* normalisers: `metropolisMove` divides by `vol(δBₙ)` (a rejected proposal
becomes a holding atom), `speedyMetropolisMove` divides by `vol(B(x,δ) ∩ K)` (the speedy
proposal conditions on landing in `K`).  The ratio of the normalisers is exactly `ell`. -/

/-- **The Metropolis move probability factors as local conductance times mean acceptance**:

    metropolisMove K δ s x  =  ell K δ x · speedyMetropolisMove K δ s x.

`ell K δ x` is the chance the uniform proposal from `x` lands in `K`; `speedyMetropolisMove`
is the mean acceptance probability of the filter *given* that it did.  The identity is
**exact and carries no hypotheses at all** — not even `MeasurableSet K` or `δ > 0`.

Where the walk is stuck (`vol(B(x,δ) ∩ K) = 0`) both sides are `0`: the accepted mass is
bounded by that volume (`lintegral_metropolisDensity_le`), so the numerator vanishes too, and
the `ℝ≥0∞` convention `x/0 = 0` makes the factor `speedyMetropolisMove` vanish rather than
blow up.  Where `δ ≤ 0` both sides are `0` for the same reason. -/
theorem metropolisMove_eq_ell_mul_speedyMetropolisMove
    (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    metropolisMove K δ s x = ell K δ x * speedyMetropolisMove K δ s x := by
  have hNW : (∫⁻ y in K, metropolisDensity s δ x y) ≤ volume (Metric.ball x δ ∩ K) :=
    lintegral_metropolisDensity_le K δ s x
  rw [metropolisMove_apply, ell_apply, speedyMetropolisMove_apply]
  rcases eq_or_ne (volume (Metric.ball x δ ∩ K)) 0 with hW0 | hW0
  · have hN0 : (∫⁻ y in K, metropolisDensity s δ x y) = 0 := by
      rw [hW0] at hNW; exact le_zero_iff.1 hNW
    rw [hW0, hN0]
    simp
  · have hWtop : volume (Metric.ball x δ ∩ K) ≠ ⊤ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_left)
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    calc (volume (Metric.ball x δ))⁻¹ * ∫⁻ y in K, metropolisDensity s δ x y
        = (volume (Metric.ball x δ ∩ K) * (volume (Metric.ball x δ ∩ K))⁻¹)
            * ((volume (Metric.ball x δ))⁻¹ * ∫⁻ y in K, metropolisDensity s δ x y) := by
          rw [ENNReal.mul_inv_cancel hW0 hWtop, one_mul]
      _ = (volume (Metric.ball x δ))⁻¹ * volume (Metric.ball x δ ∩ K)
            * ((volume (Metric.ball x δ ∩ K))⁻¹ * ∫⁻ y in K, metropolisDensity s δ x y) := by
          ring

/-! ## 2. The cost of one speedy step, along the real trajectory

Deliverable 1.  `TrajTransfer.lean`'s `pathMeasure_dirac_holdsUntil` is proved for an
*arbitrary* Markov kernel on a space with measurable singletons, so nothing about the geometric
holding law has to be redone: only the value of `P x {x}` changes, and §1 computes it. -/

/-- **The filtered ball walk stays put with probability exactly `1 − ℓ(x)·a(x)`.**  Complement
of `metropolisGaussian_apply_compl_singleton`, with §1 substituted; `[NeZero n]` is inherited
from it and is not removable (in `EuclideanSpace ℝ (Fin 0)` the space is a single atom). -/
theorem metropolisGaussian_apply_singleton [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    metropolisGaussian K δ s x {x} = 1 - ell K δ x * speedyMetropolisMove K δ s x := by
  have hsum : metropolisGaussian K δ s x {x} + metropolisGaussian K δ s x {x}ᶜ = 1 := by
    rw [measure_add_measure_compl (measurableSet_singleton x)]
    exact measure_univ
  rw [metropolisGaussian_apply_compl_singleton K δ s x] at hsum
  rw [← metropolisMove_eq_ell_mul_speedyMetropolisMove, ← hsum,
    ENNReal.add_sub_cancel_right
      (ne_top_of_le_ne_top ENNReal.one_ne_top (metropolisMove_le_one K δ s x))]

/-- **The holding time of the Metropolis-filtered ball walk is `Geometric(ℓ(x)·a(x))`**, at
trajectory level: started at `x`, the law of the *whole infinite path* assigns the event
"still at `x` at every time `0, …, k`" the mass `(1 − ℓ(x)·a(x))^k`.

Assumes only `[NeZero n]` — no measurability of `K`, no positivity of `δ` or `s`.  Contrast the
uniform statement `pathMeasure_ballWalk_dirac_holdsUntil`, whose parameter is `ℓ(x)` alone: the
extra factor `a(x)` is the Metropolis filter, and it makes the walk hold *strictly longer*. -/
theorem pathMeasure_metropolisGaussian_dirac_holdsUntil [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) (x : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    pathMeasure (metropolisGaussian K δ s) (Measure.dirac x)
        {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}
      = (1 - ell K δ x * speedyMetropolisMove K δ s x) ^ k := by
  rw [pathMeasure_dirac_holdsUntil, metropolisGaussian_apply_singleton]

/-- **The mean holding time of the filtered ball walk at `x` is exactly `(ℓ(x)·a(x))⁻¹`.**
The sum is `∑ₖ P(the walk has not left x by time k)`, the tail-sum form of the mean exit time.

Assumes only `[NeZero n]`.  At a stuck `x`, or at an `x` the filter never lets the walk leave,
both sides are `⊤`, correctly. -/
theorem tsum_pathMeasure_metropolisGaussian_dirac_holdsUntil [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ∑' k : ℕ, pathMeasure (metropolisGaussian K δ s) (Measure.dirac x)
        {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}
      = (ell K δ x * speedyMetropolisMove K δ s x)⁻¹ := by
  have hle : ell K δ x * speedyMetropolisMove K δ s x ≤ 1 := by
    rw [← metropolisMove_eq_ell_mul_speedyMetropolisMove]
    exact metropolisMove_le_one K δ s x
  simp_rw [pathMeasure_metropolisGaussian_dirac_holdsUntil]
  rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top hle]

/-- **Deliverable 1: the expected number of `metropolisGaussian` steps per accepted move.**

The exit time of the filtered ball walk from `x` — `inf {i | ωᵢ ≠ x}`, written in its tail-sum
form `∑ₖ 1[ω has not left x by time k]` — has mean exactly

    (ell K δ x · speedyMetropolisMove K δ s x)⁻¹

under the *real* trajectory measure of `metropolisGaussian K δ s` started at `x`.  Assumes only
`[NeZero n]`.

This is the Gaussian replacement for `lintegral_exitTime_pathMeasure_ballWalk`'s `(ℓ(x))⁻¹`:
one accepted move costs `1/(ℓ·a)` filtered ball-walk steps, and the extra `1/a` is the price of
the filter. -/
theorem lintegral_exitTime_pathMeasure_metropolisGaussian [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ ω, (∑' k : ℕ, {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x}.indicator
          (1 : (ℕ → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω)
        ∂(pathMeasure (metropolisGaussian K δ s) (Measure.dirac x))
      = (ell K δ x * speedyMetropolisMove K δ s x)⁻¹ := by
  rw [lintegral_tsum fun k =>
    (measurable_one.indicator (measurableSet_holdsUntil x k)).aemeasurable]
  have h : ∀ k : ℕ, ∫⁻ ω, {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x}.indicator
        (1 : (ℕ → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω
        ∂(pathMeasure (metropolisGaussian K δ s) (Measure.dirac x))
      = pathMeasure (metropolisGaussian K δ s) (Measure.dirac x)
          {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x} :=
    fun k => lintegral_indicator_one (measurableSet_holdsUntil x k)
  simp_rw [h]
  exact tsum_pathMeasure_metropolisGaussian_dirac_holdsUntil K δ s x

/-! ## 3. A floor on the acceptance

`metropolisAccept_ge` is a *pointwise* floor on `min(1, g(y)/g(x))` for `‖x‖ ≤ R` and
`dist y x ≤ δ`.  Averaging it over the accepted part of the proposal ball floors
`speedyMetropolisMove`, which is that average.  The only obstruction is a stuck `x`, where the
average is `0/0 = 0`; `δ > 0` makes the stuck points null in `K`. -/

/-- **The mean acceptance is at least `e^{−(2Rδ+δ²)/(2s)}` at every non-stuck point of a body
of radius `R`.**

    ofReal (exp (−(2Rδ+δ²)/(2s)))  ≤  speedyMetropolisMove K δ s x

for `‖x‖ ≤ R` and `vol(B(x,δ) ∩ K) ≠ 0`.  Assumes `s > 0`, `R ≥ 0`, `δ ≥ 0`; no measurability
of `K` is needed, because `speedyMetropolisMove` is a ratio of two integrals over `K` and
neither is being differentiated.

`hstuck` is not removable: at a stuck `x` the ratio is `0/0 = 0` by the `ℝ≥0∞` convention while
the floor is positive.  It is discharged almost everywhere on `K` by
`ae_restrict_acceptance_floor_le_speedyMetropolisMove`. -/
theorem acceptance_floor_le_speedyMetropolisMove {s : ℝ} (hs : 0 < s) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) {K : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ R)
    (hstuck : volume (Metric.ball x δ ∩ K) ≠ 0) :
    ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
      ≤ speedyMetropolisMove K δ s x := by
  have hWtop : volume (Metric.ball x δ ∩ K) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_left)
  have hlow : ∀ y : EuclideanSpace ℝ (Fin n),
      (Metric.ball x δ).indicator
          (fun _ => ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))) y
        ≤ metropolisDensity s δ x y := by
    intro y
    by_cases hy : y ∈ Metric.ball x δ
    · rw [Set.indicator_of_mem hy, metropolisDensity, Set.indicator_of_mem hy]
      exact metropolisAccept_ge hs hR hδ hx (Metric.mem_ball.1 hy).le
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
  rw [speedyMetropolisMove_apply]
  refine (ENNReal.le_div_iff_mul_le (Or.inl hstuck) (Or.inl hWtop)).2 ?_
  calc ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
        * volume (Metric.ball x δ ∩ K)
      = ∫⁻ y in K, (Metric.ball x δ).indicator
          (fun _ => ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))) y := by
        rw [lintegral_indicator measurableSet_ball,
          Measure.restrict_restrict measurableSet_ball, setLIntegral_const]
    _ ≤ ∫⁻ y in K, metropolisDensity s δ x y := lintegral_mono hlow

/-- **The acceptance floor, almost everywhere on `K`.**  For `δ > 0` the stuck points meet `K`
in a Lebesgue-null set (`volume_inter_stuckPoints_eq_zero`, via `ae_restrict_ell_ne_zero`), so
the pointwise floor holds `volume.restrict K`-a.e. under `hKR : ∀ x ∈ K, ‖x‖ ≤ R` alone.

Assumes `MeasurableSet K`, `s > 0`, `R ≥ 0`, `δ > 0` and `hKR`. -/
theorem ae_restrict_acceptance_floor_le_speedyMetropolisMove {s : ℝ} (hs : 0 < s) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) :
    ∀ᵐ x ∂(volume.restrict K),
      ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
        ≤ speedyMetropolisMove K δ s x := by
  filter_upwards [ae_restrict_ell_ne_zero hK hδ, ae_restrict_mem hK] with x hell hxK
  refine acceptance_floor_le_speedyMetropolisMove hs hR hδ.le (hKR x hxK) ?_
  intro hcon
  exact hell (by rw [ell_apply, hcon, ENNReal.zero_div])

/-! ## 4. The cost of one speedy step in stationarity

Cousins–Vempala's display at `vol3_journal.tex:933` reads `∫_K (1/ℓ) dQ = ∫_K (1/λ) dQ̂ = 1/λ`,
"where `Q̂` is the corresponding distribution for the ball walk".  For the Gaussian phase
`Q = ellGaussianProb K δ s ∝ ℓ·g·1_K` and `Q̂ ∝ g·1_K`, and the reweighting `ℓ·g ↦ g` is again
*exact*: it is `ellMeasure_withDensity_inv_ell`'s argument with the extra factor `g` carried
through.  What does *not* cancel is the acceptance, which is why §3 exists. -/

/-- **The reweighting identity for the Gaussian phase.**

    ∫⁻ (ℓ·a)⁻¹ d(ellGaussianMeasure K δ s)  =  ∫_K g·a⁻¹.

The `ℓ` of the density and the `ℓ⁻¹` of the integrand cancel *exactly* (a.e. on `K`, by
`ae_restrict_ell_ne_zero`); the acceptance `a⁻¹` survives.  Assumes `MeasurableSet K` and
`δ > 0`, and nothing else — no convexity, no bound on `vol K`, no positivity of `s`.

Note that `(ℓ·a)⁻¹ = ℓ⁻¹·a⁻¹` holds here with no side condition: both factors are
probabilities, hence `≠ ⊤`, which is exactly what `ENNReal.mul_inv` asks for. -/
theorem lintegral_inv_ell_mul_move_ellGaussianMeasure {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹ ∂(ellGaussianMeasure K δ s)
      = ∫⁻ x in K, gaussianWeight s x * (speedyMetropolisMove K δ s x)⁻¹ := by
  have hmeas : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      (ell K δ x * speedyMetropolisMove K δ s x)⁻¹ :=
    ((measurable_ell hK δ).mul (measurable_speedyMetropolisMove hK δ s)).inv
  rw [ellGaussianMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_ell_mul_gaussianWeight hK δ s) hmeas]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_ell_ne_zero hK hδ] with x hell
  have helltop : ell K δ x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ x)
  simp only [Pi.mul_apply]
  rw [ENNReal.mul_inv (Or.inl hell) (Or.inl helltop)]
  calc ell K δ x * gaussianWeight s x
        * ((ell K δ x)⁻¹ * (speedyMetropolisMove K δ s x)⁻¹)
      = (ell K δ x * (ell K δ x)⁻¹)
          * (gaussianWeight s x * (speedyMetropolisMove K δ s x)⁻¹) := by ring
    _ = gaussianWeight s x * (speedyMetropolisMove K δ s x)⁻¹ := by
        rw [ENNReal.mul_inv_cancel hell helltop, one_mul]

/-- **Cousins–Vempala's `λ`-hypothesis, converted from its ratio form.**  `λ ≤ (∫_K ℓ·g)/(∫_K g)`
becomes `λ · (∫_K g) ≤ ∫_K ℓ·g` once the denominator is known to be positive and finite.  Every
theorem below takes the multiplicative form, so that no `ℝ≥0∞` division appears in a hypothesis
and so that `λ = 0` is honest rather than accidental. -/
theorem mul_lintegral_gaussianWeight_le_of_le_div {K : Set (EuclideanSpace ℝ (Fin n))}
    {δ s : ℝ} (hG0 : (∫⁻ x in K, gaussianWeight s x) ≠ 0)
    (hGtop : (∫⁻ x in K, gaussianWeight s x) ≠ ⊤) {lam : ℝ≥0∞}
    (hlam : lam ≤ ellGaussianMeasure K δ s Set.univ / ∫⁻ x in K, gaussianWeight s x) :
    lam * (∫⁻ x in K, gaussianWeight s x) ≤ ellGaussianMeasure K δ s Set.univ :=
  (ENNReal.le_div_iff_mul_le (Or.inl hG0) (Or.inl hGtop)).1 hlam

/-- **One speedy step costs at most `1/(a₀·λ)` filtered ball-walk steps, in stationarity.**

    a₀ · λ · ∫⁻ (ℓ·a)⁻¹ dellGaussianProb  ≤  1,   a₀ = ofReal (exp (−(2Rδ+δ²)/(2s))).

Assumes `MeasurableSet K`, `δ > 0`, `s > 0`, `R ≥ 0`, `hKR : ∀ x ∈ K, ‖x‖ ≤ R`, the two
non-degeneracy guards on the total `ℓ·g`-weight, and `hlam`.  Stated multiplicatively so that
it carries no `ℝ≥0∞` division and is vacuous — honestly — at `λ = 0`.

This is `mul_lintegral_inv_ell_ellProb_le_one_of_le_avg` (`WastedSteps.lean`) with the Gaussian
weight carried through the reweighting and the acceptance priced by §3.  The factor `a₀` is the
whole difference. -/
theorem mul_mul_lintegral_inv_ell_mul_move_ellGaussianProb_le_one
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ)
    {s : ℝ} (hs : 0 < s) {R : ℝ} (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hZ0 : ellGaussianMeasure K δ s Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K δ s Set.univ ≠ ⊤) {lam : ℝ≥0∞}
    (hlam : lam * (∫⁻ x in K, gaussianWeight s x) ≤ ellGaussianMeasure K δ s Set.univ) :
    ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * lam
        * ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹ ∂(ellGaussianProb K δ s) ≤ 1 := by
  have hint : ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹ ∂(ellGaussianProb K δ s)
      = (ellGaussianMeasure K δ s Set.univ)⁻¹
        * ∫⁻ x in K, gaussianWeight s x * (speedyMetropolisMove K δ s x)⁻¹ := by
    rw [ellGaussianProb, lintegral_smul_measure, smul_eq_mul,
      lintegral_inv_ell_mul_move_ellGaussianMeasure hK hδ s]
  have hfloor : ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
        * ∫⁻ x in K, gaussianWeight s x * (speedyMetropolisMove K δ s x)⁻¹
      ≤ ∫⁻ x in K, gaussianWeight s x := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_acceptance_floor_le_speedyMetropolisMove hs hR hδ hK hKR]
      with x hx
    calc ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
          * (gaussianWeight s x * (speedyMetropolisMove K δ s x)⁻¹)
        = gaussianWeight s x * (ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
            * (speedyMetropolisMove K δ s x)⁻¹) := by ring
      _ ≤ gaussianWeight s x * 1 := by gcongr; exact mul_inv_le_one_of_le hx
      _ = gaussianWeight s x := mul_one _
  rw [hint]
  calc ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * lam
        * ((ellGaussianMeasure K δ s Set.univ)⁻¹
          * ∫⁻ x in K, gaussianWeight s x * (speedyMetropolisMove K δ s x)⁻¹)
      = (ellGaussianMeasure K δ s Set.univ)⁻¹
          * (lam * (ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
            * ∫⁻ x in K, gaussianWeight s x * (speedyMetropolisMove K δ s x)⁻¹)) := by ring
    _ ≤ (ellGaussianMeasure K δ s Set.univ)⁻¹ * (lam * ∫⁻ x in K, gaussianWeight s x) := by
        gcongr
    _ ≤ (ellGaussianMeasure K δ s Set.univ)⁻¹ * ellGaussianMeasure K δ s Set.univ := by
        gcongr
    _ = 1 := ENNReal.inv_mul_cancel hZ0 hZtop

/-! ## 5. `lem:speedy-to-ball`, Gaussian

Ingredient (i) — warmth along the chain — is `WastedSteps.lean` §1, reused verbatim: its
`sum_lintegral_iterate_le_of_isWarm` is generic in the measurable space, the kernel and the
observable, so nothing about warmness has to be redone for the Gaussian chain.  Ingredient
(ii) — the stationary cost `1/(a₀·λ)` — is §4.  Cousins–Vempala's proof is their product, and
so is this. -/

/-- **Cousins–Vempala `lem:speedy-to-ball` for the Gaussian sampler** (deliverable 2), core
form:

    a₀ · λ · ∑_{i<t} ∫⁻ (ℓ·a)⁻¹ d(iterate (speedyMetropolisGaussian K δ s) Q₀ i)  ≤  t · M,

with `a₀ = ofReal (exp (−(2Rδ+δ²)/(2s)))` the acceptance floor of §3.

In words: if the `g`-weighted average local conductance is at least `λ`, the body has radius
at most `R`, and the speedy Metropolis–Gaussian chain is started from a law that is `M`-warm
for its own stationary law `ellGaussianProb K δ s`, then the total mean holding time of the
*filtered* ball walk accumulated over `t` speedy steps is at most `M·t/(a₀·λ)`.

Assumes `MeasurableSet K`, `δ > 0`, `s > 0`, `R ≥ 0`, `hKR : ∀ x ∈ K, ‖x‖ ≤ R`, the two
guards on the total `ℓ·g`-weight, `hlam` (CV's `lem:lambda-bound` in `g`-weighted
multiplicative form, **assumed, not proved** — see the module docstring) and
`hwarm : IsWarm M Q₀ (ellGaussianProb K δ s)` (CV's `M(Q₀,Q) ≤ M`).

Stated multiplicatively: `λ` may be `0`, in which case both CV's bound and this one are
vacuous.  Compare `WastedSteps.lean`'s
`mul_sum_lintegral_inv_ell_iterate_speedyWalk_le`, which is this statement with `a ≡ 1`,
`a₀ = 1` and `g ≡ 1`; the acceptance factor and the radius binder `hKR` are the entire
difference.

**Scope.**  Read items 1 and 3 of the module docstring's "What is *not* claimed" before
quoting this: the left-hand side is a sum of per-step conditional expectations, each a proved
mean exit time of the real filtered ball walk
(`mul_sum_lintegral_exitTime_iterate_speedyMetropolisGaussian_le`), and **not** the number of
steps a single trajectory takes; and a "speedy step" here is a step of the kernel
`speedyMetropolisGaussian`, which has a holding atom of its own. -/
theorem mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ)
    {s : ℝ} (hs : 0 < s) {R : ℝ} (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hZ0 : ellGaussianMeasure K δ s Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K δ s Set.univ ≠ ⊤) {lam M : ℝ≥0∞}
    (hlam : lam * (∫⁻ x in K, gaussianWeight s x) ≤ ellGaussianMeasure K δ s Set.univ)
    {Q₀ : Measure (EuclideanSpace ℝ (Fin n))} (hwarm : IsWarm M Q₀ (ellGaussianProb K δ s))
    (t : ℕ) :
    ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * lam
        * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
            ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i)
      ≤ (t : ℝ≥0∞) * M := by
  have hstat : step (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s)
      = ellGaussianProb K δ s :=
    step_invariant (invariant_speedyMetropolisGaussian hK δ s)
  have hsum := sum_lintegral_iterate_le_of_isWarm hwarm hstat
    (fun x => (ell K δ x * speedyMetropolisMove K δ s x)⁻¹) t
  have havg := mul_mul_lintegral_inv_ell_mul_move_ellGaussianProb_le_one hK hδ hs hR hKR
    hZ0 hZtop hlam
  calc ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * lam
        * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
            ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i)
      ≤ ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * lam
          * ((t : ℝ≥0∞) * (M * ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
            ∂(ellGaussianProb K δ s))) := by gcongr
    _ = (t : ℝ≥0∞) * M * (ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * lam
          * ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
            ∂(ellGaussianProb K δ s)) := by ring
    _ ≤ (t : ℝ≥0∞) * M * 1 := by gcongr
    _ = (t : ℝ≥0∞) * M := mul_one _

/-- **The divided form**, `∑ ≤ t·M/(a₀·λ)`, which is Cousins–Vempala's `M·t/λ` inflated by the
acceptance.

Assumes everything the core form assumes, plus `λ ≠ 0` and `λ ≠ ⊤` — the two guards `ℝ≥0∞`
division needs.  No guard on `a₀` is needed: `ofReal (exp _)` is automatically non-zero
(`Real.exp_pos`) and finite (`ENNReal.ofReal_ne_top`), which is one reason the floor is stated
in that form. -/
theorem sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ)
    {s : ℝ} (hs : 0 < s) {R : ℝ} (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hZ0 : ellGaussianMeasure K δ s Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K δ s Set.univ ≠ ⊤) {lam M : ℝ≥0∞}
    (hlam : lam * (∫⁻ x in K, gaussianWeight s x) ≤ ellGaussianMeasure K δ s Set.univ)
    (hlam0 : lam ≠ 0) (hlamtop : lam ≠ ⊤)
    {Q₀ : Measure (EuclideanSpace ℝ (Fin n))} (hwarm : IsWarm M Q₀ (ellGaussianProb K δ s))
    (t : ℕ) :
    ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
        ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i)
      ≤ (t : ℝ≥0∞) * M
          / (ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * lam) := by
  have ha0 : ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  refine (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero ha0 hlam0))
    (Or.inl (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlamtop))).2 ?_
  rw [mul_comm]
  exact mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le hK hδ hs hR hKR
    hZ0 hZtop hlam hwarm t

/-! ### The same bound about the real filtered ball-walk trajectory

Deliverable 3.  §2's `lintegral_exitTime_pathMeasure_metropolisGaussian` computes the mean,
under the *trajectory measure* of `metropolisGaussian` started at `x`, of the exit time
`inf {i | ωᵢ ≠ x}` — the number of filtered ball-walk steps up to and including the first
accepted move — to be exactly `(ℓ(x)·a(x))⁻¹`.  Averaging that identity over the law of the
current speedy state turns the formal reciprocal above into a statement about genuine step
counts. -/

/-- **The averaged mean-holding-time identity for the filtered ball walk.**  For any law `μ` of
the starting point,

    ∫⁻ x, E_x[exit time of metropolisGaussian from x] dμ = ∫⁻ x, (ℓ(x)·a(x))⁻¹ dμ,

the inner expectation being taken under the filtered ball walk's trajectory measure started at
the Dirac mass at `x`, and the exit time written in its tail-sum form.

Assumes `[NeZero n]` and nothing else — no measurability of `K`, no hypothesis on `μ`: the
identity is pointwise in `x`, so it integrates against anything. -/
theorem lintegral_lintegral_exitTime_pathMeasure_metropolisGaussian [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    ∫⁻ x, (∫⁻ ω, (∑' k : ℕ, {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x}.indicator
              (1 : (ℕ → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω)
            ∂(pathMeasure (metropolisGaussian K δ s) (Measure.dirac x))) ∂μ
      = ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹ ∂μ :=
  lintegral_congr fun x => lintegral_exitTime_pathMeasure_metropolisGaussian K δ s x

/-- **Cousins–Vempala `lem:speedy-to-ball` for the Gaussian sampler, trajectory form** — the
headline of this file:

    a₀ · λ · ∑_{i<t} ∫⁻ x, E_x[metropolisGaussian exit time from x]
        d(iterate (speedyMetropolisGaussian K δ s) Q₀ i)  ≤  t · M.

Identical to the core form except that the integrand is the *proved* expected number of
`metropolisGaussian` steps until an accepted move, computed under that chain's own trajectory
measure, rather than the reciprocal `(ℓ(x)·a(x))⁻¹`.  So each summand is a genuine expected
filtered ball-walk step count, and the sum is exactly the quantity Cousins–Vempala bound by
linearity of expectation.

Assumes everything the core form assumes, plus `[NeZero n]`.

**What this still does not say**: that a single filtered ball-walk trajectory realising `t`
speedy steps takes at most `M·t/(a₀·λ)` steps.  Passing from the sum of per-step conditional
expectations to a functional of one trajectory is the path-level time change `ω_t = Y_{N t}`,
which is `TrajTransfer.lean`'s unproved item 1.  No running-time claim is made or implied. -/
theorem mul_sum_lintegral_exitTime_iterate_speedyMetropolisGaussian_le [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ)
    {s : ℝ} (hs : 0 < s) {R : ℝ} (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hZ0 : ellGaussianMeasure K δ s Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K δ s Set.univ ≠ ⊤) {lam M : ℝ≥0∞}
    (hlam : lam * (∫⁻ x in K, gaussianWeight s x) ≤ ellGaussianMeasure K δ s Set.univ)
    {Q₀ : Measure (EuclideanSpace ℝ (Fin n))} (hwarm : IsWarm M Q₀ (ellGaussianProb K δ s))
    (t : ℕ) :
    ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * lam
        * ∑ i ∈ Finset.range t,
            ∫⁻ x, (∫⁻ ω, (∑' k : ℕ,
                    {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x}.indicator
                      (1 : (ℕ → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω)
                  ∂(pathMeasure (metropolisGaussian K δ s) (Measure.dirac x)))
              ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i)
      ≤ (t : ℝ≥0∞) * M := by
  simp_rw [lintegral_lintegral_exitTime_pathMeasure_metropolisGaussian K δ s]
  exact mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le hK hδ hs hR hKR
    hZ0 hZtop hlam hwarm t

/-! ## 6. The Cousins–Vempala regime: the acceptance costs a factor `5/3`

`acceptance_floor_of_cv` (`SpeedyGaussianConductance.lean`) shows that at `s = σ²`, with the
step size `δ ≤ σ/(8√n)` the mixing analysis already assumes and a body inside `‖x‖ ≤ 2σ√n`,

    2Rδ + δ²  ≤  σ²/2 + σ²/64  =  (33/64)σ²,   hence   e^{−(2Rδ+δ²)/(2σ²)}  ≥  3/5.

So in that regime the Metropolis filter multiplies Cousins–Vempala's uniform bound `M·t/λ` by
at most `5/3` — a constant, independent of `n`, `δ`, `σ` and `K`.  The statements below are
written with integer coefficients (`3·X ≤ 5·Y`) so that no `ℝ≥0∞` division appears. -/

/-- **The acceptance floor in the Cousins–Vempala regime, in `ℝ≥0∞`**: `3 ≤ 5·a₀`, i.e.
`a₀ ≥ 3/5`.  A transcription of `acceptance_floor_of_cv`, whose conclusion
`1 ≤ 20·e·(1/8)·(2/3)` is `1 ≤ (5/3)·e`.  Assumes `n ≥ 2`, `σ > 0`, `δ > 0`,
`δ ≤ σ/(8√n)` and `R ≤ 2σ√n`. -/
theorem three_le_five_mul_acceptance_floor_of_cv (hn : 2 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hRσ : R ≤ 2 * σ * Real.sqrt n) :
    (3 : ℝ≥0∞) ≤ 5 * ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))) := by
  have h := acceptance_floor_of_cv hn hσ hδ hδσ hRσ
  have hreal : (3 : ℝ) ≤ 5 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) := by linarith
  calc (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by simp
    _ ≤ ENNReal.ofReal (5 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = 5 * ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- **`lem:speedy-to-ball`, Gaussian, in the Cousins–Vempala regime**: at `s = σ²`,
`δ ≤ σ/(8√n)`, `R ≤ 2σ√n` and `n ≥ 2`,

    3 · (λ · ∑_{i<t} ∫⁻ (ℓ·a)⁻¹ dQᵢ)  ≤  5 · (t · M),

i.e. `λ · ∑ ≤ (5/3)·t·M`.  **This is the effect of the Metropolis filter on the constant**: the
uniform chain's bound is `λ · ∑ ≤ t·M`, and the filter costs a factor `5/3` and nothing more.
The `3/5` comes from `acceptance_floor_of_le`'s `e^{−t} ≥ 1 − t` and is deliberately weaker
than the `e^{−33/128} ≈ 0.77` the exponential actually gives; it costs no transcendental
arithmetic.

`hlam` and `hwarm` are carried unproved exactly as above. -/
theorem three_mul_sum_lintegral_le_five_mul_of_cv (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ σ R : ℝ} (hδ : 0 < δ)
    (hσ : 0 < σ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hZ0 : ellGaussianMeasure K δ (σ ^ 2) Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K δ (σ ^ 2) Set.univ ≠ ⊤) {lam M : ℝ≥0∞}
    (hlam : lam * (∫⁻ x in K, gaussianWeight (σ ^ 2) x)
      ≤ ellGaussianMeasure K δ (σ ^ 2) Set.univ)
    {Q₀ : Measure (EuclideanSpace ℝ (Fin n))}
    (hwarm : IsWarm M Q₀ (ellGaussianProb K δ (σ ^ 2))) (t : ℕ) :
    3 * (lam * ∑ i ∈ Finset.range t,
          ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
            ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i))
      ≤ 5 * ((t : ℝ≥0∞) * M) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hcore := mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le hK hδ hs
    hR hKR hZ0 hZtop hlam hwarm t
  have hfloor := three_le_five_mul_acceptance_floor_of_cv (R := R) hn hσ hδ hδσ hRσ
  calc 3 * (lam * ∑ i ∈ Finset.range t,
          ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
            ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i))
      ≤ 5 * ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)))
          * (lam * ∑ i ∈ Finset.range t,
              ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
                ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i)) := by gcongr
    _ = 5 * (ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))) * lam
          * ∑ i ∈ Finset.range t,
              ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
                ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i)) := by ring
    _ ≤ 5 * ((t : ℝ≥0∞) * M) := by gcongr

/-! ## 7. Discharging `hlam` in the KLS97 regime `δ ≤ 1/(2n)`

The `λ`-hypothesis is Cousins–Vempala's `lem:lambda-bound`, and at their step size it needs
Lovász–Vempala's smoothing lemma — which this repository does not have (`LambdaBoundSharp.lean`
carries `hLov` unproved; `LovaszSmoothing.lean` records why).  **But at the smaller step
`δ ≤ 1/(2n)` it is elementary**, and this section proves it for the *Gaussian-weighted* average,
so that `hlam` disappears from the statements below rather than being carried.

The argument is `Arlib.MarkovChains.half_le_speedy_shrunken`'s (`KLS97Shell.lean`), rearranged:
with `c = 1 − 1/(2n)` and `B(0,1) ⊆ K` convex,

    ∫_K ℓ·g  ≥  ∫_{cK} ℓ·g  =  ∫_{cK} g  =  cⁿ·∫_K g_{s/c²}  ≥  cⁿ·∫_K g  ≥  (1/2)·∫_K g,

where the second step is `ell_eq_one_on_shrunken` (at `δ ≤ 1 − c` the proposal ball from a
point of `cK` never escapes `K`, so `ℓ ≡ 1` there), the third is
`lintegral_gaussianWeight_smul_set`, the fourth is `gaussianWeight_mono_variance` (shrinking
moves points towards the origin, where the Gaussian weight is larger) and the last is
`half_le_one_sub_inv_two_mul_pow`.  No smoothing lemma and no surface measure is involved.

**This is a genuine restriction on `δ`, not a free lunch** — see `KLS97Shell.lean`'s module
docstring.  Cousins–Vempala run at a larger step, where the deficit does not vanish and the
KLS97 averaged bound is genuinely needed; at `δ = Θ(1/n)` the mixing bound degrades from
`O(σ²n²·log(M/ε))` to `O(σ²n³·log(M/ε))`.  What is bought is that `λ = 1/2` becomes a theorem. -/

/-- **A body containing the unit ball has non-zero Gaussian mass.**  Assumes `MeasurableSet K`,
`B(0,1) ⊆ K` and `s > 0`; the unit-ball case is
`withDensity_gaussianWeight_unitBall_ne_zero`. -/
theorem lintegral_gaussianWeight_ne_zero_of_unitBall_subset
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {s : ℝ} (hs : 0 < s) :
    (∫⁻ x in K, gaussianWeight s x) ≠ 0 := by
  have h0 : (volume.withDensity (gaussianWeight s))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
    withDensity_gaussianWeight_unitBall_ne_zero hs
  rw [withDensity_apply _ measurableSet_ball] at h0
  intro hcon
  refine h0 (le_antisymm ?_ zero_le)
  rw [← hcon]
  exact lintegral_mono' (Measure.restrict_mono hball le_rfl) le_rfl

/-- **The Gaussian-weighted average local conductance is at least `1/2` at `δ ≤ 1/(2n)`** —
Cousins–Vempala's `lem:lambda-bound`, *proved* rather than assumed, in the multiplicative form
every theorem of this file consumes:

    (1/2) · ∫_K g  ≤  ∫_K ℓ·g  =  ellGaussianMeasure K δ s Set.univ.

Assumes `n ≥ 1`, `MeasurableSet K`, `Convex ℝ K`, `B(0,1) ⊆ K`, `0 < δ ≤ 1/(2n)` and `s > 0`.
No bound on `vol K`, no smoothing lemma, no isoperimetry. -/
theorem half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {δ s : ℝ}
    (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) (hs : 0 < s) :
    ENNReal.ofReal (1 / 2) * (∫⁻ x in K, gaussianWeight s x)
      ≤ ellGaussianMeasure K δ s Set.univ := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hhalf : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set c : ℝ := 1 - 1 / (2 * (n : ℝ)) with hcdef
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hδc : δ ≤ 1 - c := by rw [hcdef]; linarith
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (Metric.mem_ball_self one_pos)
  have hsub : c • K ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hKc.smul_mem_of_zero_mem h0K hy ⟨hc0.le, hc1.le⟩
  have hnum : (∫⁻ x in c • K, ell K δ x * gaussianWeight s x)
      = ∫⁻ x in c • K, gaussianWeight s x := by
    refine setLIntegral_congr_fun (measurableSet_smul_set hK (ne_of_gt hc0)) (fun x hx => ?_)
    rw [ell_eq_one_on_shrunken hKc hball hc0 hc1 hδ hδc hx, one_mul]
  have hscale : (∫⁻ x in c • K, gaussianWeight s x)
      = ENNReal.ofReal (c ^ n) * ∫⁻ x in K, gaussianWeight (s / c ^ 2) x :=
    lintegral_gaussianWeight_smul_set hK hc0 s
  have hmono : (∫⁻ x in K, gaussianWeight s x) ≤ ∫⁻ x in K, gaussianWeight (s / c ^ 2) x := by
    refine lintegral_mono fun x => ?_
    refine gaussianWeight_mono_variance hs ?_ x
    rw [le_div_iff₀ (by positivity)]
    have hcsq : c ^ 2 ≤ 1 := by nlinarith
    nlinarith [hs.le]
  have hcn : ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (c ^ n) :=
    ENNReal.ofReal_le_ofReal (by rw [hcdef]; exact half_le_one_sub_inv_two_mul_pow hn)
  rw [ellGaussianMeasure_univ]
  calc ENNReal.ofReal (1 / 2) * (∫⁻ x in K, gaussianWeight s x)
      ≤ ENNReal.ofReal (c ^ n) * ∫⁻ x in K, gaussianWeight s x := mul_le_mul_right' hcn _
    _ ≤ ENNReal.ofReal (c ^ n) * ∫⁻ x in K, gaussianWeight (s / c ^ 2) x := by gcongr
    _ = ∫⁻ x in c • K, ell K δ x * gaussianWeight s x := by rw [hnum, hscale]
    _ ≤ ∫⁻ x in K, ell K δ x * gaussianWeight s x :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

/-- **The non-degeneracy guard `hZ0`, discharged in the same regime.**  If the `ℓ·g`-weight of
`K` were zero the previous theorem would force the Gaussian mass of `K` to vanish, which
`lintegral_gaussianWeight_ne_zero_of_unitBall_subset` forbids. -/
theorem ellGaussianMeasure_univ_ne_zero_of_shrunken (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {δ s : ℝ}
    (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) (hs : 0 < s) :
    ellGaussianMeasure K δ s Set.univ ≠ 0 := by
  intro hcon
  have h := half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ hn hK hKc hball hδ hδn hs
  rw [hcon, le_zero_iff, mul_eq_zero] at h
  rcases h with h | h
  · exact (ENNReal.ofReal_pos.2 (by norm_num)).ne' h
  · exact lintegral_gaussianWeight_ne_zero_of_unitBall_subset hball hs h

/-- **`lem:speedy-to-ball`, Gaussian, with `hlam` and `hZ0` discharged**:

    a₀ · ∑_{i<t} ∫⁻ (ℓ·a)⁻¹ dQᵢ  ≤  2 · (t · M).

Only `hwarm` remains as an unproved binder; the `λ` of Cousins–Vempala's bound is now the
*proved* `1/2` of §7, which is where the factor `2` comes from.  The bound on `vol K` is also
gone: it follows from `hKR`, since a body of radius `R` sits inside a closed ball.

Assumes `n ≥ 1`, `MeasurableSet K`, `Convex ℝ K`, `B(0,1) ⊆ K`, `0 < δ ≤ 1/(2n)`, `s > 0`,
`R ≥ 0`, `hKR : ∀ x ∈ K, ‖x‖ ≤ R` and `hwarm`. -/
theorem mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le_uncond
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {δ s : ℝ}
    (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) (hs : 0 < s) {R : ℝ} (hR : 0 ≤ R)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) {M : ℝ≥0∞} {Q₀ : Measure (EuclideanSpace ℝ (Fin n))}
    (hwarm : IsWarm M Q₀ (ellGaussianProb K δ s)) (t : ℕ) :
    ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
        * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
            ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i)
      ≤ 2 * ((t : ℝ≥0∞) * M) := by
  have hKtop : volume K ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top
      (x := (0 : EuclideanSpace ℝ (Fin n))) (r := R)).ne (measure_mono fun x hx => ?_)
    simpa [Metric.mem_closedBall, dist_zero_right] using hKR x hx
  have hZ0 := ellGaussianMeasure_univ_ne_zero_of_shrunken hn hK hKc hball hδ hδn hs
  have hZtop : ellGaussianMeasure K δ s Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (ellGaussianMeasure_univ_le hs K δ)
  have hlam := half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ hn hK hKc hball
    hδ hδn hs
  have hcore := mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le hK hδ hs
    hR hKR hZ0 hZtop hlam hwarm t
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 1 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
        * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
            ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i)
      = 2 * (ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
          * ENNReal.ofReal (1 / 2)
          * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
              ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i)) := by
        rw [show (2 : ℝ≥0∞) * (ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
              * ENNReal.ofReal (1 / 2)
              * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
                  ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i))
            = (2 * ENNReal.ofReal (1 / 2))
              * (ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
                * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
                    ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i)) from by ring,
          h2, one_mul]
    _ ≤ 2 * ((t : ℝ≥0∞) * M) := by gcongr

/-- **The Cousins–Vempala regime with *both* constants proved**: at `s = σ²`, `δ ≤ 1/(2n)`,
`δ ≤ σ/(8√n)`, `R ≤ 2σ√n`, `n ≥ 2` and `B(0,1) ⊆ K` convex,

    3 · ∑_{i<t} ∫⁻ (ℓ·a)⁻¹ dQᵢ  ≤  10 · (t · M),   i.e.   ∑ ≤ (10/3)·t·M.

`10/3 = 2 · (5/3)`: the `2` is the proved `λ ≥ 1/2` of §7 and the `5/3` is the proved
acceptance floor `a ≥ 3/5` of §6.  **`hwarm` is the only hypothesis of this statement that is
not a geometric guard**; nothing else is assumed. -/
theorem three_mul_sum_lintegral_le_ten_mul_of_cv (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {δ σ R : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hδn : δ ≤ 1 / (2 * (n : ℝ)))
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hR : 0 ≤ R) (hRσ : R ≤ 2 * σ * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) {M : ℝ≥0∞} {Q₀ : Measure (EuclideanSpace ℝ (Fin n))}
    (hwarm : IsWarm M Q₀ (ellGaussianProb K δ (σ ^ 2))) (t : ℕ) :
    3 * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
          ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i)
      ≤ 10 * ((t : ℝ≥0∞) * M) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have huncond := mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le_uncond
    (le_trans (by norm_num) hn) hK hKc hball hδ hδn hs hR hKR hwarm t
  have hfloor := three_le_five_mul_acceptance_floor_of_cv (R := R) hn hσ hδ hδσ hRσ
  calc 3 * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
          ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i)
      ≤ 5 * ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)))
          * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
              ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i) := by gcongr
    _ = 5 * (ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)))
          * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
              ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i)) := by ring
    _ ≤ 5 * (2 * ((t : ℝ≥0∞) * M)) := by gcongr
    _ = 10 * ((t : ℝ≥0∞) * M) := by ring

/-! ## 8. Non-vacuity

`CLAUDE.md` §11: a theorem whose hypotheses nothing satisfies certifies nothing.  There are two
witnesses, with **disjoint scopes**, because §7 restricts `δ` in a way §§1–6 do not:

* `exists_wastedStepsGaussian_witness` discharges the binders of **§§1–6** — the unit ball with
  any `0 < δ ≤ 1/2` and any `s > 0`, started at stationarity, with `λ` non-zero and finite and
  `M = 1`.  It does **not** satisfy §7's `hδn : δ ≤ 1/(2n)`, which is false at `δ = 1/2` for
  `n ≥ 2`, and it claims nothing about §7.
* `exists_wastedStepsGaussian_uncond_witness` discharges the binders of **§7** — the unit ball
  at `δ = 1/(2n)`, `σ = 1`, `R = 1`, for `n ≥ 16`.

Unlike `WastedSteps.lean`'s witness the bound is **not attained** in either, and neither witness
pretends otherwise: the acceptance floor `a₀ ≤ a(x)` has genuine slack (it is a uniform floor on
a function that varies over `K`), so no equality is claimed.  What *is* claimed, and proved, is
that every hypothesis is met, that the left-hand side is strictly positive and finite, and that
the acceptance factor is not vacuously `1` — the filter really does reject. -/

/-- **The non-vacuity witness.**  For every dimension `n ≥ 1`, every step `0 < δ ≤ 1/2`, every
variance `s > 0` and every `t ≥ 1` there are a body `K` — the unit ball — a radius `R`, a start
`Q₀`, a `λ` and an `M` such that

* `K` is measurable and `∀ x ∈ K, ‖x‖ ≤ R` with `R = 1`, so the acceptance floor applies;
* `0 < ∫_K ℓ·g < ⊤`, so `ellGaussianProb K δ s` is a genuine probability measure and the two
  guards `hZ0`, `hZtop` hold;
* `λ ≠ 0` and `λ ≠ ⊤`, so the divided form applies and its right-hand side is not `⊤`;
* `hlam` holds **with equality** — `λ` is the *exact* `g`-weighted average local conductance
  `(∫_K ℓ·g)/(∫_K g)`, so the witness makes no concession on Cousins–Vempala's `λ`-hypothesis;
* `hwarm` holds with `M = 1`, the best possible warmness (the chain is started at stationarity);
* the acceptance is **strictly between `0` and `1`** at the centre — so the extra factor this
  file introduces is real, not a vacuous `a ≡ 1` (`speedyMetropolisMove_unitBall_lt_one`);
* the left-hand sum is **at least `t`**, hence strictly positive, and **finite**;
* the conclusion of the core theorem holds.

`[NeZero n]` is needed for the strict-rejection conjunct only. -/
theorem exists_wastedStepsGaussian_witness [NeZero n] {δ s : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hs : 0 < s) {t : ℕ} (ht : 1 ≤ t) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (R : ℝ)
      (Q₀ : Measure (EuclideanSpace ℝ (Fin n))) (lam M : ℝ≥0∞),
      MeasurableSet K ∧ 0 ≤ R ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧
        ellGaussianMeasure K δ s Set.univ ≠ 0 ∧ ellGaussianMeasure K δ s Set.univ ≠ ⊤ ∧
        IsProbabilityMeasure (ellGaussianProb K δ s) ∧ IsProbabilityMeasure Q₀ ∧
        lam ≠ 0 ∧ lam ≠ ⊤ ∧ M = 1 ∧
        lam * (∫⁻ x in K, gaussianWeight s x) = ellGaussianMeasure K δ s Set.univ ∧
        IsWarm M Q₀ (ellGaussianProb K δ s) ∧
        0 < speedyMetropolisMove K δ s 0 ∧ speedyMetropolisMove K δ s 0 < 1 ∧
        (t : ℝ≥0∞) ≤ ∑ i ∈ Finset.range t,
            ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
              ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i) ∧
        0 < ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
              ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i) ∧
        (∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
              ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i)) ≠ ⊤ ∧
        ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * lam
            * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
              ∂(iterate (speedyMetropolisGaussian K δ s) Q₀ i)
          ≤ (t : ℝ≥0∞) * M := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 1 with hKdef
  have hK : MeasurableSet K := measurableSet_ball
  have hδ1 : δ ≤ 1 := by linarith
  have hKR : ∀ x ∈ K, ‖x‖ ≤ (1 : ℝ) := by
    intro x hx
    rw [hKdef, Metric.mem_ball, dist_zero_right] at hx
    exact hx.le
  have hZ0 : ellGaussianMeasure K δ s Set.univ ≠ 0 := ellGaussianMeasure_unitBall_ne_zero hs hδ hδ2
  have hZtop : ellGaussianMeasure K δ s Set.univ ≠ ⊤ := ellGaussianMeasure_unitBall_ne_top hs
  haveI hprob : IsProbabilityMeasure (ellGaussianProb K δ s) :=
    isProbabilityMeasure_ellGaussianProb hZ0 hZtop
  -- the total Gaussian weight of `K` is positive and finite
  have hvol : volume K ≠ ⊤ := volume_unitBall_ne_top
  have hGtop : (∫⁻ x in K, gaussianWeight s x) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hvol ?_
    calc ∫⁻ x in K, gaussianWeight s x ≤ ∫⁻ _ in K, (1 : ℝ≥0∞) :=
          setLIntegral_mono' hK fun x _ => gaussianWeight_le_one hs x
      _ = volume K := by rw [setLIntegral_one]
  have hZG : ellGaussianMeasure K δ s Set.univ ≤ ∫⁻ x in K, gaussianWeight s x := by
    rw [ellGaussianMeasure_univ]
    refine lintegral_mono fun x => ?_
    calc ell K δ x * gaussianWeight s x ≤ 1 * gaussianWeight s x := by
          gcongr; exact ell_le_one K δ x
      _ = gaussianWeight s x := one_mul _
  have hG0 : (∫⁻ x in K, gaussianWeight s x) ≠ 0 := by
    intro hcon
    rw [hcon] at hZG
    exact hZ0 (le_antisymm hZG zero_le)
  -- the exact `g`-weighted average local conductance
  set lam : ℝ≥0∞ := ellGaussianMeasure K δ s Set.univ / ∫⁻ x in K, gaussianWeight s x with hlamdef
  have hlameq : lam * (∫⁻ x in K, gaussianWeight s x) = ellGaussianMeasure K δ s Set.univ := by
    rw [hlamdef]
    exact ENNReal.div_mul_cancel hG0 hGtop
  have hlam0 : lam ≠ 0 := by
    rw [hlamdef]
    intro hcon
    rcases ENNReal.div_eq_zero_iff.1 hcon with h | h
    · exact hZ0 h
    · exact hGtop h
  have hlamtop : lam ≠ ⊤ := by
    rw [hlamdef]
    intro hcon
    rcases ENNReal.div_eq_top.1 hcon with ⟨-, h⟩ | ⟨h, -⟩
    · exact hG0 h
    · exact hZtop h
  -- the chain started at stationarity stays there
  have hiter : ∀ i : ℕ, iterate (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) i
      = ellGaussianProb K δ s :=
    iterate_invariant (invariant_speedyMetropolisGaussian hK δ s)
  -- the integrand is at least `1`, so the sum is at least `t`
  have hge1 : ∀ x : EuclideanSpace ℝ (Fin n),
      (1 : ℝ≥0∞) ≤ (ell K δ x * speedyMetropolisMove K δ s x)⁻¹ := by
    intro x
    rw [ENNReal.le_inv_iff_mul_le, one_mul, ← metropolisMove_eq_ell_mul_speedyMetropolisMove]
    exact metropolisMove_le_one K δ s x
  have hsumge : (t : ℝ≥0∞) ≤ ∑ i ∈ Finset.range t,
      ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
        ∂(iterate (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) i) := by
    have hone : ∀ i : ℕ, (1 : ℝ≥0∞) ≤ ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
        ∂(iterate (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) i) := by
      intro i
      calc (1 : ℝ≥0∞)
          = ∫⁻ _x, (1 : ℝ≥0∞)
              ∂(iterate (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) i) := by
            rw [hiter i, lintegral_one, measure_univ]
        _ ≤ _ := lintegral_mono fun x => hge1 x
    calc (t : ℝ≥0∞) = ∑ _i ∈ Finset.range t, (1 : ℝ≥0∞) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun i _ => hone i
  have ht0 : (0 : ℝ≥0∞) < (t : ℝ≥0∞) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ht
  have hbound := mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le
    (R := 1) (M := 1) hK hδ hs zero_le_one hKR hZ0 hZtop (le_of_eq hlameq) (IsWarm.refl _) t
  have ha0 : ENNReal.ofReal (Real.exp (-(2 * 1 * δ + δ ^ 2) / (2 * s))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hfin : (∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
      ∂(iterate (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) i)) ≠ ⊤ := by
    intro hcon
    rw [hcon, ENNReal.mul_top (mul_ne_zero ha0 hlam0)] at hbound
    have htop : ((t : ℝ≥0∞) * 1) = ⊤ := top_le_iff.1 hbound
    rw [mul_one] at htop
    exact (ENNReal.natCast_ne_top t) htop
  exact ⟨K, 1, ellGaussianProb K δ s, lam, 1, hK, zero_le_one, hKR, hZ0, hZtop, hprob, hprob,
    hlam0, hlamtop, rfl, hlameq, IsWarm.refl _,
    speedyMetropolisMove_unitBall_pos hs hδ hδ1, speedyMetropolisMove_unitBall_lt_one hs hδ hδ1,
    hsumge, lt_of_lt_of_le ht0 hsumge, hfin, hbound⟩

/-- **The cost sum is at least `t`, for the chain started at stationarity.**  The integrand
`(ℓ·a)⁻¹` is at least `1` everywhere (`ℓ·a = metropolisMove ≤ 1`) and each `Qᵢ` is the
stationary probability measure, so every summand is at least `1`.  This is what makes the
left-hand side of every bound above strictly positive rather than vacuously `0`. -/
theorem le_sum_lintegral_inv_ell_mul_move_iterate_stationary
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    [IsProbabilityMeasure (ellGaussianProb K δ s)] (t : ℕ) :
    (t : ℝ≥0∞) ≤ ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
        ∂(iterate (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) i) := by
  have hiter : ∀ i : ℕ, iterate (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) i
      = ellGaussianProb K δ s :=
    iterate_invariant (invariant_speedyMetropolisGaussian hK δ s)
  have hone : ∀ i : ℕ, (1 : ℝ≥0∞) ≤ ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
      ∂(iterate (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) i) := by
    intro i
    calc (1 : ℝ≥0∞)
        = ∫⁻ _x, (1 : ℝ≥0∞)
            ∂(iterate (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) i) := by
          rw [hiter i, lintegral_one, measure_univ]
      _ ≤ _ := by
          refine lintegral_mono fun x => ?_
          rw [ENNReal.le_inv_iff_mul_le, one_mul,
            ← metropolisMove_eq_ell_mul_speedyMetropolisMove]
          exact metropolisMove_le_one K δ s x
  calc (t : ℝ≥0∞) = ∑ _i ∈ Finset.range t, (1 : ℝ≥0∞) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    _ ≤ _ := Finset.sum_le_sum fun i _ => hone i

/-- **Non-vacuity for the fully discharged statements of §7.**  For every dimension `n ≥ 16`
and every `t ≥ 1`, the unit ball with

    δ = 1/(2n),   σ = 1,   R = 1,   Q₀ = ellGaussianProb K δ 1,   M = 1

satisfies *every* binder of `three_mul_sum_lintegral_le_ten_mul_of_cv` simultaneously — note
that `hlam` is no longer among them, and the theorem's own conclusion `λ ≥ 1/2` is exhibited —
and the left-hand side is at least `t`, so the bound `3·∑ ≤ 10·t` is a genuine sandwich
`t ≤ ∑ ≤ (10/3)·t` and not the vacuous `0 ≤ anything`.

`n ≥ 16` is what reconciles the two step-size constraints at `σ = 1`: `δ ≤ 1/(2n)` and
`δ ≤ σ/(8√n)` are compatible at `δ = 1/(2n)` exactly when `4 ≤ √n`.  This is the same tension
`SamplerStepCount.lean` records as `4 ≤ σ√n`; it is a constraint on the witness, not on the
theorems, which take the two bounds as separate binders. -/
theorem exists_wastedStepsGaussian_uncond_witness (hn : 16 ≤ n) {t : ℕ} (ht : 1 ≤ t) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (δ σ R : ℝ)
      (Q₀ : Measure (EuclideanSpace ℝ (Fin n))) (M : ℝ≥0∞),
      MeasurableSet K ∧ Convex ℝ K ∧ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K ∧
        0 < δ ∧ 0 < σ ∧ δ ≤ 1 / (2 * (n : ℝ)) ∧ δ ≤ σ / (8 * Real.sqrt n) ∧
        0 ≤ R ∧ R ≤ 2 * σ * Real.sqrt n ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧ M = 1 ∧
        IsProbabilityMeasure (ellGaussianProb K δ (σ ^ 2)) ∧
        IsProbabilityMeasure Q₀ ∧ IsWarm M Q₀ (ellGaussianProb K δ (σ ^ 2)) ∧
        ENNReal.ofReal (1 / 2) * (∫⁻ x in K, gaussianWeight (σ ^ 2) x)
          ≤ ellGaussianMeasure K δ (σ ^ 2) Set.univ ∧
        (t : ℝ≥0∞) ≤ ∑ i ∈ Finset.range t,
            ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
              ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i) ∧
        0 < ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
              ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i) ∧
        3 * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
              ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i)
          ≤ 10 * ((t : ℝ≥0∞) * M) := by
  classical
  have hn1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hs0 : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have h4 : (4 : ℝ) ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := by linarith
  set K : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 1 with hKdef
  have hK : MeasurableSet K := measurableSet_ball
  have hKc : Convex ℝ K := convex_ball _ _
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K := subset_rfl
  have hKR : ∀ x ∈ K, ‖x‖ ≤ (1 : ℝ) := by
    intro x hx
    rw [hKdef, Metric.mem_ball, dist_zero_right] at hx
    exact hx.le
  have hδ : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
  have hδσ : 1 / (2 * (n : ℝ)) ≤ (1 : ℝ) / (8 * Real.sqrt (n : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hσsq : ((1 : ℝ)) ^ 2 = (1 : ℝ) := one_pow 2
  have hs : (0 : ℝ) < ((1 : ℝ)) ^ 2 := by norm_num
  have hZ0 := ellGaussianMeasure_univ_ne_zero_of_shrunken hn1 hK hKc hball hδ le_rfl hs
  have hKtop : volume K ≠ ⊤ := volume_unitBall_ne_top
  have hZtop : ellGaussianMeasure K (1 / (2 * (n : ℝ))) ((1 : ℝ) ^ 2) Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (ellGaussianMeasure_univ_le hs K _)
  haveI hprob : IsProbabilityMeasure (ellGaussianProb K (1 / (2 * (n : ℝ))) ((1 : ℝ) ^ 2)) :=
    isProbabilityMeasure_ellGaussianProb hZ0 hZtop
  have hlam := half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ hn1 hK hKc hball
    hδ le_rfl hs
  have hsumge := le_sum_lintegral_inv_ell_mul_move_iterate_stationary hK
    (1 / (2 * (n : ℝ))) ((1 : ℝ) ^ 2) t
  have ht0 : (0 : ℝ≥0∞) < (t : ℝ≥0∞) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ht
  have hmain := three_mul_sum_lintegral_le_ten_mul_of_cv (n := n) (M := 1)
    (le_trans (by norm_num) hn) hK hKc hball hδ (by norm_num : (0:ℝ) < 1) le_rfl hδσ
    zero_le_one (by nlinarith) hKR (IsWarm.refl _) t
  exact ⟨K, 1 / (2 * (n : ℝ)), 1, 1,
    ellGaussianProb K (1 / (2 * (n : ℝ))) ((1 : ℝ) ^ 2), 1,
    hK, hKc, hball, hδ, by norm_num, le_rfl, hδσ, zero_le_one, by nlinarith, hKR, rfl,
    hprob, hprob, IsWarm.refl _, hlam, hsumge, lt_of_lt_of_le ht0 hsumge, hmain⟩

/-! ## Axiom audit (`CLAUDE.md` §4)

Every theorem of this file, re-checked at elaboration time.  Each must print exactly
`[propext, Classical.choice, Quot.sound]`; anything else — in particular `sorryAx` — means the
file is not finished. -/

#print axioms mul_inv_le_one_of_le
#print axioms metropolisMove_eq_ell_mul_speedyMetropolisMove
#print axioms metropolisGaussian_apply_singleton
#print axioms pathMeasure_metropolisGaussian_dirac_holdsUntil
#print axioms tsum_pathMeasure_metropolisGaussian_dirac_holdsUntil
#print axioms lintegral_exitTime_pathMeasure_metropolisGaussian
#print axioms acceptance_floor_le_speedyMetropolisMove
#print axioms ae_restrict_acceptance_floor_le_speedyMetropolisMove
#print axioms lintegral_inv_ell_mul_move_ellGaussianMeasure
#print axioms mul_lintegral_gaussianWeight_le_of_le_div
#print axioms mul_mul_lintegral_inv_ell_mul_move_ellGaussianProb_le_one
#print axioms mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le
#print axioms sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le
#print axioms lintegral_lintegral_exitTime_pathMeasure_metropolisGaussian
#print axioms mul_sum_lintegral_exitTime_iterate_speedyMetropolisGaussian_le
#print axioms three_le_five_mul_acceptance_floor_of_cv
#print axioms three_mul_sum_lintegral_le_five_mul_of_cv
#print axioms lintegral_gaussianWeight_ne_zero_of_unitBall_subset
#print axioms half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ
#print axioms ellGaussianMeasure_univ_ne_zero_of_shrunken
#print axioms mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le_uncond
#print axioms three_mul_sum_lintegral_le_ten_mul_of_cv
#print axioms le_sum_lintegral_inv_ell_mul_move_iterate_stationary
#print axioms exists_wastedStepsGaussian_witness
#print axioms exists_wastedStepsGaussian_uncond_witness

end Arlib.MarkovChains
