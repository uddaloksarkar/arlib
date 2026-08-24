/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.SamplerStepCount

/-!
# The cold phases, at the step size `δ = min(σ/(8√n), 1/(2n))`

## Scope — read this first

Exactly the scope of `Arlib/MarkovChains/Continuous/SamplerStepCount.lean`: what is proved
here is an **arithmetic/accounting result about step counts already proved elsewhere**, at a
different step size.  There is no cost model, no machine model and no running-time claim, and
nothing under `Ttc/` is edited, imported or referred to.  A step count is not a running time.

## The gap this file closes

`SamplerStepCount.lean` fixes `δ = 1/(2n)` — the regime at which
`Arlib/MarkovChains/Continuous/KLS97Shell.lean`'s two Kannan–Lovász–Simonovits inputs become
provable outright — and observes that the mixing theorem's own binder `hδσ : δ ≤ σ/(8√n)` then
reads *exactly* `4 ≤ σ·√n`.  `Arlib/Convexity/GaussianCooling/ColdStart.lean` starts the
annealing schedule at `σ²₀ = 1/n`, where `σ₀·√n = 1 < 4`.  **So the earliest phases satisfy
neither constraint at `δ = 1/(2n)`**, and `SamplerStepCount.lean` records this as an open gap.

The repair is to take the step size that meets **both** constraints at once,

    `δ(σ) := min (σ/(8√n)) (1/(2n))`,

which is legal at *every* `σ > 0` with no side condition whatever.  Everything below is stated
at that `δ`, and **no theorem in this file carries `hσn : 4 ≤ σ·√n`**.

## The two regimes, and the exponents

`min` splits by which constraint binds, at the threshold `σ·√n = 4`:

| regime | `δ` | `σ²·n/δ²` | per-phase deadline | dimension exponent |
| --- | --- | --- | --- | --- |
| **cold**, `σ·√n ≤ 4` | `σ/(8√n)` | `64·n²` | `104857600·n²·X/(log 2)² + 1` | **`n²`** |
| **warm**, `4 ≤ σ·√n` | `1/(2n)` | `4·σ²·n³` | `6553600·σ²·n³·X/(log 2)² + 1` | **`n³`** |

with `X := log M + 2·log(1/ε)`, `104857600 = 4·640²·64` and `6553600 = 4·640²·4`.  Both stay
polynomial; the warm line is verbatim `SamplerStepCount.lean`'s
`mixesWithin_lazy_speedyMetropolisGaussian_kls`, which this file reuses rather than re-proves.

**The cold phases are strictly cheaper, not more expensive** — this is
`coldCount_le_warmCount` below.  Two reasons, both visible in the table:

* the cold count has dimension exponent `n²`, one power of `n` *less* than the warm count;
* it is **free of `σ`** altogether: shrinking the step in proportion to `σ` cancels the `σ²`
  in the numerator exactly, so every cold phase costs the same `104857600·n²·X/(log 2)²`.

At the threshold `σ²n = 16` the two agree, and for every warm `σ` the warm count is the larger.
So the phases `SamplerStepCount.lean` had to exclude are the *cheapest* ones in the schedule,
and the accounting simplifies: the maximum over phases is attained in the warm range.

## The uniform statement

`1/min(a,b)² ≤ 1/a² + 1/b²` gives a single deadline valid at **every** `σ > 0`, cold and warm:

    `6553600·(σ²·n³ + 16·n²)·X / (log 2)² + 1`.

It is the warm deadline plus the cold one, so it is within a factor `2` of the truth in either
regime (in the warm regime `σ²n ≥ 16` makes the `16n²` term the smaller of the two).  Because
it is monotone in `σ`, one budget computed at a dominating `σmax` serves the whole schedule —
`mixesWithin_all_phases_coldStep` — and the total is the clean product
`m · ⌈deadline(σmax)⌉₊` of §4.

A pleasant side effect: `SamplerStepCount.lean`'s `total_speedy_steps_poly` needed `hσn` to
know `σmax²n³ ≥ 7056`, which is what lets the constant `13653334` absorb the `+2` of the
ceiling.  Here `σmax²n³ + 16n² ≥ 16n² ≥ 7056` holds at `n ≥ 21` **unconditionally**, so the
same constants come out with no hypothesis at all.

## What each section delivers

1. **The step size** — `coldStep_pos`, `coldStep_le_conductance`, `coldStep_le_kls`,
   `coldStep_valid`; the regime identifications `coldStep_eq_cold`, `coldStep_eq_warm`; and the
   *typed* KLS97 instantiations `ell_eq_one_on_shrunken_coldStep`,
   `half_le_speedy_shrunken_coldStep`, which check the regime by elaboration rather than by
   argument.
2. **Per phase** — `mixesWithin_lazy_speedyMetropolisGaussian_coldStep` (uniform),
   `mixesWithin_lazy_speedyMetropolisGaussian_cold` (the `n²` count),
   `mixesWithin_lazy_speedyMetropolisGaussian_warm` (the `n³` count, from
   `SamplerStepCount.lean`), and `coldCount_le_warmCount`.
3. **All phases at one budget** — `mixesWithin_all_phases_coldStep`.
4. **Total** — `total_speedy_steps_coldStep_le`, `total_speedy_steps_coldStep_poly`,
   `total_speedy_steps_coldStep_poly_varBudget`.
5. **Non-vacuity** — `cold_phase_regime_witness`, at a genuinely **cold** phase.

## Hypotheses carried unproved

`hσn` is gone.  The rest of `SamplerStepCount.lean`'s list is inherited unchanged and is *not*
repaired here:

* **`hwarm : IsWarm (ofReal M) μⱼ (ellGaussianProb K δ σⱼ²)`** — the per-phase warm start.
  `WarmChain.lean` proves `n`-free warmness of `coolLaw i` for `coolLaw (i+1)`; the bridge to
  the speedy chain's own stationary law `ellGaussianProb` (an extra factor `ℓ`) is **not proved
  in this repository**, and `EllFloor.lean` rules out the obvious route (there is no uniform
  pointwise floor on `ell`: `ell ≤ 2⁻ⁿ` at a cube corner, at every `δ`).
* **`hm`** — the identification of `ColdStart.lean`'s existentially-bound phase count with
  `generalPhaseCount n κ L'`.
* **`hsigmax`** — that `σmax` dominates every phase's `σⱼ`.
* **`hRσ : R ≤ 2·σ·√n`** — inherited from `conductance_speedyMetropolisGaussian_ge_uncond`,
  where it is the isoperimetric compatibility "the body fits inside the Gaussian's effective
  radius" (`IsoIndicator.lean:83`).  **This is a residual restriction on exactly the phases
  this file is about, and it is worth stating plainly.**  At `ColdStart.lean`'s initial variance
  `σ²₀ = 1/n` it reads `R ≤ 2`: the cold phases are in-regime only for bodies of radius at most
  `2`.  Choosing a smaller `δ` does not touch it — `hRσ` is a hypothesis of the isoperimetry,
  not of the step size — so a body with `B(0,1) ⊆ K ⊆ B(0,R)` and `R > 2` still falls outside
  the per-phase theorem at its coldest variances.  Nothing here repairs that; it is recorded in
  the spirit of `CLAUDE.md` §5, as `SamplerStepCount.lean` recorded the `hσn` gap.

## Audit surface (`CLAUDE.md` §11)

* **Capstones**: `mixesWithin_lazy_speedyMetropolisGaussian_coldStep` (§2),
  `mixesWithin_all_phases_coldStep` (§3), `total_speedy_steps_coldStep_poly_varBudget` (§4).
  Read the types only.
* **Hypotheses carried unproved**: the four listed above, each an inline binder.
* **Non-vacuity**: `cold_phase_regime_witness`, which runs a **two-phase** schedule at `n = 21`,
  `K = B(0,1)`, `R = 1`, with `σ₀ = 1/√21` — so `σ₀² = 1/n` *exactly* `ColdStart.lean`'s
  initial variance and `σ₀·√n = 1 < 4`, a genuinely cold phase, the very phase
  `SamplerStepCount.lean` had to exclude — and `σ₁ = 100` warm, carrying the uniform mixing
  conclusion at both, the cold `n²` conclusion at phase `0`, and the numeric total.
* **Semantic `def`s**: none.  This file introduces no `def`, no `structure`, no `class`, no
  `axiom` and no named `Prop`; both the step size and every step count are written out in the
  statements that use them, so no name stands in for a proof.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1. The step size that meets both regimes

`δ(σ) = min (σ/(8√n)) (1/(2n))`.  The two facts are `min_le_left` and `min_le_right`; they are
stated as named lemmas, and then *used* to instantiate the two KLS97 theorems, so that the
regime is checked by elaboration rather than argued in prose. -/

/-- **The step size is positive**, for every `σ > 0` and every `n ≥ 1`. -/
theorem coldStep_pos (hn : 1 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    0 < min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  exact lt_min (by positivity) (by positivity)

/-- **The conductance regime**: `δ ≤ σ/(8√n)`, the binder `hδσ` of
`Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit`. -/
theorem coldStep_le_conductance {σ : ℝ} :
    min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) ≤ σ / (8 * Real.sqrt n) :=
  min_le_left _ _

/-- **The KLS97 shell regime**: `δ ≤ 1/(2n)`, the binder `hδn` of
`Arlib.MarkovChains.half_le_speedy_shrunken` and the `hδc` of
`Arlib.MarkovChains.ell_eq_one_on_shrunken` at `c = 1 − 1/(2n)`. -/
theorem coldStep_le_kls {σ : ℝ} :
    min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) ≤ 1 / (2 * (n : ℝ)) :=
  min_le_right _ _

/-- **Both regimes at once, for every `σ > 0`.**

Positivity, the conductance constraint `δ ≤ σ/(8√n)` and the KLS97 constraint `δ ≤ 1/(2n)`,
with **no side condition on `σ`** — in particular none of the form `4 ≤ σ√n`.  This is the
one-line fact that removes `SamplerStepCount.lean`'s `hσn`. -/
theorem coldStep_valid (hn : 1 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    0 < min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))
      ∧ min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) ≤ σ / (8 * Real.sqrt n)
      ∧ min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) ≤ 1 / (2 * (n : ℝ)) :=
  ⟨coldStep_pos hn hσ, coldStep_le_conductance, coldStep_le_kls⟩

/-- **In the cold regime `σ·√n ≤ 4` the conductance constraint binds**: `δ = σ/(8√n)`.

`σ/(8√n) ≤ 1/(2n)` is, after clearing denominators, `2σn ≤ 8√n`, i.e. `σ√n ≤ 4`. -/
theorem coldStep_eq_cold (hn : 1 ≤ n) {σ : ℝ} (hcold : σ * Real.sqrt n ≤ 4) :
    min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) = σ / (8 * Real.sqrt n) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  refine min_eq_left ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hcold) hspos.le]

/-- **In the warm regime `4 ≤ σ·√n` the KLS97 constraint binds**: `δ = 1/(2n)`, which is
`SamplerStepCount.lean`'s step size.  So the two files agree wherever both apply. -/
theorem coldStep_eq_warm (hn : 1 ≤ n) {σ : ℝ} (hwarm : 4 ≤ σ * Real.sqrt n) :
    min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) = 1 / (2 * (n : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  refine min_eq_right ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hwarm) hspos.le]

/-- **KLS97 fact 2 at this step size**: `ℓ ≡ 1` on the shrunken body `(1 − 1/(2n))·K`.

`Arlib.MarkovChains.ell_eq_one_on_shrunken` at `c = 1 − 1/(2n)` and `δ = min(σ/(8√n), 1/(2n))`.
The point of stating it is that the regime hypothesis is discharged by `coldStep_le_kls` — the
`δ ≤ 1 − c` binder is met by elaboration, for every `σ > 0`, with no `hσn`. -/
theorem ell_eq_one_on_shrunken_coldStep (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {σ : ℝ} (hσ : 0 < σ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (1 - 1 / (2 * (n : ℝ))) • K) :
    ell K (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) x = 1 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
  have hhalf : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ell_eq_one_on_shrunken hKc hball (by linarith) (by linarith)
    (coldStep_pos hn hσ) ?_ hx
  rw [sub_sub_cancel]
  exact coldStep_le_kls

/-- **KLS97 fact 1 at this step size**: the Gaussian-weighted speedy law keeps at least half its
mass on the shrunken body `(1 − 1/(2n))·K`.

`Arlib.MarkovChains.half_le_speedy_shrunken` at `δ = min(σ/(8√n), 1/(2n))`; again the regime
binder `hδn` is discharged by `coldStep_le_kls`, for every `σ > 0`. -/
theorem half_le_speedy_shrunken_coldStep (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) :
    ENNReal.ofReal (1 / 2)
        * ∫⁻ x in K, ell K (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) x
            * gaussianWeight s x
      ≤ ∫⁻ x in (1 - 1 / (2 * (n : ℝ))) • K,
          ell K (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) x * gaussianWeight s x :=
  half_le_speedy_shrunken hn hK hKc hball (coldStep_pos hn hσ) coldStep_le_kls hs

/-! ## 2. The per-phase step count at that step size

The mixing deadline of `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit` is
`4·640²·σ²·n·X/(δ·log 2)² + 1`.  Substituting `δ = min(a,b)` and using `1/min(a,b)² ≤ 1/a²+1/b²`
gives one deadline valid at every `σ`; substituting the individual branch gives the sharper
regime-specific count. -/

/-- **`C/min(a,b)² ≤ C/a² + C/b²` for `C ≥ 0`.**  The whole content of the uniform bound: `min`
is one of its arguments, and the other term is nonnegative. -/
theorem div_min_sq_le {a b C : ℝ} (hC : 0 ≤ C) :
    C / min a b ^ 2 ≤ C / a ^ 2 + C / b ^ 2 := by
  rcases min_cases a b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · have : 0 ≤ C / b ^ 2 := div_nonneg hC (sq_nonneg b)
    linarith
  · have : 0 ≤ C / a ^ 2 := div_nonneg hC (sq_nonneg a)
    linarith

/-- **The deadline at `δ = min(σ/(8√n), 1/(2n))`, bounded uniformly in `σ`.**

    `4·640²·σ²·n·X/(δ·log 2)² ≤ 6553600·(σ²·n³ + 16·n²)·X/(log 2)²`.

The two summands on the right are exactly the two branches: `6553600·σ²n³` is the warm one
(`1/b² = 4n²`) and `6553600·16·n² = 104857600·n²` the cold one (`1/a² = 64n/σ²`, which cancels
the `σ²`). -/
theorem coldStep_deadline_le (hn : 21 ≤ n) {σ X : ℝ} (hσ : 0 < σ) (hX : 0 ≤ X) :
    4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * X
        / (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) * Real.log 2) ^ 2
      ≤ 6553600 * (σ ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2) * X / Real.log 2 ^ 2 := by
  have hnR : (21 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogne : Real.log 2 ≠ 0 := ne_of_gt hlogpos
  have hlog2 : (0 : ℝ) < Real.log 2 ^ 2 := by positivity
  have hN : (0 : ℝ) ≤ 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * X := mul_nonneg (by positivity) hX
  have hrw : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * X
        / (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) * Real.log 2) ^ 2
      = 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * X / Real.log 2 ^ 2
        / min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) ^ 2 := by
    rw [mul_pow, div_div, mul_comm (Real.log 2 ^ 2)]
  rw [hrw]
  refine le_trans (div_min_sq_le (div_nonneg hN hlog2.le)) (le_of_eq ?_)
  have ha2 : (σ / (8 * Real.sqrt n)) ^ 2 = σ ^ 2 / (64 * (n : ℝ)) := by
    rw [div_pow, mul_pow, hsq]; norm_num
  have hb2 : (1 / (2 * (n : ℝ))) ^ 2 = 1 / (4 * (n : ℝ) ^ 2) := by
    rw [div_pow, mul_pow]; norm_num
  rw [ha2, hb2]
  field_simp
  ring

/-- **The per-phase speedy step count at `δ = min(σ/(8√n), 1/(2n))`, uniformly in `σ`.**

The lazy speedy Metropolis–Gaussian chain at that step size mixes to within `ε` of its own
stationary law from an `M`-warm start after

    `t ≥ 6553600·(σ²·n³ + 16·n²)·(log M + 2·log(1/ε)) / (log 2)² + 1`

steps, **for every `σ > 0`** — cold and warm alike.  Every binder is
`Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit`'s except that `hδ` and `hδσ`
are discharged internally (`coldStep_pos`, `coldStep_le_conductance`) and there is **no**
`hσn : 4 ≤ σ√n`: that is the whole point of the file.  `δ` also meets the KLS97 shell regime,
by `coldStep_le_kls`.

This is a step-count statement about a Markov chain, not a running time; see the module
docstring's scope paragraph. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_coldStep (hn : 21 ≤ n) {σ R : ℝ}
    (hσ : 0 < σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (ellGaussianProb K (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 6553600 * (σ ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2)
      * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin
      (lazy (speedyMetropolisGaussian K
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
      (ellGaussianProb K (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)) mu0 t
      (ENNReal.ofReal eps) := by
  have hX : 0 ≤ Real.log M + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log (1 / eps) :=
      Real.log_nonneg (by rw [le_div_iff₀ heps0]; linarith)
    linarith
  refine mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit hn hσ
    (coldStep_pos (by omega) hσ) coldStep_le_conductance hK hKc hK0 hR hKR hRσ hM hwarm
    heps0 heps1 ?_
  have := coldStep_deadline_le hn hσ hX
  linarith

/-- **The cold phases: the sharp count, with dimension exponent `n²` and no `σ` at all.**

At `σ·√n ≤ 4` the step size is `δ = σ/(8√n)` (`coldStep_eq_cold`), and then
`σ²·n/δ² = 64·n²` *identically* — the `σ²` cancels.  So the deadline is

    `t ≥ 104857600·n²·(log M + 2·log(1/ε))/(log 2)² + 1`,   `104857600 = 4·640²·64`,

with **no dependence on `σ`**: every cold phase costs the same, however cold it is.  Compare
`SamplerStepCount.lean`'s warm count `6553600·σ²n³·X/(log 2)² + 1`, one power of `n` worse; see
`coldCount_le_warmCount`. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_cold (hn : 21 ≤ n) {σ R : ℝ}
    (hσ : 0 < σ) (hcold : σ * Real.sqrt n ≤ 4)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (ellGaussianProb K (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 104857600 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin
      (lazy (speedyMetropolisGaussian K
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
      (ellGaussianProb K (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)) mu0 t
      (ENNReal.ofReal eps) := by
  have hnR : (21 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogne : Real.log 2 ≠ 0 := ne_of_gt hlogpos
  have hmin : min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) = σ / (8 * Real.sqrt n) :=
    coldStep_eq_cold (by omega) hcold
  rw [hmin] at hwarm ⊢
  refine mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit hn hσ (by positivity)
    le_rfl hK hKc hK0 hR hKR hRσ hM hwarm heps0 heps1 ?_
  have heq : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
        / (σ / (8 * Real.sqrt n) * Real.log 2) ^ 2
      = 104857600 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, hsq]
    field_simp
    ring
  rw [heq]
  exact ht

/-- **The warm phases at the same step size: `SamplerStepCount.lean`'s count, verbatim.**

At `4 ≤ σ·√n` the step size is `δ = 1/(2n)` (`coldStep_eq_warm`), so this theorem *is*
`Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_kls`, restated with `δ` spelled as
the `min`.  Dimension exponent `n³`.  Nothing new is proved; the point is that the two files
agree on the overlap and that `min` covers the whole schedule. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_warm (hn : 21 ≤ n) {σ R : ℝ}
    (hσ : 0 < σ) (hσn : 4 ≤ σ * Real.sqrt n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (ellGaussianProb K (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 6553600 * σ ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin
      (lazy (speedyMetropolisGaussian K
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
      (ellGaussianProb K (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)) mu0 t
      (ENNReal.ofReal eps) := by
  have hmin : min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) = 1 / (2 * (n : ℝ)) :=
    coldStep_eq_warm (by omega) hσn
  rw [hmin] at hwarm ⊢
  exact mixesWithin_lazy_speedyMetropolisGaussian_kls hn hσ hσn hK hKc hK0 hR hKR hRσ hM hwarm
    heps0 heps1 ht

/-- **The cold phases are cheaper than any warm phase.**

Wherever the warm count applies — i.e. `4 ≤ σ√n`, which is `σ²n ≥ 16` — the cold count is the
smaller of the two:

    `104857600·n²·X ≤ 6553600·σ²·n³·X`.

Equality holds exactly at the threshold `σ²n = 16`.  So dropping `SamplerStepCount.lean`'s
`hσn` does not add a *more* expensive regime at the cold end of `ColdStart.lean`'s schedule; it
adds a strictly *cheaper* one, and the maximum over phases is still attained at the largest
`σ`. -/
theorem coldCount_le_warmCount (hn : 21 ≤ n) {σ X : ℝ} (_hσ : 0 < σ)
    (hσn : 4 ≤ σ * Real.sqrt n) (hX : 0 ≤ X) :
    104857600 * (n : ℝ) ^ 2 * X ≤ 6553600 * σ ^ 2 * (n : ℝ) ^ 3 * X := by
  have hnR : (21 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hs16 : (16 : ℝ) ≤ σ ^ 2 * (n : ℝ) := by nlinarith [hσn, hsq, hspos]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hs16) (sq_nonneg (n : ℝ))) hX]

/-! ## 3. Every phase at one budget

As in `SamplerStepCount.lean` §2, but with the per-phase step size `δⱼ = min(σⱼ/(8√n), 1/(2n))`
and the uniform deadline of §2, which is monotone in `σ`.  **There is no `hsign` binder**: the
family may contain cold phases, warm phases, or both. -/

/-- **All `m` phases mix within the same budget, cold phases included.**

For variances `σ : ℕ → ℝ` and starts `μ : ℕ → Measure _` sharing the body `K`, every phase
`j < m` — running at its own step size `δⱼ = min(σⱼ/(8√n), 1/(2n))` — mixes to within `ε` after

    `t = ⌈6553600·(σmax²·n³ + 16·n²)·(log M + 2·log(1/ε))/(log 2)² + 1⌉₊`

speedy steps, where `σmax` dominates every `σⱼ`.  Compared with
`Arlib.MarkovChains.mixesWithin_all_phases_kls`, the binder `hsign : ∀ j < m, 4 ≤ σⱼ√n` is
**gone** and the deadline has gained the additive `16n²`, which is the cost of covering the
cold phases uniformly (and is dominated by `σmax²n³` as soon as `σmax²n ≥ 16`).

`hwarm` is the residual warm-start binder discussed in the module docstring. -/
theorem mixesWithin_all_phases_coldStep (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) {R : ℝ} (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {m : ℕ} {sig : ℕ → ℝ} {mu : ℕ → Measure (EuclideanSpace ℝ (Fin n))}
    (hmu : ∀ j, IsProbabilityMeasure (mu j))
    (hsig0 : ∀ j < m, 0 < sig j)
    (hRsig : ∀ j < m, R ≤ 2 * sig j * Real.sqrt n)
    {M eps sigmax : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hwarm : ∀ j < m, IsWarm (ENNReal.ofReal M) (mu j)
      (ellGaussianProb K (min (sig j / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (sig j ^ 2)))
    (hsigmax : ∀ j < m, sig j ≤ sigmax) :
    ∀ j < m, MixesWithin
      (lazy (speedyMetropolisGaussian K
        (min (sig j / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (sig j ^ 2)))
      (ellGaussianProb K (min (sig j / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (sig j ^ 2))
      (mu j)
      ⌈6553600 * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2)
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊
      (ENNReal.ofReal eps) := by
  have hX : 0 ≤ Real.log M + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log (1 / eps) :=
      Real.log_nonneg (by rw [le_div_iff₀ heps0]; linarith)
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 ^ 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  intro j hj
  haveI := hmu j
  refine mixesWithin_lazy_speedyMetropolisGaussian_coldStep hn (hsig0 j hj) hK hKc hK0
    hR hKR (hRsig j hj) hM (hwarm j hj) heps0 heps1 ?_
  have hsq : sig j ^ 2 ≤ sigmax ^ 2 := by
    nlinarith [hsig0 j hj, hsigmax j hj]
  have hn3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hmono : 6553600 * (sig j ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2)
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2
      ≤ 6553600 * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2)
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 := by
    rw [div_le_div_iff₀ hlog2 hlog2]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 hsq) hn3) hX) hlog2.le]
  have hceil := Nat.le_ceil (6553600 * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2)
    * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1)
  linarith

/-! ## 4. The total over phases

A clean product: one phase count times one budget.  `m` is a number of phases and `t` a number
of speedy steps; the product is a number of speedy steps and nothing else — no cost model is
involved. -/

/-- **`m·⌈D+1⌉₊ ≤ A·(D+2)`** whenever `m ≤ A` and `0 ≤ D`.  The accounting step, isolated. -/
theorem nat_mul_ceil_le {m : ℕ} {A D : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) (hm : (m : ℝ) ≤ A) :
    ((m * ⌈D + 1⌉₊ : ℕ) : ℝ) ≤ A * (D + 2) := by
  have hceil : ((⌈D + 1⌉₊ : ℕ) : ℝ) ≤ D + 2 := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ D + 1)
    linarith
  push_cast
  exact mul_le_mul hm hceil (Nat.cast_nonneg _) hA

/-- **Total speedy steps: phase count times per-phase budget, at the cold-safe step size.**

`m·t ≤ (32(n+1)L²/κ + 1)·(D + 2)` with `D` §3's deadline and `t = ⌈D + 1⌉₊`, where
`32(n+1)L²/κ + 1` is `GeneralRate.lean`'s `generalPhaseCount_le` bound on the phase count
`ColdStart.lean` uses.  `hm` is a binder for the same reason as in `SamplerStepCount.lean`:
`cold_start_annealing_witness` exposes only a *lower* bound on its existential `m`. -/
theorem total_speedy_steps_coldStep_le (hn : 21 ≤ n) {m : ℕ} {sigmax M eps κ L : ℝ}
    (hκ0 : 0 < κ) (hL : 1 ≤ L) (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hm : (m : ℝ) ≤ 32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1) :
    ((m * ⌈6553600 * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2)
          * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ (32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1)
        * (6553600 * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2)
            * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 2) := by
  have hX : 0 ≤ Real.log M + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log (1 / eps) :=
      Real.log_nonneg (by rw [le_div_iff₀ heps0]; linarith)
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 ^ 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hD0 : (0 : ℝ) ≤ 6553600 * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2)
      * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 :=
    div_nonneg (mul_nonneg (by positivity) hX) hlog2.le
  exact nat_mul_ceil_le hD0 (by positivity) hm

/-- **The total speedy step count is bounded by an explicit product of factors.**

    `m·t ≤ 5·10⁸ · (n+1) · (σmax²·n³ + 16·n²) · L² · (1 + log M + 2·log(1/ε)) / κ`.

Exponents: `n⁴` in the warm term (as `(n+1)·σmax²n³`) and `n³` in the cold term (as
`(n+1)·16n²`), together with `σmax²`, `L²`, `κ⁻¹` and one power of `log M`.  The constant is
`33·13653334 = 450560022 ≤ 5·10⁸`, exactly as in `SamplerStepCount.lean`'s
`total_speedy_steps_poly` — but with one hypothesis fewer: there, the absorption of the `+2`
needed `σmax²n³ ≥ 7056`, which came from `hσn`; here `σmax²n³ + 16n² ≥ 16n² ≥ 16·21² = 7056`
holds at `n ≥ 21` unconditionally.  So removing `hσn` costs nothing in the constant. -/
theorem total_speedy_steps_coldStep_poly (hn : 21 ≤ n) {m : ℕ} {sigmax M eps κ L : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hm : (m : ℝ) ≤ 32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1) :
    ((m * ⌈6553600 * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2)
          * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ 5 * 10 ^ 8 * ((n : ℝ) + 1) * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2) * L ^ 2
          * (1 + (Real.log M + 2 * Real.log (1 / eps))) / κ := by
  have hnR : (21 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hX : 0 ≤ Real.log M + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log (1 / eps) :=
      Real.log_nonneg (by rw [le_div_iff₀ heps0]; linarith)
    linarith
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : (0 : ℝ) < Real.log 2 ^ 2 := by positivity
  have hlog048 : (0.48 : ℝ) ≤ Real.log 2 ^ 2 := by
    nlinarith [Real.log_two_gt_d9]
  refine le_trans (total_speedy_steps_coldStep_le hn hκ0 hL hM heps0 heps1 hm) ?_
  set X := Real.log M + 2 * Real.log (1 / eps) with hXdef
  set S := sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2 with hSdef
  -- the cold term alone clears `7056`, with no hypothesis on `sigmax`
  have hbig : (7056 : ℝ) ≤ S := by
    have h1 : (0 : ℝ) ≤ sigmax ^ 2 * (n : ℝ) ^ 3 := by positivity
    have h2 : (441 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    rw [hSdef]; linarith
  have hS0 : (0 : ℝ) ≤ S := by linarith
  have hnum : (0 : ℝ) ≤ 6553600 * S * X := mul_nonneg (by positivity) hX
  have hQ : 6553600 * S * X / Real.log 2 ^ 2 + 2 ≤ 13653334 * S * (1 + X) := by
    have ha : 6553600 * S * X / Real.log 2 ^ 2 ≤ 13653334 * S * X := by
      rw [div_le_iff₀ hlog2]
      nlinarith [mul_nonneg hnum (sub_nonneg.2 hlog048)]
    have hb : (2 : ℝ) ≤ 13653334 * S := by nlinarith
    nlinarith [mul_nonneg hS0 hX]
  have hQ0 : (0 : ℝ) ≤ 6553600 * S * X / Real.log 2 ^ 2 + 2 := by
    have := div_nonneg hnum hlog2.le
    linarith
  have hP : 32 * ((n : ℝ) + 1) * L ^ 2 + κ ≤ 33 * ((n : ℝ) + 1) * L ^ 2 := by
    nlinarith [sq_nonneg (L - 1)]
  have h1X : (0 : ℝ) ≤ 1 + X := by linarith
  rw [le_div_iff₀ hκ0]
  have hrw : (32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1) * (6553600 * S * X / Real.log 2 ^ 2 + 2) * κ
      = (32 * ((n : ℝ) + 1) * L ^ 2 + κ) * (6553600 * S * X / Real.log 2 ^ 2 + 2) := by
    field_simp
  rw [hrw]
  calc (32 * ((n : ℝ) + 1) * L ^ 2 + κ) * (6553600 * S * X / Real.log 2 ^ 2 + 2)
      ≤ (33 * ((n : ℝ) + 1) * L ^ 2) * (13653334 * S * (1 + X)) :=
        mul_le_mul hP hQ hQ0 (by positivity)
    _ = 450560022 * (((n : ℝ) + 1) * S * L ^ 2 * (1 + X)) := by ring
    _ ≤ 5 * 10 ^ 8 * (((n : ℝ) + 1) * S * L ^ 2 * (1 + X)) := by
        refine mul_le_mul_of_nonneg_right (by norm_num) ?_
        have : (0 : ℝ) ≤ ((n : ℝ) + 1) * S * L ^ 2 := by positivity
        exact mul_nonneg this h1X
    _ = 5 * 10 ^ 8 * ((n : ℝ) + 1) * S * L ^ 2 * (1 + X) := by ring

/-- **The same at the volume algorithm's own variance budget `κ = varBudget (ε/2)`.**

    `m·t ≤ 2·10¹⁰ · (n+1) · (σmax²·n³ + 16·n²) · L² · (1 + log M + 2·log(1/ε)) / ε²`.

`Arlib.MarkovChains.sq_div_forty_le_varBudget_le_one` prices `1/κ ≤ 40/ε²`; the constant is
`40·5·10⁸ = 2·10¹⁰`.  This is `SamplerStepCount.lean`'s `total_speedy_steps_poly_varBudget`
with the `hσn` binder removed and `σmax²n³` replaced by `σmax²n³ + 16n²`. -/
theorem total_speedy_steps_coldStep_poly_varBudget (hn : 21 ≤ n) {m : ℕ} {sigmax M eps L : ℝ}
    (hL : 1 ≤ L) (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hm : (m : ℝ) ≤ 32 * ((n : ℝ) + 1) * L ^ 2 / GaussianCooling.varBudget (eps / 2) + 1) :
    ((m * ⌈6553600 * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2)
          * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ 2 * 10 ^ 10 * ((n : ℝ) + 1) * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2) * L ^ 2
          * (1 + (Real.log M + 2 * Real.log (1 / eps))) / eps ^ 2 := by
  obtain ⟨hlow, hhigh⟩ := sq_div_forty_le_varBudget_le_one heps0 heps1
  have hκ0 : 0 < GaussianCooling.varBudget (eps / 2) :=
    GaussianCooling.varBudget_pos (by linarith)
  refine le_trans (total_speedy_steps_coldStep_poly hn hκ0 hhigh hL hM heps0 heps1 hm) ?_
  have hX : 0 ≤ Real.log M + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log (1 / eps) :=
      Real.log_nonneg (by rw [le_div_iff₀ heps0]; linarith)
    linarith
  have hZ : (0 : ℝ) ≤ ((n : ℝ) + 1) * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2) * L ^ 2
      * (1 + (Real.log M + 2 * Real.log (1 / eps))) := by
    have h1 : (0 : ℝ) ≤ ((n : ℝ) + 1) * (sigmax ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2) * L ^ 2 := by
      positivity
    exact mul_nonneg h1 (by linarith)
  rw [div_le_div_iff₀ hκ0 (by positivity)]
  nlinarith [mul_nonneg hZ (sub_nonneg.2 hlow)]

/-! ## 5. Non-vacuity (`CLAUDE.md` §11)

A **two-phase** schedule containing a genuinely cold phase, with every binder of §§1–4
discharged simultaneously. -/

/-- **Non-vacuity, at a genuinely cold phase.**

    `n = 21`,  `K = B(0,1) ⊆ ℝ²¹`,  `R = 1`,  `m = 2`,
    `σ₀ = 1/√21`  (so `σ₀² = 1/n` exactly, and `σ₀·√n = 1 < 4`: **cold**),
    `σ₁ = 100`     (so `σ₁·√n = 100√21 ≥ 4`: warm),  `σmax = 100`,
    `μⱼ = ellGaussianProb K δⱼ σⱼ²`,  `M = 1`,  `ε = 1/2`,  `L = 84`,
    `δⱼ = min(σⱼ/(8√21), 1/42)`,  so `δ₀ = 1/168` and `δ₁ = 1/42`.

Phase `0` is exactly the phase `SamplerStepCount.lean` had to exclude: `ColdStart.lean` starts
the schedule at `σ²₀ = 1/n`, where `hσn : 4 ≤ σ√n` fails (`σ₀√n = 1`).  It is carried here both
by the uniform statement of §3 and by the sharp cold statement of §2, whose budget
`tc = ⌈104857600·21²·2·log 2/(log 2)² + 1⌉₊` is `σ`-free and satisfies `tc ≤ t` — the cold phase
really is the cheaper one.

Nothing is a placeholder: the warm starts are the *stationary* ones (`M = 1`, the best
possible), and `ε = 1/2 < 1`, so the `MixesWithin` conclusions are genuine bounds and not the
trivial `ε = 1` one.  The numeric total is `m·t ≤ 4·10¹⁵`, from `t ≤ 2·10¹⁵`, which holds
because `6553600·(10⁴·21³ + 16·21²)·2/log 2 = 1213950276403200/log 2 < 1.76·10¹⁵` by
`Real.log_two_gt_d9`.

This witnesses that the hypotheses are *satisfiable*, not that a two-phase schedule at these
variances is one any algorithm would run. -/
theorem cold_phase_regime_witness :
    ∃ (m0 : ℕ) (K : Set (EuclideanSpace ℝ (Fin 21))) (R sigmax M eps L : ℝ)
      (sig : ℕ → ℝ) (mu : ℕ → Measure (EuclideanSpace ℝ (Fin 21))) (t tc : ℕ),
      MeasurableSet K ∧ Convex ℝ K ∧ volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
      0 ≤ R ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧
      (∀ j, IsProbabilityMeasure (mu j)) ∧
      m0 = 2 ∧ 1 ≤ L ∧ M = 1 ∧ eps = 1 / 2 ∧ sigmax = 100 ∧
      (∀ j, 0 < sig j) ∧
      (∀ j < m0, R ≤ 2 * sig j * Real.sqrt ((21 : ℕ) : ℝ)) ∧
      (∀ j < m0, sig j ≤ sigmax) ∧
      1 ≤ M ∧ 0 < eps ∧ eps < 1 ∧ eps ≤ 1 ∧
      -- phase `0` is genuinely cold: `σ₀² = 1/n` and `σ₀·√n = 1 < 4`
      sig 0 ^ 2 = 1 / ((21 : ℕ) : ℝ) ∧
      sig 0 * Real.sqrt ((21 : ℕ) : ℝ) = 1 ∧
      sig 0 * Real.sqrt ((21 : ℕ) : ℝ) < 4 ∧
      -- phase `1` is warm
      4 ≤ sig 1 * Real.sqrt ((21 : ℕ) : ℝ) ∧
      (∀ j < m0, IsWarm (ENNReal.ofReal M) (mu j)
        (ellGaussianProb K
          (min (sig j / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ))))
          (sig j ^ 2))) ∧
      (m0 : ℝ) ≤ 32 * (((21 : ℕ) : ℝ) + 1) * L ^ 2
        / GaussianCooling.varBudget (eps / 2) + 1 ∧
      t = ⌈6553600 * (sigmax ^ 2 * (((21 : ℕ) : ℝ)) ^ 3 + 16 * (((21 : ℕ) : ℝ)) ^ 2)
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ ∧
      tc = ⌈104857600 * (((21 : ℕ) : ℝ)) ^ 2
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ ∧
      -- every phase mixes within the uniform budget `t`
      (∀ j < m0, MixesWithin
        (lazy (speedyMetropolisGaussian K
          (min (sig j / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ))))
          (sig j ^ 2)))
        (ellGaussianProb K
          (min (sig j / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ))))
          (sig j ^ 2)) (mu j) t (ENNReal.ofReal eps)) ∧
      -- the cold phase mixes within the sharper, `σ`-free budget `tc`, and `tc ≤ t`
      MixesWithin
        (lazy (speedyMetropolisGaussian K
          (min (sig 0 / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ))))
          (sig 0 ^ 2)))
        (ellGaussianProb K
          (min (sig 0 / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ))))
          (sig 0 ^ 2)) (mu 0) tc (ENNReal.ofReal eps) ∧
      tc ≤ t ∧
      ((m0 * t : ℕ) : ℝ) ≤ 2 * 10 ^ 10 * (((21 : ℕ) : ℝ) + 1)
        * (sigmax ^ 2 * (((21 : ℕ) : ℝ)) ^ 3 + 16 * (((21 : ℕ) : ℝ)) ^ 2) * L ^ 2
        * (1 + (Real.log M + 2 * Real.log (1 / eps))) / eps ^ 2 ∧
      ((m0 * t : ℕ) : ℝ) ≤ 4 * 10 ^ 15 := by
  classical
  have hcast : ((21 : ℕ) : ℝ) = (21 : ℝ) := by norm_num
  have h21 : (0 : ℝ) < ((21 : ℕ) : ℝ) := by rw [hcast]; norm_num
  have hsqrt21 : Real.sqrt ((21 : ℕ) : ℝ) ^ 2 = ((21 : ℕ) : ℝ) := Real.sq_sqrt h21.le
  have hspos : (0 : ℝ) < Real.sqrt ((21 : ℕ) : ℝ) := Real.sqrt_pos.2 h21
  have hsne : Real.sqrt ((21 : ℕ) : ℝ) ≠ 0 := ne_of_gt hspos
  have h4 : (4 : ℝ) ≤ Real.sqrt ((21 : ℕ) : ℝ) := by
    nlinarith [hsqrt21, hspos, hcast]
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : (0 : ℝ) < Real.log 2 ^ 2 := by positivity
  have hlog9 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- the body
  set K : Set (EuclideanSpace ℝ (Fin 21)) := Metric.ball 0 1 with hKdef
  have hKm : MeasurableSet K := measurableSet_ball
  have hKc : Convex ℝ K := convex_ball _ _
  have hKb : Bornology.IsBounded K := Metric.isBounded_ball
  have hK0 : volume K ≠ 0 := volume_unitBall_ne_zero
  have hKtop : volume K ≠ ⊤ := volume_unitBall_ne_top
  have hKR : ∀ x ∈ K, ‖x‖ ≤ (1 : ℝ) := by
    intro x hx
    rw [hKdef, Metric.mem_ball, dist_zero_right] at hx
    exact hx.le
  -- the two variances
  set sig : ℕ → ℝ := fun j => if j = 0 then 1 / Real.sqrt ((21 : ℕ) : ℝ) else 100 with hsigdef
  have hsigpos : ∀ j, 0 < sig j := by
    intro j
    rw [hsigdef]
    dsimp only
    split
    · positivity
    · norm_num
  have hsig0v : sig 0 = 1 / Real.sqrt ((21 : ℕ) : ℝ) := by simp [hsigdef]
  have hsig1v : sig 1 = 100 := by rw [hsigdef]; norm_num
  have hsig0sq : sig 0 ^ 2 = 1 / ((21 : ℕ) : ℝ) := by
    rw [hsig0v, div_pow, hsqrt21, one_pow]
  have hsig0mul : sig 0 * Real.sqrt ((21 : ℕ) : ℝ) = 1 := by
    rw [hsig0v, div_mul_cancel₀ _ hsne]
  have hsig1mul : (4 : ℝ) ≤ sig 1 * Real.sqrt ((21 : ℕ) : ℝ) := by
    rw [hsig1v]; nlinarith
  have hsigmax : ∀ j < 2, sig j ≤ (100 : ℝ) := by
    intro j hj
    interval_cases j
    · rw [hsig0v]
      rw [div_le_iff₀ hspos]
      nlinarith
    · rw [hsig1v]
  have hRsig : ∀ j < 2, (1 : ℝ) ≤ 2 * sig j * Real.sqrt ((21 : ℕ) : ℝ) := by
    intro j hj
    interval_cases j
    · nlinarith [hsig0mul]
    · nlinarith [hsig1mul]
  -- each phase's stationary law is a probability measure, and warm for itself
  have hprob : ∀ j, IsProbabilityMeasure (ellGaussianProb K
      (min (sig j / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ))))
      (sig j ^ 2)) := by
    intro j
    have hd : (0 : ℝ) < min (sig j / (8 * Real.sqrt ((21 : ℕ) : ℝ)))
        (1 / (2 * ((21 : ℕ) : ℝ))) := coldStep_pos (by norm_num) (hsigpos j)
    have hs : (0 : ℝ) < sig j ^ 2 := by positivity
    exact isProbabilityMeasure_ellGaussianProb
      (ellGaussianMeasure_univ_ne_zero hKm hKc hKb hK0 hd (sig j ^ 2))
      (ne_top_of_le_ne_top hKtop (ellGaussianMeasure_univ_le hs K _))
  set mu : ℕ → Measure (EuclideanSpace ℝ (Fin 21)) := fun j => ellGaussianProb K
    (min (sig j / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ))))
    (sig j ^ 2) with hmudef
  have hwarm : ∀ j < 2, IsWarm (ENNReal.ofReal (1 : ℝ)) (mu j)
      (ellGaussianProb K
        (min (sig j / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ))))
        (sig j ^ 2)) := by
    intro j _ S _
    exact le_of_eq (by rw [ENNReal.ofReal_one, one_mul])
  -- the variance budget at `ε = 1/2`
  have hκ0 : 0 < GaussianCooling.varBudget ((1 / 2 : ℝ) / 2) :=
    GaussianCooling.varBudget_pos (by norm_num)
  have hκ1 : GaussianCooling.varBudget ((1 / 2 : ℝ) / 2) ≤ 1 :=
    (sq_div_forty_le_varBudget_le_one (by norm_num) (by norm_num)).2
  have hm : ((2 : ℕ) : ℝ) ≤ 32 * (((21 : ℕ) : ℝ) + 1) * (84 : ℝ) ^ 2
      / GaussianCooling.varBudget ((1 / 2 : ℝ) / 2) + 1 := by
    have heq : 32 * (((21 : ℕ) : ℝ) + 1) * (84 : ℝ) ^ 2 = 4967424 := by
      rw [hcast]; norm_num
    have hinv : (1 : ℝ) ≤ 4967424 / GaussianCooling.varBudget ((1 / 2 : ℝ) / 2) := by
      rw [le_div_iff₀ hκ0]; linarith
    rw [heq]
    push_cast
    linarith
  -- the uniform deadline, evaluated
  have hone : (1 : ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
  have hDval : 6553600 * ((100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ)) ^ 3 + 16 * (((21 : ℕ) : ℝ)) ^ 2)
        * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2 + 1
      = 1213950276403200 / Real.log 2 + 1 := by
    rw [Real.log_one, hone, hcast]
    field_simp
    ring
  have hDle : 6553600 * ((100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ)) ^ 3 + 16 * (((21 : ℕ) : ℝ)) ^ 2)
        * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2 + 1
      ≤ ((2000000000000000 : ℕ) : ℝ) := by
    rw [hDval]
    have : (1213950276403200 : ℝ) / Real.log 2 ≤ 1999999999999999 := by
      rw [div_le_iff₀ hlogpos]
      nlinarith [hlog9]
    push_cast
    linarith
  set t : ℕ := ⌈6553600 * ((100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ)) ^ 3 + 16 * (((21 : ℕ) : ℝ)) ^ 2)
      * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2 + 1⌉₊ with htdef
  have htle : (t : ℝ) ≤ 2000000000000000 := by
    have := Nat.ceil_le.2 hDle
    rw [htdef]
    exact_mod_cast this
  set tc : ℕ := ⌈104857600 * (((21 : ℕ) : ℝ)) ^ 2
      * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2 + 1⌉₊ with htcdef
  -- the cold budget is the smaller one
  have hX0 : (0 : ℝ) ≤ Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ)) := by
    rw [Real.log_one, hone]
    have : (0 : ℝ) ≤ Real.log 2 := hlogpos.le
    linarith
  have htct : tc ≤ t := by
    rw [htcdef, htdef]
    refine Nat.ceil_le_ceil ?_
    have hcmp : (104857600 : ℝ) * (((21 : ℕ) : ℝ)) ^ 2
        ≤ 6553600 * ((100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ)) ^ 3 + 16 * (((21 : ℕ) : ℝ)) ^ 2) := by
      rw [hcast]; norm_num
    have hmul : 104857600 * (((21 : ℕ) : ℝ)) ^ 2
          * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ)))
        ≤ 6553600 * ((100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ)) ^ 3 + 16 * (((21 : ℕ) : ℝ)) ^ 2)
          * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_right hcmp hX0
    have hdiv : 104857600 * (((21 : ℕ) : ℝ)) ^ 2
          * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2
        ≤ 6553600 * ((100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ)) ^ 3 + 16 * (((21 : ℕ) : ℝ)) ^ 2)
          * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2 := by
      rw [div_le_div_iff₀ hlog2 hlog2]
      nlinarith [mul_le_mul_of_nonneg_right hmul hlog2.le]
    linarith
  have htcle : 104857600 * (((21 : ℕ) : ℝ)) ^ 2
      * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2 + 1 ≤ (tc : ℝ) := by
    rw [htcdef]
    exact Nat.le_ceil _
  -- the three conclusions
  have hmix := mixesWithin_all_phases_coldStep (n := 21) (m := 2) (sig := sig) (mu := mu)
    (sigmax := 100) (M := 1) (eps := 1 / 2) (R := 1)
    le_rfl hKm hKc hK0 (by norm_num) hKR hprob
    (fun j _ => hsigpos j) hRsig le_rfl (by norm_num) (by norm_num) hwarm hsigmax
  have hcoldmix := mixesWithin_lazy_speedyMetropolisGaussian_cold (n := 21) (σ := sig 0)
    (R := 1) (M := 1) (eps := 1 / 2) (mu0 := mu 0) (t := tc) le_rfl (hsigpos 0)
    (by rw [hsig0mul]; norm_num) hKm hKc hK0 (by norm_num) hKR (hRsig 0 (by norm_num))
    le_rfl (hwarm 0 (by norm_num)) (by norm_num) (by norm_num) htcle
  have hpoly := total_speedy_steps_coldStep_poly_varBudget (n := 21) (m := 2)
    (sigmax := 100) (M := 1) (eps := 1 / 2) (L := 84)
    le_rfl (by norm_num) le_rfl (by norm_num) (by norm_num) hm
  have hnum : ((2 * t : ℕ) : ℝ) ≤ 4 * 10 ^ 15 := by
    push_cast
    nlinarith [htle, Nat.cast_nonneg (α := ℝ) t]
  refine ⟨2, K, 1, 100, 1, 1 / 2, 84, sig, mu, t, tc,
    hKm, hKc, hK0, hKtop, by norm_num, hKR, hprob,
    rfl, by norm_num, rfl, rfl, rfl,
    hsigpos, hRsig, hsigmax, le_rfl, by norm_num, by norm_num, by norm_num,
    hsig0sq, hsig0mul, by rw [hsig0mul]; norm_num, hsig1mul, hwarm, hm,
    htdef, htcdef, hmix, hcoldmix, htct, hpoly, hnum⟩

/-! ### Axiom audit (`CLAUDE.md` §4)

Every theorem of this file, re-checked at elaboration time.  Each must print exactly
`[propext, Classical.choice, Quot.sound]`; anything else — in particular `sorryAx` — means the
file is not finished. -/

section AxiomCheck

#print axioms coldStep_pos
#print axioms coldStep_le_conductance
#print axioms coldStep_le_kls
#print axioms coldStep_valid
#print axioms coldStep_eq_cold
#print axioms coldStep_eq_warm
#print axioms ell_eq_one_on_shrunken_coldStep
#print axioms half_le_speedy_shrunken_coldStep
#print axioms div_min_sq_le
#print axioms coldStep_deadline_le
#print axioms mixesWithin_lazy_speedyMetropolisGaussian_coldStep
#print axioms mixesWithin_lazy_speedyMetropolisGaussian_cold
#print axioms mixesWithin_lazy_speedyMetropolisGaussian_warm
#print axioms coldCount_le_warmCount
#print axioms mixesWithin_all_phases_coldStep
#print axioms nat_mul_ceil_le
#print axioms total_speedy_steps_coldStep_le
#print axioms total_speedy_steps_coldStep_poly
#print axioms total_speedy_steps_coldStep_poly_varBudget
#print axioms cold_phase_regime_witness

end AxiomCheck

end Arlib.MarkovChains
