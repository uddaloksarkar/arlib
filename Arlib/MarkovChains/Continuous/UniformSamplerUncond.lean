/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.SpeedyUniformPoly
import Arlib.MarkovChains.Continuous.WarmEllProb
import Arlib.Convexity.LogConcaveIso

/-!
# Unconditional polynomial-time uniform sampling on a convex body

`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn`
(`SpeedyToUniform.lean:226`) turns three inputs — an isoperimetric inequality `hiso` for
`ellProb K δ`, a warm start `hwarm`, and a smoothness certificate `hsmooth` — into a
polynomial-step mixing bound for the lazy speedy walk *to the uniform measure on `K`*.
`SpeedyUniformPoly.lean` discharged `hsmooth`.  **All three are now theorems**, so this file
removes every one of the three binders and states the composition with no hypothesis left
except the geometry of `K`, the accuracy `ρ`, and the step count:

* `hsmooth` ← `Arlib.MarkovChains.isSmooth_of_ball_subset` (`EllFloor.lean`), already consumed
  inside `mixesWithin_lazy_speedyWalk_uniformOn_poly`;
* `hwarm` ← `Arlib.MarkovChains.isWarm_uniformOn_unitBall_ellProb` (`WarmEllProb.lean`), at
  the **samplable** start `mu0 = Arlib.uniformOn volume (Metric.ball 0 1)`;
* `hiso` ← `Arlib.hiso_ellProb_of_ball_bound` (`Arlib/Convexity/LogConcaveIso.lean`), at the
  dimension-free coefficient `κ = 1/(8R)` for `K ⊆ B(0,R)`.

## Main results

* `Arlib.MarkovChains.half_le_diam_bound_of_ball_subset` — `1/2 ≤ D` for any diameter bound
  `D` of a body containing the unit ball, so `κ = 1/(8D)` is well defined.
* `Arlib.MarkovChains.volume_le_one_add_pow_mul_volume_unitBall` — `vol K ≤ (1+D)ⁿ·vol B(0,1)`,
  the volume calibration that turns the warm-start constant into a closed form in `n` and `D`.
* `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_unitBallStart` — the composition
  with `hwarm` and `hsmooth` discharged and **`κ` still symbolic**: this is the statement a
  better isoperimetric coefficient slots into without any restructuring.
* `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond` — **the honest final
  theorem**: no isoperimetry, warmness or smoothness binder at all.
* `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps` — the same with
  `conductanceMixingTime` unfolded into closed-form arithmetic in `n`, `D`, `ρ`.
* `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond_ballTwo` — the non-vacuity
  witness: a concrete body, a concrete `ρ`, a concrete `t`, **every** hypothesis discharged.

## The step count, stated honestly

With `δ = ρ/(4n)` and `κ = 1/(8D)` the conductance certified by
`Arlib.MarkovChains.conductance_speedyWalk_ge` (through
`mixesWithin_lazy_speedyWalk_uniformOn_poly`) is

    φ = min(1/32, κ·δ/(256n)) = min(1/32, ρ/(8192·D·n²)),

and the warm-start constant proved below is

    M = (1+D)^(2n),        log M = 2n·log(1+D).

`conductanceMixingTime_le` (`MixingFromConductance.lean:179`) then gives

    t ≤ (log M + 2·log(2/ρ))/φ² + 1
      = (2n·log(1+D) + 2·log(2/ρ)) / min(1/32, ρ/(8192 D n²))²  + 1
      = O( n⁵ · D² · log(1+D) / ρ² ).

Polynomial in `n`, `D`, `1/ρ`, and **unconditional**.  That is the whole point of the file;
the exponent is not the point, and it is not sharp.

### Where the `n⁵D²` is lost — three factors of `n` versus the book

Lee's optimization/sampling book obtains `O(n²D²)` for the same task.  Three factors of `n`
are lost, and **none of them is created by the composition performed here**; each sits in an
upstream lemma and each would be fixed there, with no change to the statements below:

1. **Smoothness.**  `isSmooth_of_ball_subset` degrades as `1-(1-δ)ⁿ = Θ(δn)`; the book's
   `lem:avg-local-conductance` (the convex good-points body `K_δ = {ℓ ≥ 3/4}`) degrades as
   `δ√n`.  So `δ = Θ(ρ/n)` here where the book takes `δ = Θ(1/√n)`.  *Fixed in the smoothness
   lemma feeding `SpeedyUniformPoly.smoothBias_le`.*
2. **Conductance.**  `conductance_speedyWalk_ge` is linear in `δ` at the one-step overlap
   scale `δ/(2n)`; the book works at overlap scale `δ/√n`.  *Fixed in the overlap/conductance
   lemma for `speedyWalk`.*
3. **Warm start.**  `log M = 2n·log(1+D) = Θ(n log D)` from a single inscribed ball; the book
   gets an `O(1)`-warm start from an `n log D`-phase ball-growing construction
   (`ball_walk.tex:817-845`).  *Fixed by formalising that phased construction*, which is a
   multi-phase algorithm rather than a lemma — see `WarmEllProb.lean`'s module docstring,
   which also records why the exponential constant is **necessary** for this single-ball
   `mu0`.

`mixesWithin_lazy_speedyWalk_uniformOn_unitBallStart` keeps `κ` symbolic precisely so that a
sharper isoperimetric coefficient (or a sharper conductance) can be substituted without
touching anything else.

## Scope — read before quoting anything from this file

Every theorem here is a **Markov-chain mixing statement**: after `t` applications of the
kernel `lazy (speedyWalk K δ)`, the law of the walk is within total variation `ρ` of
`Arlib.uniformOn volume K`.  It is **not**:

* a running-time claim about any algorithm.  `t` counts abstract kernel applications; nothing
  here bounds the cost of **one** step (which needs a membership oracle for `K` and a sample
  from a ball), nor the bit complexity, nor the number of oracle calls;
* a statement about the TTC pipeline, volume computation, or lattice counting; in particular
  nothing of the form `O(m·n⁴)` is claimed or implied;
* a claim at `n = 1`.  `Arlib.hiso_ellProb_of_ball_bound` requires `2 ≤ n`, so every
  unconditional statement below carries `hn : 2 ≤ n`.  The consumer would accept `1 ≤ n`; the
  scope is deliberately **not** widened.

**No `def`, `structure`, `class`, `axiom` or named `Prop` is introduced in this file.**  Every
declaration is a `theorem`, and every hypothesis is an inline binder.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {n : ℕ}

/-! ## 1. Two geometric facts about a body containing the unit ball

`Arlib.hiso_ellProb_of_ball_bound` needs a **positive** circumradius `R` and
`isWarm_uniformOn_unitBall_ellProb` needs a volume calibration.  Both come from the pair
`B(0,1) ⊆ K`, `diam K ≤ D` with no further input. -/

/-- **A diameter bound for a body containing the unit ball is at least `1/2`.**

`B(0,1) ⊆ K` puts both `0` and the point `(1/2)·e₀` in `K`, at distance `1/2`.  This is what
makes `κ = 1/(8·D)` a positive number, i.e. what lets `Arlib.hiso_ellProb_of_ball_bound` be
applied at `R := D`.

The sharp constant is `2` (take `±(1-ε)e₀`); `1/2` is all that is used, and is cheaper. -/
theorem half_le_diam_bound_of_ball_subset (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    (1 : ℝ) / 2 ≤ D := by
  set y : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 / 2 : ℝ)
    with hy
  have hyn : ‖y‖ = 1 / 2 := by rw [hy, PiLp.norm_single]; norm_num
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (Metric.mem_ball_self one_pos)
  have hyK : y ∈ K := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right, hyn]
    norm_num
  have h := hD 0 h0K y hyK
  rwa [dist_zero_left, hyn] at h

/-- **A body of circumradius `D` has volume at most `(1+D)ⁿ·vol B(0,1)`.**

`K ⊆ B(0, 1+D)` (strictly, since `‖x‖ ≤ D < 1+D`), and the Lebesgue measure of a ball scales
by the `n`-th power of its radius (`MeasureTheory.Measure.addHaar_ball_of_pos` together with
`finrank_euclideanSpace_fin`).

This is the calibration hypothesis `hvol` of
`Arlib.MarkovChains.isWarm_uniformOn_unitBall_ellProb` at `c = (1+D)ⁿ`, and it is what turns
the warm-start constant into the closed form `M = (1+D)^(2n)` — with no `vol K` left in the
statement of the sampler. -/
theorem volume_le_one_add_pow_mul_volume_unitBall {K : Set (EuclideanSpace ℝ (Fin n))}
    {D : ℝ} (hD0 : 0 ≤ D) (hKR : ∀ x ∈ K, ‖x‖ ≤ D) :
    volume K ≤ ENNReal.ofReal ((1 + D) ^ n)
      * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have hR0 : (0 : ℝ) < 1 + D := by linarith
  have hsub : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 + D) := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    have := hKR x hx
    linarith
  calc volume K ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 + D)) :=
        measure_mono hsub
    _ = ENNReal.ofReal ((1 + D) ^ n)
          * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
        rw [Measure.addHaar_ball_of_pos volume 0 hR0, finrank_euclideanSpace_fin]

/-! ## 2. The composition with the warm start discharged, `κ` still symbolic

This is the theorem a sharper isoperimetric coefficient slots into.  Only `hiso` remains a
binder; `hwarm`, `hM` and `hsmooth` are gone, and the starting law is fixed to the one law on
this list that an algorithm can actually draw from. -/

/-- **The lazy speedy walk mixes to the uniform measure on `K` from a samplable start**, with
the warm-start and smoothness hypotheses of `mixesWithin_lazy_speedyWalk_uniformOn`
discharged and only the isoperimetric coefficient `κ` left symbolic.

For measurable convex `K` with `B(0,1) ⊆ K` and all pairwise distances at most `D`, and for
`0 < ρ ≤ 1`, put `δ = ρ/(4n)`.  Then from

    mu0 = Arlib.uniformOn volume (Metric.ball 0 1)

— a law one can sample directly — after

    t ≥ conductanceMixingTime ((1+D)^(2n)) (min (1/32) (κ·(ρ/(4n))/(256n))) (ρ/2)

steps the law of the walk is within total variation `ρ` of `Arlib.uniformOn volume K`.

**The warm-start constant is `M = (1+D)^(2n)`**: `isWarm_uniformOn_unitBall_ellProb` gives
`(1+D)ⁿ·c` for any calibration `vol K ≤ c·vol B(0,1)`, and
`volume_le_one_add_pow_mul_volume_unitBall` supplies `c = (1+D)ⁿ` unconditionally.  Only
`log M = 2n·log(1+D)` enters the step count, so this exponential constant costs a factor `n`
and nothing more; `WarmEllProb.lean`'s module docstring shows it is *necessary* for this
`mu0`.

`hiso` is the only remaining binder, and it is a theorem —
`Arlib.hiso_ellProb_of_ball_bound` at `κ = 1/(8D)`; see
`mixesWithin_lazy_speedyWalk_uniformOn_uncond`, which is this statement with that plugged in.
It is kept symbolic here so that a sharper `κ` improves the exponent mechanically. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_unitBallStart (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d
          * ellProb K (rho / (4 * (n : ℝ))) A * ellProb K (rho / (4 * (n : ℝ))) B
        ≤ ellProb K (rho / (4 * (n : ℝ))) ((K \ A) \ B))
    {t : ℕ}
    (ht : conductanceMixingTime ((1 + D) ^ (2 * n))
        (min (1 / 32) (kappa * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) (rho / 2) ≤ t) :
    MixesWithin (lazy (speedyWalk K (rho / (4 * (n : ℝ)))))
      (Arlib.uniformOn volume K)
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      t (ENNReal.ofReal rho) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (Metric.mem_ball_self one_pos)
  have hD0 : (0 : ℝ) ≤ D := by simpa using hD 0 h0K 0 h0K
  have hKR : ∀ x ∈ K, ‖x‖ ≤ D := by
    intro x hx
    simpa using hD x hx 0 h0K
  -- `K` is bounded, being inside a closed ball of radius `D`.
  have hsubcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) D := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hKR x hx
  have hbdd : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hsubcb
  -- the step size and its two side conditions
  have hδ : 0 < rho / (4 * (n : ℝ)) := by positivity
  have hδ1 : rho / (4 * (n : ℝ)) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  -- the warm-start constant in closed form
  have hMeq : (1 + D) ^ n * (1 + D) ^ n = (1 + D) ^ (2 * n) := by
    rw [two_mul, pow_add]
  have hcpow : (1 : ℝ) ≤ (1 + D) ^ n := one_le_pow₀ (by linarith)
  have hM : (1 : ℝ) ≤ (1 + D) ^ (2 * n) := by
    rw [← hMeq]; exact one_le_warmConst hD0 hcpow n
  have hwarm : IsWarm (ENNReal.ofReal ((1 + D) ^ (2 * n)))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (ellProb K (rho / (4 * (n : ℝ)))) := by
    rw [← hMeq]
    exact isWarm_uniformOn_unitBall_ellProb hconv hball hD hcpow
      (volume_le_one_add_pow_mul_volume_unitBall hD0 hKR) hδ hδ1
  haveI : IsProbabilityMeasure
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    Arlib.isProbabilityMeasure_uniformOn volume volume_unitBall_ne_zero volume_unitBall_ne_top
  exact mixesWithin_lazy_speedyWalk_uniformOn_poly hn hK hconv hball hbdd hrho hrho1 hkappa
    hiso hM hwarm ht

/-! ## 3. The honest final theorem: no isoperimetry, no warmness, no smoothness

`Arlib.hiso_ellProb_of_ball_bound` at `R := D` discharges the last binder. -/

/-- **Unconditional polynomial-time uniform sampling on a convex body.**

Let `2 ≤ n`, let `K ⊆ ℝⁿ` be measurable and convex with `B(0,1) ⊆ K` and all pairwise
distances at most `D`, and let `0 < ρ ≤ 1`.  Then, starting from the **samplable** law
`Arlib.uniformOn volume (Metric.ball 0 1)`, after

    t ≥ conductanceMixingTime ((1+D)^(2n))
          (min (1/32) ((1/(8·D))·(ρ/(4n))/(256n))) (ρ/2)

steps the law of the lazy speedy walk with step size `δ = ρ/(4n)` is within total variation
`ρ` of `Arlib.uniformOn volume K`.

Unfolding the two constants (`conductanceMixingTime_le`, `MixingFromConductance.lean:179`):

    φ = min(1/32, ρ/(8192·D·n²)),        log M = 2n·log(1+D),
    t = O( n⁵ · D² · log(1+D) / ρ² ).

`mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps` states that closed form.

**Every binder here is geometry of `K` or a numeric side condition.**  There is no
isoperimetry binder (`hiso` ← `Arlib.hiso_ellProb_of_ball_bound`, dimension-free at
`κ = 1/(8D)`), no warmness binder (`hwarm` ← `isWarm_uniformOn_unitBall_ellProb`, at
`M = (1+D)^(2n)`), and no smoothness binder (`hsmooth` ← `isSmooth_of_ball_subset`, consumed
inside `mixesWithin_lazy_speedyWalk_uniformOn_poly`).

**`2 ≤ n` is a real scope limit, not an artefact of the composition**: it is the hypothesis of
`Arlib.hiso_ellProb_of_ball_bound`.  The consumer would accept `1 ≤ n`; it is not widened.

**Scope.**  A mixing statement about a Markov kernel — not a running-time claim, and not a
bound on the cost of one step.  See the module docstring. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_uncond (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) {t : ℕ}
    (ht : conductanceMixingTime ((1 + D) ^ (2 * n))
        (min (1 / 32) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) (rho / 2) ≤ t) :
    MixesWithin (lazy (speedyWalk K (rho / (4 * (n : ℝ)))))
      (Arlib.uniformOn volume K)
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      t (ENNReal.ofReal rho) := by
  have hn1 : 1 ≤ n := by omega
  have hD2 : (1 : ℝ) / 2 ≤ D := half_le_diam_bound_of_ball_subset hn1 hball hD
  have hD0 : (0 : ℝ) < D := by linarith
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (Metric.mem_ball_self one_pos)
  have hKR : ∀ x ∈ K, ‖x‖ ≤ D := by
    intro x hx
    simpa using hD x hx 0 h0K
  have hK0 : volume K ≠ 0 := fun h => volume_unitBall_ne_zero (measure_mono_null hball h)
  have hδ : 0 < rho / (4 * (n : ℝ)) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    positivity
  exact mixesWithin_lazy_speedyWalk_uniformOn_unitBallStart hn1 hK hconv hball hD hrho hrho1
    (by positivity)
    (Arlib.hiso_ellProb_of_ball_bound hn hD0 hδ hK hconv hKR hK0) ht

/-! ## 4. The step count in closed form

`conductanceMixingTime_le` turns the `conductanceMixingTime` of §3 into arithmetic in
`n`, `D`, `ρ` alone. -/

/-- **The unconditional sampler with the step count written out.**

Same statement as `mixesWithin_lazy_speedyWalk_uniformOn_uncond`, with `conductanceMixingTime`
replaced by the explicit sufficient count

    t ≥ (2n·log(1+D) + 2·log(2/ρ)) / min(1/32, (1/(8D))·(ρ/(4n))/(256n))² + 1.

Since `min(1/32, (1/(8D))·(ρ/(4n))/(256n)) = min(1/32, ρ/(8192·D·n²))`, the count is

    O( n⁵ · D² · log(1+D) / ρ² ),

polynomial in `n`, `D` and `1/ρ`, and unconditional.  The `log M = 2n·log(1+D)` term is the
single-ball warm start (loss source 3 of the module docstring); the `n⁵D²` is `φ⁻²` with the
two upstream `√n` losses (sources 1 and 2) already paid.

The identity `log M = 2n·log(1+D)` is exact here (`Real.log_pow`), not an estimate: `M` really
is `(1+D)^(2n)`. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) {t : ℕ}
    (ht : (2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho))
          / (min (1 / 32) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2 + 1
        ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyWalk K (rho / (4 * (n : ℝ)))))
      (Arlib.uniformOn volume K)
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      t (ENNReal.ofReal rho) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hD2 : (1 : ℝ) / 2 ≤ D := half_le_diam_bound_of_ball_subset hn1 hball hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hMpos : (0 : ℝ) < 1 + D := by linarith
  have hM : (1 : ℝ) ≤ (1 + D) ^ (2 * n) := one_le_pow₀ (by linarith)
  have hphi0 : 0 < min (1 / 32)
      (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))) := by
    refine lt_min (by norm_num) ?_
    positivity
  have heps : (0 : ℝ) < rho / 2 := by linarith
  have hsqrt : rho / 2 ≤ Real.sqrt ((1 + D) ^ (2 * n)) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt ((1 + D) ^ (2 * n)) := by
      have h2 := Real.sqrt_le_sqrt hM
      rwa [Real.sqrt_one] at h2
    linarith
  have hlogM : Real.log ((1 + D) ^ (2 * n)) = 2 * (n : ℝ) * Real.log (1 + D) := by
    rw [Real.log_pow]
    push_cast
    ring
  have hlogeps : Real.log (1 / (rho / 2)) = Real.log (2 / rho) := by
    rw [one_div_div]
  refine mixesWithin_lazy_speedyWalk_uniformOn_uncond hn hK hconv hball hD hrho hrho1 ?_
  have hle := conductanceMixingTime_le (M := (1 + D) ^ (2 * n))
    (phi := min (1 / 32) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))))
    (eps := rho / 2) hM hphi0 heps hsqrt
  rw [hlogM, hlogeps] at hle
  exact_mod_cast hle.trans ht

/-! ## 5. Non-vacuity (`CLAUDE.md` §11) — and this one is genuinely unconditional

Every theorem above is an implication.  The witness below discharges **every** hypothesis of
`mixesWithin_lazy_speedyWalk_uniformOn_uncond` on a concrete body, at a concrete `ρ`, with a
concrete `t`, leaving `hn : 2 ≤ n` — the scope limit of `Arlib.hiso_ellProb_of_ball_bound` —
as the only surviving assumption.  In particular there is no residual `hiso`, `hwarm` or
`hsmooth`, which is exactly what the earlier witnesses
(`SpeedyUniformPoly.mixesWithin_lazy_speedyWalk_uniformOn_poly_unitBall`,
`SpeedyWalk.mixesWithin_lazy_speedyWalk_unitBall`) could not do.

The body is `B(0,2)`, not `B(0,1)`: with `K = B(0,1)` the starting law would *equal* the
target and the witness would look degenerate.  Here `mu0 = uniformOn B(0,1)` is genuinely
different from the target `uniformOn B(0,2)`, and `ρ = 1/2` is a non-trivial tolerance
(`ofReal 1` would be the vacuous total-variation bound). -/

/-- **The diameter of `B(0,2)` is at most `4`.**  The `hD` hypothesis of the witness; the same
triangle-inequality argument as `dist_le_two_of_mem_unitBall` (`WarmEllProb.lean`). -/
theorem dist_le_four_of_mem_ballTwo
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2) :
    dist x y ≤ 4 := by
  rw [Metric.mem_ball] at hx hy
  have h := dist_triangle x 0 y
  rw [dist_comm (0 : EuclideanSpace ℝ (Fin n)) y] at h
  linarith

/-- **The non-vacuity witness — fully unconditional.**

`K = B(0,2)`, `ρ = 1/2`, `t` the concrete step count.  Every hypothesis of
`mixesWithin_lazy_speedyWalk_uniformOn_uncond` is discharged:

| binder | discharged by |
| --- | --- |
| `hK : MeasurableSet K` | `measurableSet_ball` |
| `hconv : Convex ℝ K` | `convex_ball` |
| `hball : B(0,1) ⊆ K` | `Metric.ball_subset_ball` |
| `hD : diam K ≤ 4` | `dist_le_four_of_mem_ballTwo` |
| `hrho, hrho1` | `norm_num` at `ρ = 1/2` |
| `ht` | `le_rfl` — `t` *is* the step count |
| `hiso` | `Arlib.hiso_ellProb_of_ball_bound` (inside `..._uncond`) |
| `hwarm` | `isWarm_uniformOn_unitBall_ellProb` (inside `..._unitBallStart`) |
| `hsmooth` | `isSmooth_of_ball_subset` (inside `..._poly`) |

**The only surviving hypothesis is `hn : 2 ≤ n`.**  So: the lazy speedy walk on `B(0,2)` with
step size `1/(8n)`, started from the uniform law on `B(0,1)`, is within total variation `1/2`
of the uniform law on `B(0,2)` after `conductanceMixingTime (5^(2n)) (min (1/32) (1/(65536·n²))) (1/4)`
steps — a theorem with no unproved input. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_uncond_ballTwo (hn : 2 ≤ n) :
    MixesWithin
      (lazy (speedyWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
        ((1 / 2 : ℝ) / (4 * (n : ℝ)))))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (conductanceMixingTime ((1 + 4 : ℝ) ^ (2 * n))
        (min (1 / 32)
          (1 / (8 * 4) * ((1 / 2 : ℝ) / (4 * (n : ℝ))) / (256 * (n : ℝ))))
        ((1 / 2 : ℝ) / 2))
      (ENNReal.ofReal (1 / 2)) :=
  mixesWithin_lazy_speedyWalk_uniformOn_uncond hn measurableSet_ball (convex_ball _ _)
    (Metric.ball_subset_ball (by norm_num)) dist_le_four_of_mem_ballTwo (by norm_num)
    (by norm_num) le_rfl

/-! ## Axiom check -/

#print axioms half_le_diam_bound_of_ball_subset
#print axioms volume_le_one_add_pow_mul_volume_unitBall
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_unitBallStart
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_uncond
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps
#print axioms dist_le_four_of_mem_ballTwo
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_uncond_ballTwo

end Arlib.MarkovChains
