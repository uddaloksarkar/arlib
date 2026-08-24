/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.SpeedyToUniform
import Arlib.MarkovChains.Continuous.ConvexBodyMixing

/-!
# A warm start for the speedy walk: `IsWarm M (uniformOn volume (ball 0 1)) (ellProb K δ)`

`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn`
(`Arlib/MarkovChains/Continuous/SpeedyToUniform.lean:226`) delivers a polynomial-step uniform
sampler on a convex body, but it consumes an input it does not produce:

    (hM : 1 ≤ M) (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellProb K δ))

and — as that theorem's docstring insists — warmness is relative to `Arlib.MarkovChains.ellProb K δ`,
the measure the speedy walk is actually reversible for, **not** to `Arlib.uniformOn volume K`.
This file produces that input, with an explicit `M`, from a hypothesis the repository already
uses everywhere else: an inscribed unit ball plus a diameter bound.

## The construction

Take `mu0 := Arlib.uniformOn volume (Metric.ball 0 1)` — *the* samplable starting law: one can
draw from it directly, unlike the `IsWarm.refl` witness of `SpeedyWalk.lean:1343`, which starts
the chain from its own stationary measure and is therefore useless as an algorithm.

Everything reduces to one setwise comparison.  Write `V = vol(K)`, `W = vol(B)`,
`b = vol(S ∩ B)`, `L = ∫_K ell`, and let `θ` be a pointwise floor for the local conductance,
`θ ≤ ell K δ x` for all `x ∈ K`.  Then for `B ⊆ K`

    ellProb K δ S = L⁻¹ · ∫_{S∩K} ell ≥ V⁻¹ · θ · b,        (`mul_volume_inter_le_ellMeasure`)
    mu0 S = b / W,

so `mu0 S ≤ M · ellProb K δ S` as soon as `V ≤ M · θ · W`.  That is `isWarm_uniformOn_ellProb`,
and the whole proof is the `ℝ≥0∞` identity `b·W⁻¹ = (b·V⁻¹)·(V·W⁻¹)` (`div_le_mul_of_le_mul`).

The floor `θ` is not assumed: `Arlib.MarkovChains.le_ell_of_convex_of_ball_subset`
(`ConvexBodyMixing.lean:93`) proves `ell K δ x ≥ (γ/(γ+D))ⁿ` on a convex `K` with
`B(c,γ) ⊆ K` and diameter `≤ D`, for `0 < δ ≤ γ`.  At `γ = 1`, `θ = (1/(1+D))ⁿ`.

## The explicit constant, and why exponential is fine

`isWarm_uniformOn_unitBall_ellProb` gives

    M = (1 + D)ⁿ · c,          where  vol(K) ≤ c · vol(B(0,1)),

and `isWarm_uniformOn_unitBall_ellProb_ratio` discharges `c` with no extra hypothesis by taking
`c = vol(K)/vol(B(0,1))`, so that

    **M = (1 + D)ⁿ · vol(K)/vol(B(0,1))**.

Both factors are exponential in `n`: the volume ratio because `K ⊇ B(0,1)` can be `Dⁿ` times
larger, and `(1+D)ⁿ` because the local-conductance floor of `le_ell_of_convex_of_ball_subset` is
exponentially small at a corner of `K`.  **This is expected and is not a defect.**  The step
count is `Arlib.MarkovChains.conductanceMixingTime M φ ε`, and
`Arlib.MarkovChains.conductanceMixingTime_le` (`MixingFromConductance.lean:179-182`) bounds it by

    (log M + 2·log(1/ε)) / φ² + 1,

so an `M` exponential in `n` costs a factor `n` in the step count, nothing more.  This is exactly
the accounting of the literature: `har_dikin.tex:78-82` bounds the warm-start constant of
hit-and-run by `(D/d)ⁿ` — "By taking one step from the initial point, we can bound `M` by
`(D/d)ⁿ` where `d` is the minimum distance of the starting point from the boundary" — and then
reports the resulting mixing time as `Õ(n³D²)`, i.e. one extra factor of `n` from `log M`.

## Which sense of "warm"?  The `L∞` one, matching the book

`Arlib.IsWarm M μ ν` is `∀ S measurable, μ S ≤ M · ν S`, i.e. `M = sup_S μ(S)/ν(S)`.  That is
*verbatim* the book's definition — `ball_walk.tex:150-151`: "Warmth: `P` is said to be `M`-warm
with respect to `Q` if `M = sup_{A∈𝒜} P(A)/Q(A)`" — the sup-density (`L∞`) sense, not the
`L₂`/`χ²` sense.  `Arlib.rnDeriv_le_of_isWarm` (`PointwiseMixing.lean:255`) confirms it: warmness
bounds `dμ/dν ≤ M` almost everywhere.  **Every theorem in this file is in that `L∞` sense**, and
the consumer `mixesWithin_lazy_speedyWalk_uniformOn` (via `L2Mixing.lean:944`) asks for that same
sense.  Nothing here converts an `L₂`/`χ²` bound into an `L∞` one; that conversion is false in
general and this file never attempts it.  (The book's `L₂`/`χ²` route is the separate
`cor:s-mixing` part 3, `ball_walk.tex:330-334`, `d_TV ≤ ε + √(M/ε)(1-φ²/2)ᵗ` with
`M = χ²(Q₀,Q)`, and the annealing chapter pairs it with hit-and-run, not the ball walk —
`annealing_volume.tex:129-132`.)

## Why not the book's `O(1)`-warm construction?

`ball_walk.tex:817-845` gives a genuinely `O(1)` (in fact `2`-) warm start: with `Bⁿ ⊆ K ⊆ DBⁿ`,
set `K_i = 2^{i/n}Bⁿ ∩ K` and ball-walk through `i = 1, …, n log D` phases; `K_{i+1} ⊆ 2^{1/n}K_i`
gives `vol(K_{i+1}) ≤ 2 vol(K_i)`, so `2`-warmness is maintained phase to phase.  That is a
*multi-phase algorithm*, not a lemma: formalising it needs a chain of `n log D` samplers, each
consuming the previous phase's output distribution, and is far outside one file.

More importantly, **it would not remove the exponential from this file's constant**, for two
independent reasons.

1. Its target is `uniformOn volume K_i`, the ball walk's stationary measure.  The speedy walk's
   stationary measure is `ellProb K δ`, and the only route from uniform-warmness to
   `ellProb`-warmness is `isWarm_ellProb_of_isWarm_uniformOn` below, which costs `θ⁻¹`.
2. That `θ⁻¹` is not an artefact of a lossy proof.  `sup_S uniformOn(S)/ellProb(S)` is
   `(L/vol K)·sup_{x∈K} 1/ell(x)`, and `ell` really is exponentially small in a thin corner of
   `K`: **uniform-on-`K` is not `O(1)`-warm with respect to `ellProb K δ` for a general convex
   body.**  Nor is a single inscribed ball: taking `S = B` in the definition already forces
   `M ≥ uniformOn volume B (B) / ellProb K δ B ≥ (1-s)·vol(K)/vol(B)` under `IsSmooth K δ s`, so
   the exponential in `isWarm_uniformOn_unitBall_ellProb` is **necessary for this `mu0`**, not an
   artefact.  Note that `IsSmooth K δ s` does not rescue it: it bounds the *average* of `ell`,
   whereas `L∞`-warmness is a supremum, and a volume-negligible corner where `ell` is tiny
   destroys the sup while leaving the average untouched.  This is precisely the `L∞`-versus-`L₂`
   gap the book navigates by pairing annealing with hit-and-run.

What is **not** claimed: that no `O(1)`-warm start for `ellProb K δ` exists at all.  Trivially one
does — `ellProb K δ` is `1`-warm for itself (`IsWarm.refl`, used at `SpeedyWalk.lean:1343`), which
is exactly why that witness is useless as an algorithm.  And a *phased* construction running
speedy walks on `K_i = 2^{i/n}Bⁿ ∩ K` and maintaining warmness with respect to `ellProb (K_i) δ`
directly — rather than transferring from uniform at cost `θ⁻¹` — is not ruled out by the argument
above; the per-phase volume-doubling bound plausibly survives.  That is **out of scope for this
file**, not impossible.  What is settled here is the single-ball start: its constant is
exponential, necessarily so, and in the same family as the book's `(D/d)ⁿ`.

## Does uniform-warmness transfer to `ellProb`-warmness?

Two separate questions, with two different answers.

* **From `Arlib.MarkovChains.tvLe_ellProb_uniformOn`: no.**  That theorem
  (`SpeedyToUniform.lean:186`) bounds `TVLe (ellProb K δ) (uniformOn volume K) (s/(1-s))`, and a
  total-variation bound is an *additive* statement about events while warmness is a
  *multiplicative* one.  No finite `M` follows: `Arlib/Probability/TV.lean:364` records exactly
  the mechanism — `TVLe μ ν ε` permits `ν S = 0 < μ S`, and on such an `S` the inequality
  `μ S ≤ M · ν S` fails for every `M`.  Concretely, `ellProb K δ` vanishes on the stuck points
  (`ellProb_stuckPoints`) and more generally is exponentially thin near `∂K`, while the uniform
  measure is not; TV closeness says nothing about that ratio.
* **From warmness with respect to the uniform measure: yes, at a multiplicative price `θ⁻¹`.**
  `isWarm_ellProb_of_isWarm_uniformOn` below: `IsWarm M mu0 (uniformOn volume K)` implies
  `IsWarm (M · θ⁻¹) mu0 (ellProb K δ)` whenever `θ ≤ ell K δ` pointwise on `K`.  The price is
  `θ⁻¹ = ((γ+D)/γ)ⁿ`, again exponential in `n` and again only `log`-costly.  The crux is
  `mul_uniformOn_le_ellProb`, `θ · uniformOn volume K S ≤ ellProb K δ S`, which needs **no**
  guard on `vol(K)` at all.

So the transfer succeeds, but it must go through the *pointwise* floor on `ell`, never through
the total-variation bridge.

## Main results

* `Arlib.MarkovChains.div_le_mul_of_le_mul` — the `ℝ≥0∞` arithmetic, standalone.
* `Arlib.MarkovChains.mul_volume_inter_le_ellMeasure` — `θ·vol(S ∩ B) ≤ ellMeasure K δ S` for
  `B ⊆ K` and a pointwise floor `θ` on `ell`.
* `Arlib.MarkovChains.isWarm_uniformOn_ellProb` — **the general warm start**: uniform-on-`B` is
  `M`-warm for `ellProb K δ` once `vol(K) ≤ M·θ·vol(B)`.
* `Arlib.MarkovChains.isWarm_uniformOn_unitBall_ellProb`,
  `Arlib.MarkovChains.isWarm_uniformOn_unitBall_ellProb_ratio`,
  `Arlib.MarkovChains.exists_warm_uniformOn_unitBall_ellProb` — **the headline**: on a convex `K`
  with `B(0,1) ⊆ K` and diameter `≤ D`, uniform-on-`B(0,1)` is `M`-warm for `ellProb K δ` with
  `M = (1+D)ⁿ·vol(K)/vol(B(0,1))`, and `1 ≤ M`.
* `Arlib.MarkovChains.mul_uniformOn_le_ellProb`,
  `Arlib.MarkovChains.isWarm_ellProb_of_isWarm_uniformOn` — the transfer of §"Does
  uniform-warmness transfer".
* `Arlib.MarkovChains.isWarm_uniformOn_of_density_le`,
  `Arlib.MarkovChains.isWarm_ellProb_of_density_le` — the general lemma: any `mu0` whose density
  relative to Lebesgue on `K` is bounded by `C` is `C·vol(K)·θ⁻¹`-warm for `ellProb K δ`.
* `Arlib.MarkovChains.isWarm_uniformOn_unitBall_ellProb_unitBall` — the non-vacuity witness
  (`CLAUDE.md` §11): a concrete body (`K = B(0,1)`), a concrete `mu0` (uniform on `B(0,1)`) and a
  concrete finite constant, `M = 3ⁿ`.

## Scope

**No `def`, `structure`, `class`, `axiom` or named `Prop` is introduced anywhere in this file.**
Every declaration is a `theorem`.  In particular no predicate asserting a warmness bound is
defined: `Arlib.IsWarm` is imported from `Arlib/Probability/TV.lean` and only ever *concluded*
here, never assumed except in the transfer lemmas, where it is the caller's input for a
*different* target measure.
-/

namespace Arlib.MarkovChains

open MeasureTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The arithmetic

One lemma about five extended nonnegative reals; no measure theory in it. -/

/-- **The comparison of a normalised restriction with a weighted normalisation, as pure `ℝ≥0∞`
arithmetic.**

If `0 < W < ⊤`, `0 < V < ⊤` and `V ≤ M·(θ·W)`, then

    b / W  ≤  M · (V⁻¹ · (θ · b)).

Read `b = vol(S ∩ B)`, `W = vol(B)`, `V = vol(K)`, `θ` a pointwise floor on `ell`: the left side
is `uniformOn volume B S` and the right side is a lower bound for `M · ellProb K δ S`.

The whole content is `b·W⁻¹ = (b·V⁻¹)·(V·W⁻¹)`, valid because `V` is a unit, followed by
`V·W⁻¹ ≤ M·θ`, which is the hypothesis divided by the unit `W`. -/
theorem div_le_mul_of_le_mul {b W V θ M : ℝ≥0∞} (hW0 : W ≠ 0) (hWtop : W ≠ ⊤)
    (hV0 : V ≠ 0) (hVtop : V ≠ ⊤) (hM : V ≤ M * (θ * W)) :
    b / W ≤ M * (V⁻¹ * (θ * b)) := by
  have hVW : V * W⁻¹ ≤ M * θ := by
    calc V * W⁻¹ ≤ (M * (θ * W)) * W⁻¹ := mul_le_mul' hM le_rfl
      _ = (M * θ) * (W * W⁻¹) := by ring
      _ = M * θ := by rw [ENNReal.mul_inv_cancel hW0 hWtop, mul_one]
  calc b / W = b * W⁻¹ := div_eq_mul_inv _ _
    _ = (b * V⁻¹) * (V * W⁻¹) := by
        rw [show (b * V⁻¹) * (V * W⁻¹) = b * (V⁻¹ * V) * W⁻¹ from by ring,
          ENNReal.inv_mul_cancel hV0 hVtop, mul_one]
    _ ≤ (b * V⁻¹) * (M * θ) := mul_le_mul' le_rfl hVW
    _ = M * (V⁻¹ * (θ * b)) := by ring

/-! ## 2. The measure-theoretic crux

A pointwise floor on the local conductance becomes a setwise floor on the unnormalised
`ell`-weight. -/

/-- **A pointwise floor on `ell` gives a setwise floor on `ellMeasure`.**

If `B ⊆ K` and `θ ≤ ell K δ x` for every `x ∈ K`, then for every measurable `S`

    θ · vol(S ∩ B)  ≤  ellMeasure K δ S.

The chain is `θ·vol(S∩B) = ∫_{S∩B} θ ≤ ∫_{S∩B} ell ≤ ∫_{S∩K} ell = ellMeasure K δ S`, using
`B ⊆ K` twice: once so that the floor applies on `S ∩ B`, once to enlarge the domain.

This is the exact mirror of `ellMeasure_le_volume_inter` (`SpeedyWalk.lean:1381`), which is the
upper bound `ellMeasure K δ S ≤ vol(S ∩ K)` coming from `ell ≤ 1`.  Nothing here needs `δ > 0`,
convexity, or any bound on `vol(K)`. -/
theorem mul_volume_inter_le_ellMeasure {K B : Set (EuclideanSpace ℝ (Fin n))}
    (hB : MeasurableSet B) (hBK : B ⊆ K) {δ : ℝ} {θ : ℝ≥0∞}
    (hθ : ∀ x ∈ K, θ ≤ ell K δ x) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) :
    θ * volume (S ∩ B) ≤ ellMeasure K δ S := by
  have hsub : S ∩ B ⊆ S ∩ K := fun x hx => ⟨hx.1, hBK hx.2⟩
  have hval : ellMeasure K δ S = ∫⁻ x in S ∩ K, ell K δ x := by
    rw [ellMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS]
  rw [hval]
  calc θ * volume (S ∩ B) = ∫⁻ _ in S ∩ B, θ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in S ∩ B, ell K δ x := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem (hS.inter hB)] with x hx
        exact hθ x (hBK hx.2)
    _ ≤ ∫⁻ x in S ∩ K, ell K δ x :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

/-! ## 3. The general warm start -/

/-- **The uniform measure on an inscribed set `B ⊆ K` is a warm start for `ellProb K δ`.**

Assumed: `B` measurable with `B ⊆ K` and `vol(B) ≠ 0`; `vol(K) ≠ ⊤`; a pointwise floor
`θ ≤ ell K δ` on `K`; and the calibration `vol(K) ≤ M·(θ·vol(B))`.

Proved: `IsWarm M (Arlib.uniformOn volume B) (ellProb K δ)`, i.e. setwise
`uniformOn volume B S ≤ M · ellProb K δ S`.

Note what carries the argument.  `ellProb K δ S = L⁻¹·ellMeasure K δ S` with `L = ∫_K ell ≤ vol(K)`
(`ellMeasure_univ_le`), so shrinking the normaliser to `vol(K)` only *lowers* the bound; and
`mul_volume_inter_le_ellMeasure` lowers the numerator to `θ·vol(S ∩ B)`.  What remains is
`div_le_mul_of_le_mul`.  No convexity, no positivity of `δ`, and no isoperimetry. -/
theorem isWarm_uniformOn_ellProb {K B : Set (EuclideanSpace ℝ (Fin n))}
    (hB : MeasurableSet B) (hBK : B ⊆ K) (hB0 : volume B ≠ 0) (hKtop : volume K ≠ ⊤)
    {δ : ℝ} {θ : ℝ≥0∞} (hθ : ∀ x ∈ K, θ ≤ ell K δ x)
    {M : ℝ≥0∞} (hM : volume K ≤ M * (θ * volume B)) :
    IsWarm M (Arlib.uniformOn volume B) (ellProb K δ) := by
  have hBV : volume B ≤ volume K := measure_mono hBK
  have hV0 : volume K ≠ 0 := fun h => hB0 (measure_mono_null hBK h)
  have hBtop : volume B ≠ ⊤ := ne_top_of_le_ne_top hKtop hBV
  intro S hS
  rw [Arlib.uniformOn_apply volume hB hS, ellProb, Measure.smul_apply, smul_eq_mul]
  calc volume (S ∩ B) / volume B
      ≤ M * ((volume K)⁻¹ * (θ * volume (S ∩ B))) :=
        div_le_mul_of_le_mul hB0 hBtop hV0 hKtop hM
    _ ≤ M * ((ellMeasure K δ Set.univ)⁻¹ * ellMeasure K δ S) :=
        mul_le_mul' le_rfl (mul_le_mul' (ENNReal.inv_le_inv.mpr (ellMeasure_univ_le K δ))
          (mul_volume_inter_le_ellMeasure hB hBK hθ hS))

/-! ## 4. The headline: a convex body with an inscribed unit ball

`le_ell_of_convex_of_ball_subset` supplies `θ = (1/(1+D))ⁿ`, and the calibration constant is the
volume ratio `vol(K)/vol(B(0,1))`. -/

/-- **The warm-start constant is at least `1`.**  Pure arithmetic: `1 ≤ (1+D)ᵐ` for `0 ≤ D`, and
`1 ≤ c`.  This is the `hM : 1 ≤ M` hypothesis of `mixesWithin_lazy_speedyWalk_uniformOn`. -/
theorem one_le_warmConst {D c : ℝ} (hD0 : 0 ≤ D) (hc : 1 ≤ c) (m : ℕ) :
    1 ≤ (1 + D) ^ m * c := by
  have h1 : (1 : ℝ) ≤ (1 + D) ^ m := one_le_pow₀ (by linarith)
  nlinarith

/-- **The warm start on a convex body with an inscribed unit ball.**

Assumed: `K` convex, `B(0,1) ⊆ K`, all pairwise distances in `K` bounded by `D`, a step size
`0 < δ ≤ 1`, and a volume calibration `vol(K) ≤ c·vol(B(0,1))` with `1 ≤ c`.

Proved:

    IsWarm (ENNReal.ofReal ((1 + D)ⁿ · c)) (uniformOn volume (B(0,1))) (ellProb K δ).

The constant is exponential in `n` — see the module docstring; only `log M` enters
`conductanceMixingTime`, so this costs one factor of `n` in the step count and no more.

`hKtop` is *not* a hypothesis: `volume_ne_top_of_diam_bound` derives it from `hD`. -/
theorem isWarm_uniformOn_unitBall_ellProb {K : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ K) (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {c : ℝ} (hc : 1 ≤ c)
    (hvol : volume K
      ≤ ENNReal.ofReal c * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    IsWarm (ENNReal.ofReal ((1 + D) ^ n * c))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (ellProb K δ) := by
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (Metric.mem_ball_self one_pos)
  have hD0 : (0 : ℝ) ≤ D := by simpa using hD 0 h0K 0 h0K
  have hD1 : (0 : ℝ) < 1 + D := by linarith
  have hKtop : volume K ≠ ⊤ := volume_ne_top_of_diam_bound h0K hD
  have hθ : ∀ x ∈ K, ENNReal.ofReal ((1 / (1 + D)) ^ n) ≤ ell K δ x :=
    le_ell_of_convex_of_ball_subset hconv one_pos hball hD hδ hδ1
  refine isWarm_uniformOn_ellProb measurableSet_ball hball volume_unitBall_ne_zero hKtop hθ ?_
  have hpow : (1 + D) ^ n * c * (1 / (1 + D)) ^ n = c := by
    have hne : (1 : ℝ) + D ≠ 0 := hD1.ne'
    have hcancel : (1 + D) * (1 / (1 + D)) = 1 := by field_simp
    calc (1 + D) ^ n * c * (1 / (1 + D)) ^ n
        = ((1 + D) * (1 / (1 + D))) ^ n * c := by rw [mul_pow]; ring
      _ = c := by rw [hcancel, one_pow, one_mul]
  have hkey : ENNReal.ofReal ((1 + D) ^ n * c) * ENNReal.ofReal ((1 / (1 + D)) ^ n)
      = ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_mul (by positivity), hpow]
  calc volume K
      ≤ ENNReal.ofReal c * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := hvol
    _ = (ENNReal.ofReal ((1 + D) ^ n * c) * ENNReal.ofReal ((1 / (1 + D)) ^ n))
          * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by rw [hkey]
    _ = ENNReal.ofReal ((1 + D) ^ n * c)
          * (ENNReal.ofReal ((1 / (1 + D)) ^ n)
            * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) := mul_assoc _ _ _

/-- **The volume calibration is free**: `V = ofReal (V.toReal / W.toReal) · W` whenever `V < ⊤`
and `0 < W < ⊤`.  This is what turns the parameter `c` of `isWarm_uniformOn_unitBall_ellProb`
into the honest ratio `vol(K)/vol(B(0,1))`, with no extra hypothesis on the caller. -/
theorem ofReal_toReal_div_mul {V W : ℝ≥0∞} (hVtop : V ≠ ⊤) (hW0 : W ≠ 0) (hWtop : W ≠ ⊤) :
    ENNReal.ofReal (V.toReal / W.toReal) * W = V := by
  rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hW0 hWtop), ENNReal.ofReal_toReal hVtop,
    ENNReal.ofReal_toReal hWtop, ENNReal.div_mul_cancel hW0 hWtop]

/-- **The warm start with the ratio spelled out.**  Same hypotheses as
`isWarm_uniformOn_unitBall_ellProb` minus the calibration, with

    M = (1 + D)ⁿ · vol(K) / vol(B(0,1)).

This is the explicit constant advertised in the module docstring. -/
theorem isWarm_uniformOn_unitBall_ellProb_ratio {K : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ K) (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    IsWarm (ENNReal.ofReal ((1 + D) ^ n *
        ((volume K).toReal
          / (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (ellProb K δ) := by
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (Metric.mem_ball_self one_pos)
  have hKtop : volume K ≠ ⊤ := volume_ne_top_of_diam_bound h0K hD
  have hW0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 := volume_unitBall_ne_zero
  have hWtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := volume_unitBall_ne_top
  have hWpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal :=
    ENNReal.toReal_pos hW0 hWtop
  have hle : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
      ≤ (volume K).toReal := ENNReal.toReal_mono hKtop (measure_mono hball)
  refine isWarm_uniformOn_unitBall_ellProb hconv hball hD ((one_le_div hWpos).2 hle) ?_ hδ hδ1
  exact le_of_eq (ofReal_toReal_div_mul hKtop hW0 hWtop).symm

/-- **The warm start, packaged for `mixesWithin_lazy_speedyWalk_uniformOn`.**

`∃ M : ℝ, 1 ≤ M ∧ IsWarm (ENNReal.ofReal M) (uniformOn volume (B(0,1))) (ellProb K δ)` — exactly
the pair `(hM, hwarm)` that `SpeedyToUniform.lean:236-237` asks for, with `mu0` a law one can
actually sample from.  The witness is `M = (1+D)ⁿ·vol(K)/vol(B(0,1))`. -/
theorem exists_warm_uniformOn_unitBall_ellProb {K : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ K) (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ M : ℝ, 1 ≤ M ∧
      IsWarm (ENNReal.ofReal M)
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
        (ellProb K δ) := by
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (Metric.mem_ball_self one_pos)
  have hD0 : (0 : ℝ) ≤ D := by simpa using hD 0 h0K 0 h0K
  have hKtop : volume K ≠ ⊤ := volume_ne_top_of_diam_bound h0K hD
  have hW0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 := volume_unitBall_ne_zero
  have hWtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := volume_unitBall_ne_top
  have hWpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal :=
    ENNReal.toReal_pos hW0 hWtop
  have hle : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
      ≤ (volume K).toReal := ENNReal.toReal_mono hKtop (measure_mono hball)
  exact ⟨_, one_le_warmConst hD0 ((one_le_div hWpos).2 hle) n,
    isWarm_uniformOn_unitBall_ellProb_ratio hconv hball hD hδ hδ1⟩

/-! ## 5. Transfer from uniform-warmness

The answer to "does `M`-warmness for `uniformOn volume K` give `M'`-warmness for `ellProb K δ`?"
It does — but only through a *pointwise* floor on `ell`, never through
`tvLe_ellProb_uniformOn`.  See the module docstring. -/

/-- **`ellProb K δ` dominates `θ` times the uniform measure on `K`**, for any pointwise floor
`θ ≤ ell K δ` on `K`:

    θ · uniformOn volume K S  ≤  ellProb K δ S      for every measurable `S`.

**No guard on `vol(K)` is needed at all** — not positivity, not finiteness.  The two normalisers
are `vol(K)` and `L = ∫_K ell ≤ vol(K)`, and `ENNReal.inv_le_inv` reverses that inequality
unconditionally; at `vol(K) ∈ {0, ⊤}` both sides degenerate consistently.

This is the exact multiplicative statement that a total-variation bound such as
`tvLe_ellProb_uniformOn` cannot deliver. -/
theorem mul_uniformOn_le_ellProb {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {δ : ℝ} {θ : ℝ≥0∞} (hθ : ∀ x ∈ K, θ ≤ ell K δ x)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    θ * Arlib.uniformOn volume K S ≤ ellProb K δ S := by
  rw [Arlib.uniformOn_apply volume hK hS, ellProb, Measure.smul_apply, smul_eq_mul]
  calc θ * (volume (S ∩ K) / volume K)
      = (volume K)⁻¹ * (θ * volume (S ∩ K)) := by rw [div_eq_mul_inv]; ring
    _ ≤ (ellMeasure K δ Set.univ)⁻¹ * ellMeasure K δ S :=
        mul_le_mul' (ENNReal.inv_le_inv.mpr (ellMeasure_univ_le K δ))
          (mul_volume_inter_le_ellMeasure hK (subset_refl K) hθ hS)

/-- **Uniform-warmness transfers to `ellProb`-warmness at multiplicative cost `θ⁻¹`.**

`IsWarm M mu0 (uniformOn volume K)` and a pointwise floor `θ ≤ ell K δ` on `K` give
`IsWarm (M · θ⁻¹) mu0 (ellProb K δ)`.

With `le_ell_of_convex_of_ball_subset` the price is `θ⁻¹ = ((γ+D)/γ)ⁿ` — exponential in `n`,
hence a factor `n` in the step count via `conductanceMixingTime_le`.

This is the honest form of the transfer.  It is emphatically **not** obtainable from
`tvLe_ellProb_uniformOn`: a total-variation bound is additive and permits `ellProb K δ S = 0` with
`uniformOn volume K S > 0`, on which no multiplicative bound can hold
(`Arlib/Probability/TV.lean:364`). -/
theorem isWarm_ellProb_of_isWarm_uniformOn {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} {θ : ℝ≥0∞} (hθ0 : θ ≠ 0) (hθtop : θ ≠ ⊤)
    (hθ : ∀ x ∈ K, θ ≤ ell K δ x) {M : ℝ≥0∞}
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))}
    (hwarm : IsWarm M mu0 (Arlib.uniformOn volume K)) :
    IsWarm (M * θ⁻¹) mu0 (ellProb K δ) := by
  intro S hS
  calc mu0 S ≤ M * Arlib.uniformOn volume K S := hwarm S hS
    _ = (M * θ⁻¹) * (θ * Arlib.uniformOn volume K S) := by
        rw [show (M * θ⁻¹) * (θ * Arlib.uniformOn volume K S)
              = M * (θ⁻¹ * θ) * Arlib.uniformOn volume K S from by ring,
          ENNReal.inv_mul_cancel hθ0 hθtop, mul_one]
    _ ≤ (M * θ⁻¹) * ellProb K δ S := mul_le_mul' le_rfl (mul_uniformOn_le_ellProb hK hθ hS)

/-! ## 6. The general lemma: any `mu0` with a bounded density on `K` -/

/-- **A bounded density relative to Lebesgue on `K` gives uniform-warmness.**  If
`mu0 S ≤ C · vol(S ∩ K)` setwise, then `mu0` is `C·vol(K)`-warm for `uniformOn volume K`.  Both
guards on `vol(K)` are needed: the uniform measure is not a probability measure without them. -/
theorem isWarm_uniformOn_of_density_le {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hV0 : volume K ≠ 0) (hVtop : volume K ≠ ⊤) {C : ℝ≥0∞}
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))}
    (hdens : ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S →
      mu0 S ≤ C * volume (S ∩ K)) :
    IsWarm (C * volume K) mu0 (Arlib.uniformOn volume K) := by
  intro S hS
  rw [Arlib.uniformOn_apply volume hK hS]
  calc mu0 S ≤ C * volume (S ∩ K) := hdens S hS
    _ = C * volume K * (volume (S ∩ K) / volume K) := by
        rw [mul_assoc, ENNReal.mul_div_cancel hV0 hVtop]

/-- **The general warm-start lemma.**  Any `mu0` whose density relative to Lebesgue on `K` is
bounded by `C` — i.e. `mu0 S ≤ C·vol(S ∩ K)` setwise — is `C·vol(K)·θ⁻¹`-warm for `ellProb K δ`,
where `θ` is any pointwise floor on the local conductance.

With `le_ell_of_convex_of_ball_subset` (`ConvexBodyMixing.lean:93`) the floor is
`θ = (γ/(γ+D))ⁿ`, so the constant is `C·vol(K)·((γ+D)/γ)ⁿ`: exponentially large, but only
`log M` enters `conductanceMixingTime` (`MixingFromConductance.lean:179-182`).

`isWarm_uniformOn_unitBall_ellProb` is the sharper route when `mu0` is uniform on an inscribed
ball: it avoids the `vol(K)` factor incurred here by comparing directly against `vol(B)`. -/
theorem isWarm_ellProb_of_density_le {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hV0 : volume K ≠ 0) (hVtop : volume K ≠ ⊤)
    {δ : ℝ} {θ : ℝ≥0∞} (hθ0 : θ ≠ 0) (hθtop : θ ≠ ⊤) (hθ : ∀ x ∈ K, θ ≤ ell K δ x)
    {C : ℝ≥0∞} {mu0 : Measure (EuclideanSpace ℝ (Fin n))}
    (hdens : ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S →
      mu0 S ≤ C * volume (S ∩ K)) :
    IsWarm (C * volume K * θ⁻¹) mu0 (ellProb K δ) :=
  isWarm_ellProb_of_isWarm_uniformOn hK hθ0 hθtop hθ
    (isWarm_uniformOn_of_density_le hK hV0 hVtop hdens)

/-! ## 7. Non-vacuity: a concrete body, a concrete `mu0`, a concrete finite `M`

`CLAUDE.md` §11.  Every theorem above is an implication; without an instance in which all the
hypotheses hold *and* `M` is finite, they certify nothing.  Take `K = B(0,1)` — convex, its own
inscribed unit ball, of diameter at most `2` — and `mu0 = uniformOn volume (B(0,1))`.  Then the
calibration holds with `c = 1` and the constant is `M = 3ⁿ`: finite, explicit, and exponential in
`n` exactly as advertised. -/

/-- **The diameter of the unit ball is at most `2`.**  The `hD` hypothesis of the witness. -/
theorem dist_le_two_of_mem_unitBall
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    dist x y ≤ 2 := by
  rw [Metric.mem_ball] at hx hy
  have h := dist_triangle x 0 y
  rw [dist_comm (0 : EuclideanSpace ℝ (Fin n)) y] at h
  linarith

/-- **The non-vacuity witness.**  For `K = B(0,1)` and `0 < δ ≤ 1`,

    IsWarm (ENNReal.ofReal (3ⁿ)) (uniformOn volume (B(0,1))) (ellProb (B(0,1)) δ),

with the companion `1 ≤ 3ⁿ` supplied by `one_le_warmConst`.  A concrete body, a concrete
starting law that can actually be sampled, and a concrete finite `M` — unlike
`SpeedyWalk.lean:1343`, whose warm start is `IsWarm 1 (ellProb …) (ellProb …)`, i.e. starting the
chain from its own stationary measure. -/
theorem isWarm_uniformOn_unitBall_ellProb_unitBall {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    IsWarm (ENNReal.ofReal ((3 : ℝ) ^ n))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ) := by
  have h := isWarm_uniformOn_unitBall_ellProb (K := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    (convex_ball _ _) (subset_refl _) (D := 2) dist_le_two_of_mem_unitBall (c := 1) le_rfl
    (by rw [ENNReal.ofReal_one, one_mul]) hδ hδ1
  rwa [show ((1 : ℝ) + 2) ^ n * 1 = (3 : ℝ) ^ n from by norm_num] at h

/-- The witness's constant really is at least `1`, as
`mixesWithin_lazy_speedyWalk_uniformOn`'s `hM` demands. -/
theorem one_le_three_pow : (1 : ℝ) ≤ (3 : ℝ) ^ n := by
  have h := one_le_warmConst (D := 2) (c := 1) (by norm_num) le_rfl n
  rwa [show ((1 : ℝ) + 2) ^ n * 1 = (3 : ℝ) ^ n from by norm_num] at h

/-! ## Axiom check -/

#print axioms div_le_mul_of_le_mul
#print axioms mul_volume_inter_le_ellMeasure
#print axioms isWarm_uniformOn_ellProb
#print axioms one_le_warmConst
#print axioms isWarm_uniformOn_unitBall_ellProb
#print axioms ofReal_toReal_div_mul
#print axioms isWarm_uniformOn_unitBall_ellProb_ratio
#print axioms exists_warm_uniformOn_unitBall_ellProb
#print axioms mul_uniformOn_le_ellProb
#print axioms isWarm_ellProb_of_isWarm_uniformOn
#print axioms isWarm_uniformOn_of_density_le
#print axioms isWarm_ellProb_of_density_le
#print axioms dist_le_two_of_mem_unitBall
#print axioms isWarm_uniformOn_unitBall_ellProb_unitBall
#print axioms one_le_three_pow

end Arlib.MarkovChains
