/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.SpeedyWalk
import Arlib.MarkovChains.Continuous.OverlapSqrt

/-!
# The conductance of the speedy walk, at separation `δ/√n`

`Arlib.MarkovChains.conductance_speedyWalk_ge` (`SpeedyWalk.lean:973`) certifies

    Φ(speedy walk on K, step δ)  ≥  min(1/16, κ·(δ/(2n))/64),

where the separation fed to the isoperimetric hypothesis is `δ/(2n)`.  This file replaces
that separation by `δ/√n` and certifies

    Φ(speedy walk on K, step δ)  ≥  min(1/96, κ·(δ/√n)/384),

at the price of one extra hypothesis, spelled out below.  Since the mixing time is `Φ⁻²`,
a `√n` in `Φ` is a factor `n` in the step count; `sqrt_gain_eq` measures the gain exactly
(it is `√n/3`, an equality, not an estimate) and `old_div_six_le_new` states the
full-bound comparison unconditionally.

## What the extra hypothesis is, and where it comes from

The `δ/(2n)` separation is bought by the *elementary* overlap estimate
`Arlib.MarkovChains.one_le_speedyWalk_add_speedyWalk_compl`, which costs `n‖u−v‖/δ` and
needs **no** hypothesis at all beyond convexity.  The `δ/√n` separation is bought by
`Arlib.MarkovChains.one_le_twelve_mul_speedyWalk_add_of_comparable` (`OverlapSqrt.lean:439`),
whose geometry is [KLS95, Lemma 3.5] and which needs the two ball slices at `u` and `v` to be
**comparable**:

    max(vol(B(u,δ) ∩ K), vol(B(v,δ) ∩ K)) ≤ (3/2)·min(vol(B(u,δ) ∩ K), vol(B(v,δ) ∩ K)),

equivalently `ℓ(u) ≤ (3/2)·ℓ(v)` and `ℓ(v) ≤ (3/2)·ℓ(u)`.  The speedy walk normalises each
one-step law by *its own* `vol(B(x,δ) ∩ K)`, so unlike the ball walk it has no `vol(δBⁿ)` to
compare both slices against; comparability is exactly what replaces it.  This is
Cousins–Vempala's own hypothesis `d_ℓ(u,v) < 1/3` (`1409.6011/vol3_journal.tex:581`), and
`Arlib.MarkovChains.ell_le_of_densDist_ell_lt` proves the two are the same statement.

**It is carried as an explicit binder and is not discharged here.**  It is not automatic:
`Arlib.MarkovChains.exists_ell_not_comparable_at_sqrt_dim_counterexample`
(`OverlapSqrt.lean:816`) exhibits a bounded convex body of positive volume and a pair of
points at separation `δ/√n` where it fails.

## Provenance: this is a reconstruction, not a transcription

Lee's book *states* the speedy walk's conductance as `Ω(1/(nD))` (`ball_walk.tex:809–811`)
and gives **no proof** — the speedy walk gets one exercise (`ball_walk.tex:804–807`, that the
stationary density is proportional to `ℓ`) and that one unproved theorem.  So there is no
book argument to transcribe here; the argument below is assembled from the repository's own
`δ/√n` overlap machinery.

What the book *does* prove at `δ/√n` is for the **ball walk**, and it uses a different device
in place of comparability (`ball_walk.tex:700–772`): it restricts the whole three-way
partition to the **good-points body**

    K_δ = {x ∈ K : ℓ(x) ≥ 3/4},

which `lem:avg-local-conductance` (`ball_walk.tex:674–678`) asserts is *convex* with
`vol(K_δ) ≥ (1 − 2δ√n)·vol(K)`, applies isoperimetry to `K_δ` under the uniform measure, and
pays for the restriction with `s`-conductance slack (`vol(S_i'') ≥ vol(S_i') − s`, `:736–740`).
Inside `K_δ` the one-step lemma `lem:ONESTEP` (`:501–504`) is applied with `ℓ = 3/4` at both
endpoints — a **two-sided floor on a subset**, not a comparison of `ℓ` values.

`three_quarters_le_ell_comparable` below records, machine-checked, that the book's device is
*strictly stronger* than the binder this file carries: `ℓ(u), ℓ(v) ≥ 3/4` implies
comparability at the constant `3/2`, because `ℓ ≤ 1` always.  So a proof of the `K_δ` route
would discharge this file's `hcomp` on `K_δ`.  That route is being built elsewhere; nothing
in this file duplicates it.

The two devices are **incomparable**, not nested: `ell_ball_three_lt_three_quarters` exhibits
a bounded convex body on which `K_δ = ∅` — the book's device is vacuous there — while `hcomp`
holds with equality (`conductance_speedyWalk_sqrt_ballThree`).

## Relation to `EllFloor.lean`

`Arlib.MarkovChains.metropolis_ell_floor_unsatisfiable_on_cube` (`EllFloor.lean:402`) shows
that a **global constant floor** `ℓ(x) ≥ θ` with `θ` bounded away from `0` is unsatisfiable on
a cube from dimension `3` on — the corner forces `ℓ ≤ 2⁻ⁿ`.  That negative does **not** apply
to the binder carried here: comparability compares `ℓ` at two *nearby* points and says nothing
about its size.  `conductance_speedyWalk_sqrt_ballThree` is a body where `ℓ ≡ 1/9`, far below
any useful floor (compare `Arlib.MarkovChains.general_ell_floor_le_three_pow_neg`), and where
`hcomp` nevertheless holds outright.  So the honest status of the `n²`-step target on this
route is **conditionally reachable, modulo `hcomp` and `hiso` — not blocked by `EllFloor`**.

## Two calibrations, so the gain is not overstated

*What is machine-checked is the conductance comparison, not the step count.*  `sqrt_gain_eq`,
`old_second_le_new_second` and `old_div_six_le_new` are theorems about `Φ`.  The statement
"hence a factor `n/9` off the mixing time" is the `Φ⁻²` arithmetic applied by hand; the
`Φ⁻²` machinery of `Arlib/MarkovChains/Continuous/MixingSqrt.lean` is wired to the Gaussian
route and is *not* instantiated at the bound proved here.

*The `n²` the book reports is not measured in the same units.*  The book's `O(n²/ψ²)` ball-walk
mixing rate (`ball_walk.tex:663–668`, shown tight at `:776–789`) carries a **poly(1/ε)**
dependence on the target accuracy, which is exactly the defect the speedy walk exists to
repair (`ball_walk.tex:797–799`); this repository's composition delivers **log(M/ε)**.  So
"the book gets `n²`, we get `n⁴`" understates what is being bought on this side, and the two
figures should not be subtracted as if they were the same quantity.

## Scope

No `def`, `structure`, `class` or `axiom` is introduced.  Every input — the isoperimetric
inequality and the comparability of local conductances — is an inline `∀`-hypothesis of the
theorem that consumes it.  Neither is proved here, so **no theorem in this file is a
polynomial-time statement and none may be quoted as one**.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

section SpeedyConductanceSqrt

variable {n : ℕ}

/-! ## 1. The book's `ℓ ≥ 3/4` restriction implies the comparability binder

`ball_walk.tex:734` restricts to `K_δ = {ℓ ≥ 3/4}` and applies `lem:ONESTEP` there with
`ℓ = 3/4` at *both* endpoints.  Because `ℓ ≤ 1` unconditionally, that floor is strictly
stronger than the `3/2`-comparability this file carries: `ℓ(u) ≤ 1 ≤ (3/2)·(3/4) ≤ (3/2)·ℓ(v)`.
So the book's device, once available, discharges `hcomp` pointwise on `K_δ`. -/

/-- `3/4` in `ℝ≥0∞` is `ENNReal.ofReal (3/4)`. -/
theorem ofReal_three_quarters :
    ENNReal.ofReal (3 / 4 : ℝ) = (3 : ℝ≥0∞) / 4 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
  simp

/-- **The `ℓ ≥ 3/4` floor implies `3/2`-comparability, one-sidedly and for free.**

Only the floor *at the target point* `v` is used, together with `ell ≤ 1`
(`Arlib.MarkovChains.ell_le_one`): `ℓ(u) ≤ 1 ≤ (3/2)·(3/4) ≤ (3/2)·ℓ(v)`.

This is the precise sense in which the book's good-points device (`ball_walk.tex:674–678`,
`:734`) is stronger than the hypothesis carried by this file.  It is *not* used in the proof
of the conductance bound — it is the bridge that lets a proof of the `K_δ` route discharge
`hcomp` on `K_δ` without any further work. -/
theorem ell_le_of_three_quarters_le_ell {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    {u v : EuclideanSpace ℝ (Fin n)} (hv : (3 : ℝ≥0∞) / 4 ≤ ell K δ v) :
    ell K δ u ≤ ENNReal.ofReal (3 / 2) * ell K δ v := by
  have e98 : ENNReal.ofReal (3 / 2 : ℝ) * ((3 : ℝ≥0∞) / 4) = ENNReal.ofReal (9 / 8 : ℝ) := by
    rw [← ofReal_three_quarters, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3 / 2)]
    norm_num
  have e1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (9 / 8 : ℝ) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  calc ell K δ u ≤ 1 := ell_le_one K δ u
    _ ≤ ENNReal.ofReal (9 / 8 : ℝ) := e1
    _ = ENNReal.ofReal (3 / 2) * ((3 : ℝ≥0∞) / 4) := e98.symm
    _ ≤ ENNReal.ofReal (3 / 2) * ell K δ v := by gcongr

/-- **Two-sided form**: the book's `K_δ` floor at both endpoints gives exactly the ball-slice
comparability that `Arlib.MarkovChains.one_le_twelve_mul_speedyWalk_add_of_comparable` wants.

`Arlib.MarkovChains.three_quarters_le_ell_of_mem_speedyPoints` says the hypotheses hold *by
definition* on `Arlib.MarkovChains.SpeedyPoints K δ`, which is the repository's name for
`K_δ`. -/
theorem three_quarters_le_ell_comparable {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    (hδ : 0 < δ) {u v : EuclideanSpace ℝ (Fin n)}
    (hu : (3 : ℝ≥0∞) / 4 ≤ ell K δ u) (hv : (3 : ℝ≥0∞) / 4 ≤ ell K δ v) :
    max (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K))
      ≤ ENNReal.ofReal (3 / 2)
          * min (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K)) :=
  max_volume_ball_inter_le_of_ell_comparable hδ (ell_le_of_three_quarters_le_ell hv)
    (ell_le_of_three_quarters_le_ell hu)

/-! ## 2. The crux: separation at `δ/√n`

The contrapositive of `Arlib.MarkovChains.one_le_twelve_mul_speedyWalk_add_of_comparable`.
The escape threshold is `1/24` rather than the `1/4` of
`Arlib.MarkovChains.lt_dist_of_speedyWalk_lt`, because the overlap constant there is `12`
rather than `1`; that is the whole price paid in absolute constants for the `√n`. -/

/-- **Separation from overlap, at `δ/√n`.**  If a step from `u` leaves `T` with probability
less than `1/24` and a step from `v` enters `T` with probability less than `1/24`, and the two
ball slices are comparable, then

    δ/√n  <  ‖u − v‖.

Compare `Arlib.MarkovChains.lt_dist_of_speedyWalk_lt`, whose conclusion is `δ/(2n) < ‖u − v‖`
under no comparability hypothesis at all.  The gain is the factor `2√n`; the price is
`hcomp`. -/
theorem lt_dist_of_speedyWalk_lt_sqrt (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) {δ : ℝ} (hδ : 0 < δ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) (hu0 : u ∉ StuckPoints K δ)
    (hcomp : max (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K))
      ≤ ENNReal.ofReal (3 / 2)
          * min (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K)))
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : MeasurableSet T)
    (hu' : 24 * speedyWalk K δ u Tᶜ < 1) (hv' : 24 * speedyWalk K δ v T < 1) :
    δ / Real.sqrt n < dist u v := by
  by_contra hc
  rw [not_lt] at hc
  have hsep : ‖u - v‖ ≤ δ / Real.sqrt n := by rwa [← dist_eq_norm]
  have hu0' : volume (Metric.ball u δ ∩ K) ≠ 0 := fun h => hu0 (mem_stuckPoints_iff.2 h)
  have hov := one_le_twelve_mul_speedyWalk_add_of_comparable hn hK hKc hδ hu hv hsep hu0'
    hcomp hT
  have hlow : (2 : ℝ≥0∞) ≤ 24 * speedyWalk K δ u Tᶜ + 24 * speedyWalk K δ v T := by
    calc (2 : ℝ≥0∞) = 2 * 1 := (mul_one _).symm
      _ ≤ 2 * (12 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T)) := by gcongr
      _ = 24 * speedyWalk K δ u Tᶜ + 24 * speedyWalk K δ v T := by ring
  have hhigh : 24 * speedyWalk K δ u Tᶜ + 24 * speedyWalk K δ v T < 2 := by
    calc 24 * speedyWalk K δ u Tᶜ + 24 * speedyWalk K δ v T < 1 + 1 :=
          ENNReal.add_lt_add hu' hv'
      _ = 2 := by norm_num
  exact absurd (lt_of_le_of_lt hlow hhigh) (lt_irrefl 2)

/-- **The same, with comparability as a global binder on `K`** — the shape the conductance
proof can consume, since inside that proof the distance `‖u − v‖ ≤ δ/√n` is only available
after the `by_contra`. -/
theorem lt_dist_of_speedyWalk_lt_sqrt_global (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) {δ : ℝ} (hδ : 0 < δ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) (hu0 : u ∉ StuckPoints K δ)
    (hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ / Real.sqrt n →
      ell K δ x ≤ ENNReal.ofReal (3 / 2) * ell K δ y)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : MeasurableSet T)
    (hu' : 24 * speedyWalk K δ u Tᶜ < 1) (hv' : 24 * speedyWalk K δ v T < 1) :
    δ / Real.sqrt n < dist u v := by
  by_contra hc
  rw [not_lt] at hc
  have hsep : ‖u - v‖ ≤ δ / Real.sqrt n := by rwa [← dist_eq_norm]
  have hsep' : ‖v - u‖ ≤ δ / Real.sqrt n := by rwa [norm_sub_rev]
  have h := lt_dist_of_speedyWalk_lt_sqrt hn hK hKc hδ hu hv hu0
    (max_volume_ball_inter_le_of_ell_comparable hδ (hcomp u hu v hv hsep)
      (hcomp v hv u hu hsep')) hT hu' hv'
  exact absurd h (not_lt.2 hc)

/-! ## 3. The conductance bound at separation `δ/√n`

The three-way partition of `Arlib.MarkovChains.conductance_speedyWalk_ge`
(`SpeedyWalk.lean:973`), with two changes and nothing else:

* the escape threshold in the definitions of `S₁, S₂` is `1/24` instead of `1/4`, because
  the overlap constant of `Arlib.MarkovChains.one_le_twelve_mul_speedyWalk_add_of_comparable`
  is `12` instead of `1`;
* the separation handed to `hiso` is `δ/√n` instead of `δ/(2n)`, by
  `lt_dist_of_speedyWalk_lt_sqrt_global`.

Every other step — the flow accounting through
`Arlib.MarkovChains.mul_measure_add_measure_le_mul_flow`, the three coverings, the
`π(S) ≤ 2·π((S ∩ K₀) \ S₁)` branch — is the same argument at the new constants. -/

/-- **The conductance of the speedy walk on a convex body, at separation `δ/√n`:**

    Φ(speedy walk on K with δ-steps)  ≥  min(1/96, κ·(δ/√n)/384).

Compare `Arlib.MarkovChains.conductance_speedyWalk_ge`, which gets
`min(1/16, κ·(δ/(2n))/64)` with **no** comparability hypothesis.  The isoperimetric branch
here is larger by the exact factor `√n/3` (`sqrt_gain_eq`), hence the mixing time is smaller
by `n/9`; the whole bound is larger up to the absolute constant `6`
(`old_div_six_le_new`, unconditional in `n`).

Hypotheses that carry content:

* `hconv` — `K` is convex.  Consumed by [KLS95, Lemma 3.5] inside the overlap estimate.
* `hcomp` — **the local conductances of any two points of `K` within `δ/√n` are within a
  factor `3/2`.**  This is the new hypothesis, the whole price of the `√n`, and it is *not*
  discharged anywhere.  It is Cousins–Vempala's `d_ℓ(u,v) < 1/3`
  (`1409.6011/vol3_journal.tex:581`; see `Arlib.MarkovChains.ell_le_of_densDist_ell_lt`), it
  is satisfiable on a bounded convex body of positive volume
  (`conductance_speedyWalk_sqrt_ballThree`), and it is **not automatic**
  (`Arlib.MarkovChains.exists_ell_not_comparable_at_sqrt_dim_counterexample`).  It is implied
  by the book's `K_δ` floor (`three_quarters_le_ell_comparable`).
* `hiso` — the isoperimetric inequality for `Arlib.MarkovChains.ellProb K δ`, spelled out
  inline.  Nothing here proves it; Mathlib has no isoperimetric inequality for log-concave
  densities.

The rest are non-degeneracy guards: `2 ≤ n`, `K` measurable with `0 < vol(K) < ∞`, `0 < δ`.

**This is not a polynomial-time statement and may not be quoted as one**: `hiso` and `hcomp`
are hypotheses. -/
theorem conductance_speedyWalk_sqrt_ge (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ)
    (hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ / Real.sqrt n →
      ell K δ x ≤ ENNReal.ofReal (3 / 2) * ell K δ y)
    {kappa : ℝ≥0∞}
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      kappa * ENNReal.ofReal d * ellProb K δ A * ellProb K δ B
        ≤ ellProb K δ ((K \ A) \ B)) :
    min (1 / 96) (kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384)
      ≤ conductance (speedyWalk K δ) (ellProb K δ) := by
  haveI : IsProbabilityMeasure (ellProb K δ) :=
    isProbabilityMeasure_ellProb_of_volume hK hK0 hKtop hδ
  have hnR : (0:ℝ) < (n : ℝ) := by
    have : (0:ℕ) < n := lt_of_lt_of_le (by norm_num) hn
    exact_mod_cast this
  have hsqrt : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hdpos : (0:ℝ) < δ / Real.sqrt n := by positivity
  set pi : Measure (EuclideanSpace ℝ (Fin n)) := ellProb K δ with hpidef
  set P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    speedyWalk K δ with hPdef
  have hrev : IsReversible P pi := isReversible_speedyWalk_prob hK δ
  set K0 : Set (EuclideanSpace ℝ (Fin n)) := K ∩ (StuckPoints K δ)ᶜ with hK0def
  have hK0m : MeasurableSet K0 := hK.inter (measurableSet_stuckPoints hK δ).compl
  have hK0K : K0 ⊆ K := Set.inter_subset_left
  have hK0c : pi K0ᶜ = 0 := by
    have hset : K0ᶜ = Kᶜ ∪ StuckPoints K δ := by
      rw [hK0def, Set.compl_inter, compl_compl]
    rw [hset]
    exact measure_union_null (ellProb_compl_eq_zero hK δ) (ellProb_stuckPoints hK δ)
  refine le_conductance P pi fun S hSm hSpos hShalf => ?_
  have hpitop : pi S ≠ ⊤ := measure_ne_top _ _
  have hcompl : pi S + pi Sᶜ = 1 := by
    rw [measure_add_measure_compl hSm, measure_univ]
  have hSc : (1:ℝ≥0∞) / 2 ≤ pi Sᶜ := by
    have h1 : (1:ℝ≥0∞) / 2 + 1 / 2 ≤ 1 / 2 + pi Sᶜ := by
      calc (1:ℝ≥0∞) / 2 + 1 / 2 = 1 := ENNReal.add_halves 1
        _ = pi S + pi Sᶜ := hcompl.symm
        _ ≤ 1 / 2 + pi Sᶜ := by gcongr
    exact (ENNReal.add_le_add_iff_left (by simp)).1 h1
  set S1 : Set (EuclideanSpace ℝ (Fin n)) := (S ∩ K0) ∩ {x | 24 * P x Sᶜ < 1} with hS1def
  set S2 : Set (EuclideanSpace ℝ (Fin n)) := (K0 \ S) ∩ {x | 24 * P x S < 1} with hS2def
  have hS1m : MeasurableSet S1 :=
    (hSm.inter hK0m).inter
      (measurableSet_lt ((Kernel.measurable_coe P hSm.compl).const_mul 24) measurable_const)
  have hS2m : MeasurableSet S2 :=
    (hK0m.diff hSm).inter
      (measurableSet_lt ((Kernel.measurable_coe P hSm).const_mul 24) measurable_const)
  have hmem1 : ∀ x, x ∈ S1 ↔ ((x ∈ S ∧ x ∈ K0) ∧ 24 * P x Sᶜ < 1) := by
    intro x; rw [hS1def]; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  have hmem2 : ∀ x, x ∈ S2 ↔ ((x ∈ K0 ∧ x ∉ S) ∧ 24 * P x S < 1) := by
    intro x; rw [hS2def]; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq]
  have hS1K : S1 ⊆ K := fun x hx => hK0K ((hmem1 x).1 hx).1.2
  have hS2K : S2 ⊆ K := fun x hx => hK0K ((hmem2 x).1 hx).1.1
  -- the flow accounting
  have hSA : S \ (S1 ∪ K0ᶜ) = (S ∩ K0) \ S1 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    tauto
  have hSB : Sᶜ \ (S2 ∪ K0ᶜ) = (K0 \ S) \ S2 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff]
    tauto
  have hA' : ∀ x ∈ S \ (S1 ∪ K0ᶜ), (1:ℝ≥0∞) ≤ 24 * P x Sᶜ := by
    rw [hSA]
    rintro x ⟨⟨hxS, hxK⟩, hxS1⟩
    by_contra hc
    rw [not_le] at hc
    exact hxS1 ((hmem1 x).2 ⟨⟨hxS, hxK⟩, hc⟩)
  have hB' : ∀ x ∈ Sᶜ \ (S2 ∪ K0ᶜ), (1:ℝ≥0∞) ≤ 24 * P x S := by
    rw [hSB]
    rintro x ⟨⟨hxK, hxS⟩, hxS2⟩
    by_contra hc
    rw [not_le] at hc
    exact hxS2 ((hmem2 x).2 ⟨⟨hxK, hxS⟩, hc⟩)
  have hflow : pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2) ≤ 48 * flow P pi S Sᶜ := by
    have h := mul_measure_add_measure_le_mul_flow P pi hrev hSm (hS1m.union hK0m.compl)
      (hS2m.union hK0m.compl) hA' hB'
    rw [hSA, hSB, one_mul] at h
    calc pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2) ≤ 2 * (24 * flow P pi S Sᶜ) := h
      _ = 48 * flow P pi S Sᶜ := by ring
  -- coverings
  have hpart : pi ((K \ S1) \ S2) ≤ pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2) := by
    have hsub : (K \ S1) \ S2 ⊆ (((S ∩ K0) \ S1) ∪ ((K0 \ S) \ S2)) ∪ K0ᶜ := by
      rintro x ⟨⟨hxK, hxS1⟩, hxS2⟩
      by_cases hxK0 : x ∈ K0
      · by_cases hxS : x ∈ S
        · exact Or.inl (Or.inl ⟨⟨hxS, hxK0⟩, hxS1⟩)
        · exact Or.inl (Or.inr ⟨⟨hxK0, hxS⟩, hxS2⟩)
      · exact Or.inr hxK0
    calc pi ((K \ S1) \ S2) ≤ pi ((((S ∩ K0) \ S1) ∪ ((K0 \ S) \ S2)) ∪ K0ᶜ) :=
          measure_mono hsub
      _ ≤ pi (((S ∩ K0) \ S1) ∪ ((K0 \ S) \ S2)) + pi K0ᶜ := measure_union_le _ _
      _ ≤ (pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2)) + pi K0ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2) := by rw [hK0c, add_zero]
  have hcov1 : pi S ≤ pi ((S ∩ K0) \ S1) + pi S1 := by
    have hsub : S ⊆ (((S ∩ K0) \ S1) ∪ S1) ∪ K0ᶜ := by
      intro x hx
      by_cases hxK : x ∈ K0
      · by_cases hxS1 : x ∈ S1
        · exact Or.inl (Or.inr hxS1)
        · exact Or.inl (Or.inl ⟨⟨hx, hxK⟩, hxS1⟩)
      · exact Or.inr hxK
    calc pi S ≤ pi ((((S ∩ K0) \ S1) ∪ S1) ∪ K0ᶜ) := measure_mono hsub
      _ ≤ pi (((S ∩ K0) \ S1) ∪ S1) + pi K0ᶜ := measure_union_le _ _
      _ ≤ pi ((S ∩ K0) \ S1) + pi S1 + pi K0ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((S ∩ K0) \ S1) + pi S1 := by rw [hK0c, add_zero]
  have hcov2 : pi Sᶜ ≤ pi ((K0 \ S) \ S2) + pi S2 := by
    have hsub : Sᶜ ⊆ (((K0 \ S) \ S2) ∪ S2) ∪ K0ᶜ := by
      intro x hx
      by_cases hxK : x ∈ K0
      · by_cases hxS2 : x ∈ S2
        · exact Or.inl (Or.inr hxS2)
        · exact Or.inl (Or.inl ⟨⟨hxK, hx⟩, hxS2⟩)
      · exact Or.inr hxK
    calc pi Sᶜ ≤ pi ((((K0 \ S) \ S2) ∪ S2) ∪ K0ᶜ) := measure_mono hsub
      _ ≤ pi (((K0 \ S) \ S2) ∪ S2) + pi K0ᶜ := measure_union_le _ _
      _ ≤ pi ((K0 \ S) \ S2) + pi S2 + pi K0ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((K0 \ S) \ S2) + pi S2 := by rw [hK0c, add_zero]
  -- the separation, now at `δ/√n`
  have hsep : ∀ u ∈ S1, ∀ v ∈ S2, δ / Real.sqrt n ≤ dist u v := by
    intro u hu v hv
    have hu1 := (hmem1 u).1 hu
    have hv1 := (hmem2 v).1 hv
    have huK : u ∈ K := hK0K hu1.1.2
    have hvK : v ∈ K := hK0K hv1.1.1
    have hu0 : u ∉ StuckPoints K δ := hu1.1.2.2
    have hu24 : 24 * speedyWalk K δ u Sᶜ < 1 := by rw [hPdef] at hu1; exact hu1.2
    have hv24 : 24 * speedyWalk K δ v S < 1 := by rw [hPdef] at hv1; exact hv1.2
    exact (lt_dist_of_speedyWalk_lt_sqrt_global hn hK hconv hδ huK hvK hu0 hcomp hSm
      hu24 hv24).le
  -- the two branches
  have hkey : pi S ≤ 96 * flow P pi S Sᶜ
      ∨ kappa * ENNReal.ofReal (δ / Real.sqrt n) * pi S ≤ 384 * flow P pi S Sᶜ := by
    by_cases hc1 : pi S ≤ 2 * pi ((S ∩ K0) \ S1)
    · left
      calc pi S ≤ 2 * pi ((S ∩ K0) \ S1) := hc1
        _ ≤ 2 * (pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2)) := by gcongr; exact le_self_add
        _ ≤ 2 * (48 * flow P pi S Sᶜ) := by gcongr
        _ = 96 * flow P pi S Sᶜ := by ring
    by_cases hc2 : pi Sᶜ ≤ 2 * pi ((K0 \ S) \ S2)
    · left
      calc pi S ≤ pi Sᶜ := hShalf.trans hSc
        _ ≤ 2 * pi ((K0 \ S) \ S2) := hc2
        _ ≤ 2 * (pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2)) := by gcongr; exact le_add_self
        _ ≤ 2 * (48 * flow P pi S Sᶜ) := by gcongr
        _ = 96 * flow P pi S Sᶜ := by ring
    right
    rw [not_le] at hc1 hc2
    have h1 : pi S < 2 * pi S1 := by
      have hstep : pi S + pi S < pi S + 2 * pi S1 := by
        calc pi S + pi S = 2 * pi S := (two_mul _).symm
          _ ≤ 2 * (pi ((S ∩ K0) \ S1) + pi S1) := by gcongr
          _ = 2 * pi ((S ∩ K0) \ S1) + 2 * pi S1 := by ring
          _ < pi S + 2 * pi S1 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc1
      exact (ENNReal.add_lt_add_iff_left hpitop).1 hstep
    have h2 : pi Sᶜ < 2 * pi S2 := by
      have hstep : pi Sᶜ + pi Sᶜ < pi Sᶜ + 2 * pi S2 := by
        calc pi Sᶜ + pi Sᶜ = 2 * pi Sᶜ := (two_mul _).symm
          _ ≤ 2 * (pi ((K0 \ S) \ S2) + pi S2) := by gcongr
          _ = 2 * pi ((K0 \ S) \ S2) + 2 * pi S2 := by ring
          _ < pi Sᶜ + 2 * pi S2 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc2
      exact (ENNReal.add_lt_add_iff_left (measure_ne_top _ _)).1 hstep
    have h2half : (1:ℝ≥0∞) ≤ 2 * pi Sᶜ := by
      have hhalf : (2:ℝ≥0∞) * (1 / 2) = 1 := by
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      calc (1:ℝ≥0∞) = 2 * (1 / 2) := hhalf.symm
        _ ≤ 2 * pi Sᶜ := by gcongr
    have h3 : (1:ℝ≥0∞) ≤ 4 * pi S2 := by
      calc (1:ℝ≥0∞) ≤ 2 * pi Sᶜ := h2half
        _ ≤ 2 * (2 * pi S2) := by gcongr
        _ = 4 * pi S2 := by ring
    have hprod : pi S ≤ 8 * (pi S1 * pi S2) := by
      calc pi S = pi S * 1 := (mul_one _).symm
        _ ≤ 2 * pi S1 * (4 * pi S2) := mul_le_mul' h1.le h3
        _ = 8 * (pi S1 * pi S2) := by ring
    have hisoS := hiso (δ / Real.sqrt n) hdpos S1 S2 hS1m hS2m hS1K hS2K hsep
    calc kappa * ENNReal.ofReal (δ / Real.sqrt n) * pi S
        ≤ kappa * ENNReal.ofReal (δ / Real.sqrt n) * (8 * (pi S1 * pi S2)) := by gcongr
      _ = 8 * (kappa * ENNReal.ofReal (δ / Real.sqrt n) * pi S1 * pi S2) := by ring
      _ ≤ 8 * pi ((K \ S1) \ S2) := by gcongr
      _ ≤ 8 * (pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2)) := by gcongr
      _ ≤ 8 * (48 * flow P pi S Sᶜ) := by gcongr
      _ = 384 * flow P pi S Sᶜ := by ring
  have hswap : ∀ a b c : ℝ≥0∞, a / c * b = a * b / c := by
    intro a b c
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  rw [conductanceOn_apply, ENNReal.le_div_iff_mul_le (Or.inl hSpos.ne') (Or.inl hpitop)]
  rcases hkey with h | h
  · calc min ((1:ℝ≥0∞) / 96) (kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384) * pi S
        ≤ (1:ℝ≥0∞) / 96 * pi S := by gcongr; exact min_le_left _ _
      _ = 1 * pi S / 96 := hswap _ _ _
      _ = pi S / 96 := by rw [one_mul]
      _ ≤ flow P pi S Sᶜ := by
          rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          exact h.trans_eq (mul_comm _ _)
  · calc min ((1:ℝ≥0∞) / 96) (kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384) * pi S
        ≤ kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384 * pi S := by
          gcongr; exact min_le_right _ _
      _ = kappa * ENNReal.ofReal (δ / Real.sqrt n) * pi S / 384 := hswap _ _ _
      _ ≤ flow P pi S Sᶜ := by
          rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          exact h.trans_eq (mul_comm _ _)

/-! ## 4. The improvement, machine-checked

`Arlib.MarkovChains.conductance_speedyWalk_ge` gives `min(1/16, κ·(δ/(2n))/64)`; this file
gives `min(1/96, κ·(δ/√n)/384)`.  The raw inequality `old ≤ new` is **false**: the first
arguments of the two `min`s are `1/16` and `1/96`, and `1/96 < 1/16`.  That first argument is
a threshold artefact — it is the branch in which the escape probability alone already bounds
the conductance, and it carries no `n` at all.  All of the `n`-dependence lives in the second
argument, and there the comparison is exact: the new bound is the old one multiplied by
`√n/3` (`sqrt_gain_eq`).  Since the mixing time scales as `Φ⁻²`, that is a factor `n/9` off
the step count.

`old_div_six_le_new` is the statement about the *whole* bound that does hold, for every
`n ≥ 1` and with no regime hypothesis: the new bound dominates the old one up to the absolute
constant `6`. -/

/-- Iterated division collapses in `ℝ≥0∞` when the first divisor is finite and non-zero:
`a / b / c = a / (b·c)`.  Needed because `div_div` does not fire on `ℝ≥0∞`. -/
theorem ennreal_div_div (a : ℝ≥0∞) {b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbt : b ≠ ⊤) :
    a / b / c = a / (b * c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
    ← ENNReal.mul_inv (Or.inl hb0) (Or.inl hbt)]

/-- **The gain is exactly `√n/3`, as an equality.**

    (√n/3) · [ κ·(δ/(2n))/64 ]  =  κ·(δ/√n)/384.

Both sides are the isoperimetric branch of the respective conductance bounds
(`Arlib.MarkovChains.conductance_speedyWalk_ge` and `conductance_speedyWalk_sqrt_ge`).  `κ`
is an arbitrary `ℝ≥0∞`, `⊤` included. -/
theorem sqrt_gain_eq (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (kappa : ℝ≥0∞) :
    ENNReal.ofReal (Real.sqrt n / 3) * (kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64)
      = kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384 := by
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hnR
  have hsq : s * s = (n : ℝ) := Real.mul_self_sqrt hnR.le
  have hreal : s / 3 * (δ / (2 * (n : ℝ)) / 64) = δ / s / 384 := by
    rw [← hsq]
    field_simp
    ring
  have key : ENNReal.ofReal (s / 3) * (ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64)
      = ENNReal.ofReal (δ / s) / 384 := by
    rw [show (64 : ℝ≥0∞) = ENNReal.ofReal 64 from by simp,
      show (384 : ℝ≥0∞) = ENNReal.ofReal 384 from by simp,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 64),
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 384),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ s / 3), hreal]
  calc ENNReal.ofReal (s / 3) * (kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64)
      = kappa * (ENNReal.ofReal (s / 3) * (ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64)) := by
        rw [mul_div_assoc]; ring
    _ = kappa * (ENNReal.ofReal (δ / s) / 384) := by rw [key]
    _ = kappa * ENNReal.ofReal (δ / s) / 384 := (mul_div_assoc _ _ _).symm

/-- **The isoperimetric branch strictly improves from dimension `9` on.**  Immediate from
`sqrt_gain_eq`, since `√n/3 ≥ 1` exactly when `n ≥ 9`. -/
theorem old_second_le_new_second (hn : 9 ≤ n) {δ : ℝ} (hδ : 0 < δ) (kappa : ℝ≥0∞) :
    kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64
      ≤ kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384 := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (9:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h3 : (3:ℝ) ≤ Real.sqrt n := by
    nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ (n:ℝ)), Real.sqrt_nonneg ((n:ℝ))]
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.sqrt n / 3) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64
      = 1 * (kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64) := (one_mul _).symm
    _ ≤ ENNReal.ofReal (Real.sqrt n / 3)
          * (kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64) := by gcongr
    _ = kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384 := sqrt_gain_eq hn1 hδ kappa

/-- **The full-bound comparison, unconditional in `n`.**  The new conductance bound dominates
the old one up to the absolute constant `6`:

    min(1/16, κ·(δ/(2n))/64) / 6  ≤  min(1/96, κ·(δ/√n)/384).

Both `min`s are compared argument by argument: `(1/16)/6 = 1/96` exactly, and the second
arguments only need `δ/(2n) ≤ δ/√n`, i.e. `√n ≤ 2n`. -/
theorem old_div_six_le_new (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (kappa : ℝ≥0∞) :
    min (1 / 16) (kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64) / 6
      ≤ min (1 / 96) (kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384) := by
  have hnR : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hle : Real.sqrt n ≤ 2 * (n : ℝ) := by
    have h2n : (0:ℝ) ≤ 2 * (n : ℝ) := by linarith
    have hstep : Real.sqrt n ≤ Real.sqrt ((2 * (n : ℝ)) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq h2n] at hstep
  have hmono : δ / (2 * (n : ℝ)) ≤ δ / Real.sqrt n := by
    rw [div_le_div_iff₀ (by linarith) hs]
    exact mul_le_mul_of_nonneg_left hle hδ.le
  refine le_min ?_ ?_
  · calc min ((1:ℝ≥0∞) / 16) (kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64) / 6
        ≤ (1:ℝ≥0∞) / 16 / 6 := by gcongr; exact min_le_left _ _
      _ = 1 / 96 := by rw [ennreal_div_div _ (by norm_num) (by norm_num)]; norm_num
  · calc min ((1:ℝ≥0∞) / 16) (kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64) / 6
        ≤ kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64 / 6 := by
          gcongr; exact min_le_right _ _
      _ = kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 384 := by
          rw [ennreal_div_div _ (by norm_num) (by norm_num)]; norm_num
      _ ≤ kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384 := by gcongr

/-! ## 5. Non-vacuity (`CLAUDE.md` §11)

The contentious hypothesis is `hcomp`, so that is the one the witness must discharge.  On
`K = B(0,1) ⊆ ℝ²` with `δ = 3`, the step exceeds the diameter of `K`, so `B(x,3) ⊇ K` for
every `x ∈ K` and `ℓ` is **constant**; comparability then holds with equality, for every pair,
at no separation cost.  Everything except `hiso` is discharged.

The same witness settles the relationship with `EllFloor.lean`: there `ℓ ≡ 1/9`, so the
book's good-points body `K_δ = {ℓ ≥ 3/4}` is **empty** and its device says nothing, while
`hcomp` holds outright.  Comparability and the `ℓ ≥ 3/4` floor are therefore *incomparable*
hypotheses — the floor implies comparability pointwise
(`three_quarters_le_ell_comparable`), but a body can satisfy comparability everywhere and the
floor nowhere.  In particular `EllFloor.lean`'s negative — no useful *global constant* floor
exists on a cube from dimension `3` on — does not touch the hypothesis carried here. -/

/-- On `K = B(0,1) ⊆ ℝ²` with step `δ = 3`, the proposal ball always covers `K`. -/
theorem ballThree_cover {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    Metric.ball x (3 : ℝ) ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
      = Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  refine Set.inter_eq_right.mpr fun y hy => ?_
  have hx1 : dist x 0 < 1 := Metric.mem_ball.1 hx
  have hy1 : dist y 0 < 1 := Metric.mem_ball.1 hy
  refine Metric.mem_ball.2 ?_
  calc dist y x ≤ dist y 0 + dist 0 x := dist_triangle _ _ _
    _ < 3 := by rw [dist_comm (0 : EuclideanSpace ℝ (Fin 2)) x]; linarith

/-- **`ℓ ≡ 1/9` on the witness body.**  With `K = B(0,1) ⊆ ℝ²` and `δ = 3`, the accepted part
of every proposal ball is all of `K`, so `ℓ(x) = vol(B(0,1))/vol(B(0,3)) = 3⁻² = 1/9`. -/
theorem ell_ballThree {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    ell (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) 3 x = 1 / 9 := by
  have hv0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hvtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have h3 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 3)
      = 9 * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    rw [Measure.addHaar_ball volume (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num : (0:ℝ) ≤ 3),
      finrank_euclideanSpace_fin]
    norm_num
  have hkey : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
      / (9 * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) = 1 / 9 := by
    have h := ENNReal.mul_div_mul_right (1 : ℝ≥0∞) 9 hv0 hvtop
    rwa [one_mul] at h
  rw [ell_apply, ballThree_cover hx, volume_ball_eq x 3, h3, hkey]

/-- **The book's good-points body is empty on the witness**: `ℓ ≡ 1/9 < 3/4`, so
`{x ∈ K : ℓ(x) ≥ 3/4} = ∅` and the `K_δ` device of `ball_walk.tex:674–678` carries no
information there — while `hcomp` holds (`hcomp_ballThree`).  The two hypotheses are
incomparable. -/
theorem ell_ballThree_lt_three_quarters {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    ell (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) 3 x < (3 : ℝ≥0∞) / 4 := by
  have e1 : (1 : ℝ≥0∞) / 9 = ENNReal.ofReal (1 / 9 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 9)]
    simp
  rw [ell_ballThree hx, e1, ← ofReal_three_quarters]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

/-- **`hcomp` holds on the witness**, at every pair of points and at every separation:
`ℓ` is constant, so `ℓ(x) ≤ (3/2)·ℓ(y)` with room to spare. -/
theorem hcomp_ballThree :
    ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ‖x - y‖ ≤ (3 : ℝ) / Real.sqrt ((2 : ℕ) : ℝ) →
      ell (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) 3 x
        ≤ ENNReal.ofReal (3 / 2)
            * ell (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) 3 y := by
  intro x hx y hy _
  rw [ell_ballThree hx, ell_ballThree hy]
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  calc (1 : ℝ≥0∞) / 9 = 1 * (1 / 9) := (one_mul _).symm
    _ ≤ ENNReal.ofReal (3 / 2) * (1 / 9) := by gcongr

/-- **Non-vacuity witness: every hypothesis of `conductance_speedyWalk_sqrt_ge` except `hiso`
is discharged simultaneously**, on `K = B(0,1) ⊆ ℝ²` with `δ = 3`.  What remains carried is
exactly `hiso`, the isoperimetric inequality, which nothing in this repository proves.

Note in particular that `hcomp` — the hypothesis this file adds to
`Arlib.MarkovChains.conductance_speedyWalk_ge` — is *discharged* here, not assumed: it is
`hcomp_ballThree`. -/
theorem conductance_speedyWalk_sqrt_ballThree {kappa : ℝ≥0∞}
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin 2)),
      MeasurableSet A → MeasurableSet B →
      A ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      B ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      kappa * ENNReal.ofReal d
          * ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) 3 A
          * ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) 3 B
        ≤ ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) 3
            ((Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 \ A) \ B)) :
    min (1 / 96) (kappa * ENNReal.ofReal ((3 : ℝ) / Real.sqrt ((2 : ℕ) : ℝ)) / 384)
      ≤ conductance (speedyWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) 3)
          (ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) 3) :=
  conductance_speedyWalk_sqrt_ge (n := 2) le_rfl measurableSet_ball (convex_ball _ _)
    (Metric.measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne (by norm_num)
    hcomp_ballThree hiso

/-- **The witness in packaged form**, with `κ = 0` so that `hiso` too is discharged and the
bundle is closed: there is a bounded convex body of positive finite volume, and a step, at
which the speedy walk is reversible for a genuine probability measure, `hcomp` holds at the
constant `3/2` for every pair, the good-points body `{ℓ ≥ 3/4}` is empty, and the conclusion
of `conductance_speedyWalk_sqrt_ge` holds.

`κ = 0` makes the isoperimetric branch trivial, so the *content* of this statement is the
joint satisfiability of the geometric hypotheses — above all `hcomp`, which is what
`conductance_speedyWalk_sqrt_ge` adds to `Arlib.MarkovChains.conductance_speedyWalk_ge`. -/
theorem exists_conductance_speedyWalk_sqrt_witness :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2))) (δ : ℝ),
      MeasurableSet K ∧ Convex ℝ K ∧ Bornology.IsBounded K ∧
      volume K ≠ 0 ∧ volume K ≠ ⊤ ∧ 0 < δ ∧
      IsProbabilityMeasure (ellProb K δ) ∧
      IsReversible (speedyWalk K δ) (ellProb K δ) ∧
      (∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ / Real.sqrt ((2 : ℕ) : ℝ) →
        ell K δ x ≤ ENNReal.ofReal (3 / 2) * ell K δ y) ∧
      (∀ x ∈ K, ell K δ x < (3 : ℝ≥0∞) / 4) ∧
      min (1 / 96)
          ((0 : ℝ≥0∞) * ENNReal.ofReal (δ / Real.sqrt ((2 : ℕ) : ℝ)) / 384)
        ≤ conductance (speedyWalk K δ) (ellProb K δ) := by
  refine ⟨Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1, 3, measurableSet_ball,
    convex_ball _ _, Metric.isBounded_ball,
    (Metric.measure_ball_pos volume 0 one_pos).ne', measure_ball_lt_top.ne, by norm_num,
    isProbabilityMeasure_ellProb_of_volume measurableSet_ball
      (Metric.measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne (by norm_num),
    isReversible_speedyWalk_prob measurableSet_ball 3, hcomp_ballThree,
    fun x hx => ell_ballThree_lt_three_quarters hx, ?_⟩
  refine conductance_speedyWalk_sqrt_ballThree (kappa := 0) ?_
  intro d _ A B _ _ _ _ _
  simp

end SpeedyConductanceSqrt

end Arlib.MarkovChains

/-! ### Axiom audit -/

section AxiomAudit
open Arlib.MarkovChains
#print axioms ofReal_three_quarters
#print axioms ell_le_of_three_quarters_le_ell
#print axioms three_quarters_le_ell_comparable
#print axioms lt_dist_of_speedyWalk_lt_sqrt
#print axioms lt_dist_of_speedyWalk_lt_sqrt_global
#print axioms conductance_speedyWalk_sqrt_ge
#print axioms ennreal_div_div
#print axioms sqrt_gain_eq
#print axioms old_second_le_new_second
#print axioms old_div_six_le_new
#print axioms ballThree_cover
#print axioms ell_ballThree
#print axioms ell_ballThree_lt_three_quarters
#print axioms hcomp_ballThree
#print axioms conductance_speedyWalk_sqrt_ballThree
#print axioms exists_conductance_speedyWalk_sqrt_witness
end AxiomAudit
