/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.MarkovChains.Continuous.BallWalk
import Arlib.MarkovChains.Continuous.HitAndRunConductance

/-!
# The step-size function `s(x)` of the hit-and-run conductance proof

This file gives the step-size function of §10.6 of

> Y. T. Lee, *Optimization* (book draft), §10.6 "Hit-and-run", `har_dikin.tex`

in the book's own shape — as a supremum of radii at which the **local conductance**
`Arlib.MarkovChains.ell` of `Arlib/MarkovChains/Continuous/BallWalk.lean` is at least a fixed
threshold `γ` — and connects it to the machinery the repository already has.

The book writes

`s(x) = sup {t : vol((x + tBⁿ) ∩ K) / vol(tBⁿ) ≥ γ}`,  `γ ∈ (0,1]`,

and the quotient inside the braces is **literally** `ell K t x`.  So `Arlib.MarkovChains.stepSize`
below is the book's `s`, with no re-derivation of the ratio.

## The one thing this file actually proves: the bridge

**Every mathematical statement about `s` in §10.6 is already proved in this repository**, under
the name `Arlib.stepRadius` of `Arlib/Convexity/StepLength.lean` (which formalises the same
function from Lovász–Vempala, *Hit-and-Run from a Corner*, where it is written `s_α`).  What was
missing is that the two notions had never been *identified*: `ell` is built from **open** balls
and lives in `ℝ≥0∞`, while `Arlib.stepRadiusSet` is built from **closed** balls and an
`ℝ≥0∞`-valued product inequality, and no lemma related them.  `Arlib.ballFraction` occurs
nowhere outside `StepLength.lean`.

That bridge is

* `Arlib.MarkovChains.stepRadiusSet_eq_insert_zero` — the set identity, and
* `Arlib.MarkovChains.stepSize_eq_stepRadius` — `s = s_α`, for every `x`, with no
  membership, boundedness or finiteness hypothesis.

The sphere `∂B(x,t)` is Lebesgue-null for `t ≠ 0`, so open and closed balls have the same volume
and the same volume of intersection with `K`; the only genuine difference is the radius `t = 0`,
which `Arlib.stepRadiusSet` contains by fiat (both sides of its inequality vanish) and the
`ell`-set never contains (`ell K 0 x = 0/0 = 0 < γ`).  Adjoining that single point does not move
the supremum, because every other admissible radius is positive.

Everything after the bridge is a transport, and is stated here only so that the book's five
results are readable in the book's own vocabulary.

## Main definitions

* `Arlib.MarkovChains.stepSize` — the book's `s(x)`, in terms of `ell`.  This is the only
  definition introduced, and `stepSize_eq_stepRadius` is its proving lemma.

## Main results

* `Arlib.MarkovChains.stepSize_eq_stepRadius` — the bridge.
* `Arlib.MarkovChains.concaveOn_stepSize` — `s` is concave on a convex body (book, ~line 285;
  Lemma 3.1 of Lovász–Vempala).  Transported from `Arlib.stepRadius_concaveOn`.
* `Arlib.MarkovChains.stepOut_le` — the book's `lem:step_out_prob`, Corollary 4.6 of
  Kannan–Lovász–Simonovits 1997.  Transported from
  `Arlib.lintegral_volume_closedBall_sdiff_le_sqrt`.
* `Arlib.MarkovChains.expectation_stepSize_ge` — the book's `lem:step-size` part 1,
  `E_K(s) ≥ (1−γ)/(10√n)`.  Transported from `Arlib.lintegral_stepRadius_ge`.
* `Arlib.MarkovChains.medianStep_ge_stepSize_div` — the book's `lem:step-size` part 2,
  `F(x) ≥ s(x)/32` at `γ ≥ 63/64`.  Transported from `Arlib.stepRadius_div_le_medianStep`.
* `Arlib.MarkovChains.chord_stepSize_le` — the §10.6 chord estimate
  `s(x) ≤ 16·√n·d_K(u,v)·D`, which is what makes `h(x) = s(x)/(48√n·D)` admissible for the
  weighted isoperimetric inequality.  Transported from
  `Arlib.MarkovChains.stepRadius_le_of_chord`.

## Three honest deviations from the book

1. **The constant in `stepOut_le` and `expectation_stepSize_ge` is `10`, not `1`.**  The book
   states `lem:step_out_prob` with `t√n/(2r)` and hence `E_K(s) ≥ (1−γ)/√n`.  What this
   repository proves is `10·t√n/(2r)` and hence `(1−γ)/(10√n)`.  The factor is a documented
   loss in the majorant used by the KLS97 route of `Arlib/Convexity/KLS97Sharp.lean` (an
   exponential envelope in place of the Gaussian), **not** evidence of an error in KLS97.  The
   order in `n` — all the conductance bound consumes — is the book's.

2. **`medianStep_ge_stepSize_div` needs `hmove`.**  The repository's `F` is defined against the
   genuine hit-and-run kernel `Arlib.MarkovChains.hitAndRun`, which has a lazy atom at `x`
   absorbing the directions along which the chord through `x` is null or infinite.  That atom
   sits at distance `0`, so without `hitAndRunProposal K x univ = 1` a walk that stays put with
   probability more than `1/8` has `F(x) = 0` and the lemma is false.  The book never mentions
   the issue because it silently works with an interior point of a bounded body;
   `Arlib.hitAndRunProposal_univ_eq_one_of_mem_interior` discharges the hypothesis in exactly
   that situation.

3. **`n ≥ 6` is carried but is not needed.**  The book's proof of `lem:step-size` part 2 passes
   through `p ≤ 1 − γ + 2⁻ⁿ ≤ 1/32`, and the final step needs `2⁻ⁿ ≤ 1/64`, i.e. `n ≥ 6` — which
   the book states ("where we used that n ≥ 6") but which is an artefact of weakening the cone
   volume `p·(vol(sB) − vol((s/2)B))` to `p·vol(sB) − vol((s/2)B)`.  Keeping the factor gives
   `p ≤ (1−γ)/(1 − 2⁻ⁿ) ≤ 2(1−γ) ≤ 1/32` in **every** dimension `n ≥ 1`, which is what
   `Arlib.toSphere_badDir_le` proves and what `Arlib.stepRadius_le_medianStep` uses.  The
   hypothesis `6 ≤ n` is kept in the statement below to match the book verbatim; it is used only
   to supply `n ≠ 0`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Arlib.MarkovChains

variable {n : ℕ}

/-! ### The definition -/

/-- **The step-size function `s(x)` of Lee, *Optimization*, §10.6** (`har_dikin.tex`, the
display just before "the step-size function `s(x)` is concave"):

`s(x) = sup {t : vol((x + tBⁿ) ∩ K) / vol(tBⁿ) ≥ γ}`

for a fixed threshold `γ ∈ (0,1]`.  The quotient is the local conductance
`Arlib.MarkovChains.ell K t x` of `BallWalk.lean`, so the definition below is the book's,
verbatim, with `ell` in place of the book's `g(x,t)`; no second notion of "fraction of the ball
inside `K`" is introduced.

**Radii `t ≤ 0` are automatically excluded** for `γ > 0`: the ball is then empty, so
`ell K t x = 0/0 = 0 < γ`.  The supremum is a `Real.sSup`, hence takes the value `0` on an empty
or unbounded set of admissible radii — which is the value the book intends at a corner of `K`
(where no positive `t` is admissible) and which agrees with `Arlib.stepRadius`.  That agreement
is `Arlib.MarkovChains.stepSize_eq_stepRadius`, proved below, and it is what entitles this
definition to its name: every property the book asserts of `s` is transported through it. -/
noncomputable def stepSize (K : Set (EuclideanSpace ℝ (Fin n))) (γ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {t : ℝ | ENNReal.ofReal γ ≤ ell K t x}

/-- Unfolding lemma for `Arlib.MarkovChains.stepSize`. -/
theorem stepSize_apply (K : Set (EuclideanSpace ℝ (Fin n))) (γ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    stepSize K γ x = sSup {t : ℝ | ENNReal.ofReal γ ≤ ell K t x} := rfl

/-! ### The bridge to `Arlib.stepRadius`

`ell` is built from **open** balls, `Arlib.stepRadiusSet` from **closed** ones.  The two agree
because the sphere is Lebesgue-null at every nonzero radius. -/

/-- Open and closed balls of nonzero radius have the same volume: they differ by a sphere. -/
private lemma volume_ball_eq_volume_closedBall (x : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : t ≠ 0) : volume (Metric.ball x t) = volume (Metric.closedBall x t) := by
  refine le_antisymm (measure_mono Metric.ball_subset_closedBall) ?_
  calc volume (Metric.closedBall x t)
      = volume (Metric.ball x t ∪ Metric.sphere x t) := by rw [Metric.ball_union_sphere]
    _ ≤ volume (Metric.ball x t) + volume (Metric.sphere x t) := measure_union_le _ _
    _ = volume (Metric.ball x t) := by
        rw [Measure.addHaar_sphere_of_ne_zero volume x ht, add_zero]

/-- The same, intersected with an arbitrary set `K` — and with the two argument orders the two
files happen to use. -/
private lemma volume_ball_inter_eq (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : t ≠ 0) :
    volume (Metric.ball x t ∩ K) = volume (K ∩ Metric.closedBall x t) := by
  refine le_antisymm (measure_mono fun y hy => ⟨hy.2, Metric.ball_subset_closedBall hy.1⟩) ?_
  have hsub : K ∩ Metric.closedBall x t ⊆ (Metric.ball x t ∩ K) ∪ Metric.sphere x t := by
    rintro y ⟨hyK, hy⟩
    rcases lt_or_eq_of_le (Metric.mem_closedBall.1 hy) with h | h
    · exact Or.inl ⟨Metric.mem_ball.2 h, hyK⟩
    · exact Or.inr (Metric.mem_sphere.2 h)
  calc volume (K ∩ Metric.closedBall x t)
      ≤ volume ((Metric.ball x t ∩ K) ∪ Metric.sphere x t) := measure_mono hsub
    _ ≤ volume (Metric.ball x t ∩ K) + volume (Metric.sphere x t) := measure_union_le _ _
    _ = volume (Metric.ball x t ∩ K) := by
        rw [Measure.addHaar_sphere_of_ne_zero volume x ht, add_zero]

section Bridge

variable [NeZero n]

/-- **The set identity.**  For a threshold `γ > 0`, the book's set of admissible radii
`{t : ell K t x ≥ γ}` is exactly the repository's `Arlib.stepRadiusSet K γ x` with the radius
`0` removed.

`0` belongs to `stepRadiusSet` by construction (there both sides of the defining inequality
vanish, which is what keeps that set nonempty at a corner of `K`), and never to the `ell`-set
(`ell K 0 x = 0 / 0 = 0 < γ`).  At every other radius the two conditions are the same
inequality: negative radii are excluded on both sides, and at `t > 0` the ball has positive
finite volume, so `γ ≤ vol(B ∩ K)/vol(B)` and `γ · vol(B) ≤ vol(B ∩ K)` are equivalent. -/
theorem stepRadiusSet_eq_insert_zero (K : Set (EuclideanSpace ℝ (Fin n))) {γ : ℝ} (hγ : 0 < γ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Arlib.stepRadiusSet K γ x = insert 0 {t : ℝ | ENNReal.ofReal γ ≤ ell K t x} := by
  have hn : n ≠ 0 := NeZero.ne n
  have hγ0 : ENNReal.ofReal γ ≠ 0 := by simpa using hγ
  -- at a positive radius the two conditions agree
  have hpos : ∀ t : ℝ, 0 < t →
      (ENNReal.ofReal γ * volume (Metric.closedBall x t) ≤ volume (K ∩ Metric.closedBall x t)
        ↔ ENNReal.ofReal γ ≤ ell K t x) := by
    intro t ht
    have hb0 : volume (Metric.ball x t) ≠ 0 := (Metric.measure_ball_pos volume x ht).ne'
    have hbt : volume (Metric.ball x t) ≠ ⊤ := measure_ball_lt_top.ne
    rw [ell_apply, ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbt),
      volume_ball_eq_volume_closedBall x ht.ne', volume_ball_inter_eq K x ht.ne']
  ext t
  constructor
  · rintro ⟨ht0, ht⟩
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · exact Or.inl h0.symm
    · exact Or.inr ((hpos t h0).1 ht)
  · rintro (rfl | ht)
    · exact Arlib.zero_mem_stepRadiusSet hn K γ x
    · -- a member of the `ell`-set is automatically positive
      have h0 : 0 < t := by
        rcases le_or_gt t 0 with h | h
        · exfalso
          rw [Set.mem_setOf_eq, ell_apply, Metric.ball_eq_empty.2 h] at ht
          simp only [Set.empty_inter, measure_empty, ENNReal.zero_div] at ht
          exact hγ0 (le_antisymm ht bot_le)
        · exact h
      exact ⟨h0.le, (hpos t h0).2 ht⟩

/-- **The bridge.**  The book's step-size function is the repository's step radius:

`Arlib.MarkovChains.stepSize K γ x = Arlib.stepRadius K γ x`.

This holds at **every** point `x`, with no hypothesis that `x ∈ K`, that `K` be convex,
measurable or of finite volume: `stepRadiusSet_eq_insert_zero` differs from the `ell`-set by the
single radius `0`, and adjoining `0` to a set of nonnegative reals changes neither an empty
supremum (`0` either way), nor an unbounded one (`Real.sSup` is `0` either way), nor a genuine
one (every other member is positive, so `0` is not the maximum).

Because the identity is unconditional, it transports through `ConcaveOn`, through `∫⁻` and
through every inequality below by `funext`/`simp_rw` alone, with no side conditions. -/
theorem stepSize_eq_stepRadius (K : Set (EuclideanSpace ℝ (Fin n))) {γ : ℝ} (hγ : 0 < γ)
    (x : EuclideanSpace ℝ (Fin n)) : stepSize K γ x = Arlib.stepRadius K γ x := by
  set S : Set ℝ := {t : ℝ | ENNReal.ofReal γ ≤ ell K t x} with hS
  have hγ0 : ENNReal.ofReal γ ≠ 0 := by simpa using hγ
  have hSpos : ∀ t ∈ S, 0 < t := by
    intro t ht
    rcases le_or_gt t 0 with h | h
    · exfalso
      rw [hS, Set.mem_setOf_eq, ell_apply, Metric.ball_eq_empty.2 h] at ht
      simp only [Set.empty_inter, measure_empty, ENNReal.zero_div] at ht
      exact hγ0 (le_antisymm ht bot_le)
    · exact h
  rw [stepSize_apply, Arlib.stepRadius, stepRadiusSet_eq_insert_zero K hγ x, ← hS]
  rcases S.eq_empty_or_nonempty with he | hne
  · simp [he]
  · by_cases hbdd : BddAbove S
    · rw [csSup_insert hbdd hne, sup_eq_right.2]
      obtain ⟨t, htS⟩ := hne
      exact (hSpos t htS).le.trans (le_csSup hbdd htS)
    · have hbdd' : ¬ BddAbove (insert (0 : ℝ) S) :=
        fun h => hbdd (h.mono (Set.subset_insert _ _))
      rw [Real.sSup_of_not_bddAbove hbdd, Real.sSup_of_not_bddAbove hbdd']

end Bridge

/-! ### The book's five results, in the book's vocabulary

Each is the corresponding theorem of the Lovász–Vempala stack, rewritten along
`Arlib.MarkovChains.stepSize_eq_stepRadius`.  **No mathematics is re-proved here**; the point is
that `s` as the book defines it — a supremum of radii at which `ell` is at least `γ` — provably
enjoys all of them. -/

section BookResults

variable {K : Set (EuclideanSpace ℝ (Fin n))} {γ : ℝ}

/-- **`s` is concave over any convex body** (Lee, *Optimization* §10.6, the lemma immediately
after the definition of `s`; Lemma 3.1 of Lovász–Vempala).

The book's proof is exactly the one behind `Arlib.stepRadius_concaveOn`: with
`Aᵢ = K ∩ (xᵢ + rᵢBⁿ)` and `A = (A₁+A₂)/2 ⊆ K ∩ (x + ((r₁+r₂)/2)Bⁿ)`, the sharp
Brunn–Minkowski inequality gives `vol(A)^{1/n} ≥ γ^{1/n}·vol(((r₁+r₂)/2)Bⁿ)^{1/n}`.  In the
repository that is `Arlib.mem_stepRadiusSet_combo`, proved with a general weight rather than at
the midpoint, so the conclusion is full `ConcaveOn` and not only midpoint concavity.

`hKfin` is what makes the supremum defining `s` finite (`Arlib.bddAbove_stepRadiusSet`); it is
automatic for a body. -/
theorem concaveOn_stepSize (hn : n ≠ 0) (hKc : Convex ℝ K) (hKm : MeasurableSet K)
    (hKfin : volume K ≠ ⊤) (hγ : 0 < γ) : ConcaveOn ℝ K (stepSize K γ) := by
  haveI : NeZero n := ⟨hn⟩
  have h : stepSize K γ = Arlib.stepRadius K γ :=
    funext fun x => stepSize_eq_stepRadius K hγ x
  rw [h]
  exact Arlib.stepRadius_concaveOn hn hKc hKm hKfin hγ

/-- **`lem:step_out_prob`** of Lee, *Optimization* §10.6 = **Corollary 4.6 of
Kannan–Lovász–Simonovits 1997**: if `K` contains a ball of radius `r`, then for every `t > 0`

`∫_K vol((x + tBⁿ) \ K) dx ≤ (C·t√n / 2r)·vol(K)·vol(tBⁿ)`.

The book quotes this with `C = 1`.  What is *proved* in this repository — in
`Arlib/Convexity/KLS97Sharp.lean`, at the sharp order `√n` — is `C = 10`, and that is what is
restated here.  The factor is a loss in the majorant used by that file's route (an exponential
envelope `e^{2−λh}` in place of the Gaussian, plus `(1+x)ⁿ − 1 ≤ nx·e^{nx}`), **not** evidence
against KLS97's `C = 1`; see that file's docstring.  Only the order in `n` is consumed
downstream.

This statement is unrelated to `stepSize` and is included because the book's `lem:step-size`
part 1 is derived from it; it is a verbatim restatement of
`Arlib.lintegral_volume_closedBall_sdiff_le_sqrt`. -/
theorem stepOut_le (hn : n ≠ 0) (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    {z : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hball : Metric.closedBall z r ⊆ K) (hr : 0 < r)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in K, volume (Metric.closedBall x t \ K)
      ≤ ENNReal.ofReal (10 * (t * Real.sqrt n) / (2 * r)) * volume K
          * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) :=
  Arlib.lintegral_volume_closedBall_sdiff_le_sqrt hn hKc hKcl hKfin hball hr ht

/-- **`lem:step-size` part 1** of Lee, *Optimization* §10.6: for a body containing a unit ball,

`E_K(s(x)) ≥ (1 − γ)/(C√n)`.

The book's proof is the one behind `Arlib.lintegral_stepRadius_ge`: `stepOut_le` gives
`∫_K g(x,t) dx ≥ (1 − C·t√n/2)·vol(K)`, splitting the integral at the threshold `γ` gives
`vol{x ∈ K : g(x,t) ≥ γ} ≥ (1 − C·t√n/(2(1−γ)))·vol(K)` (that is
`Arlib.volume_goodSet_ge`), and the layer-cake formula
`E_K(s) = (1/vol K)·∫₀^∞ vol{x ∈ K : g(x,t) ≥ γ} dt` — Mathlib's
`MeasureTheory.lintegral_eq_lintegral_meas_le`, whose measurability side condition is supplied
by concavity of `s` via `Arlib.aemeasurable_stepRadius` — integrates it.

**The constant is `C = 10`**, inherited from `stepOut_le`; the book writes `C = 1`, i.e.
`(1−γ)/√n`.  See `stepOut_le` and the module docstring.

The integral is the lower Lebesgue integral of `ENNReal.ofReal ∘ s`, the honest reading of
`∫_K s(x) dx` for a nonnegative function, so no integrability hypothesis is needed. -/
theorem expectation_stepSize_ge (hn : n ≠ 0) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKm : MeasurableSet K) (hKfin : volume K ≠ ⊤) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K) :
    ENNReal.ofReal ((1 - γ) / (10 * Real.sqrt n)) * volume K
      ≤ ∫⁻ x in K, ENNReal.ofReal (stepSize K γ x) := by
  haveI : NeZero n := ⟨hn⟩
  simp_rw [stepSize_eq_stepRadius K hγ0]
  exact Arlib.lintegral_stepRadius_ge hn hKc hKcl hKm hKfin hγ0 hγ1 hball

/-- **`lem:step-size` part 2** of Lee, *Optimization* §10.6: for `γ ≥ 63/64`,

`F(x) ≥ s(x)/32`,

with `F = Arlib.MarkovChains.medianStep` the median hit-and-run step length,
`P(‖x − y‖ ≤ F(x)) = 1/8`.

**`6 ≤ n` is carried because the book carries it** ("where we used that `n ≥ 6`"), and it is the
*only* use it is put to here: it supplies `n ≠ 0`.  The book needs it because its displayed
chain weakens the volume of the cone swept out by the bad directions between radii `s/2` and
`s`, `p·(vol(sB) − vol((s/2)B))`, to `p·vol(sB) − vol((s/2)B)`, and then needs `2⁻ⁿ ≤ 1/64` to
close `p ≤ 1 − γ + 2⁻ⁿ ≤ 1/32`.  Keeping the factor gives `p ≤ (1−γ)/(1 − 2⁻ⁿ) ≤ 2(1−γ) ≤ 1/32`
in every dimension `n ≥ 1`; that is `Arlib.toSphere_badDir_le`, and it is why
`Arlib.stepRadius_div_le_medianStep` — which this theorem is a restatement of — has **no**
dimension hypothesis beyond `n ≠ 0`.  So the book's printed proof has a gap for `n ≤ 5` while
the statement itself is true throughout.

**`hmove` is not removable.**  `Arlib.MarkovChains.hitAndRun` has a lazy atom at `x` carrying the
mass of the directions along which the chord through `x` is null or infinite; that atom sits at
distance `0`, so a walk staying put with probability more than `1/8` has `F(x) = 0` and the
inequality fails.  The book works silently with an interior point of a bounded body, for which
`Arlib.hitAndRunProposal_univ_eq_one_of_mem_interior` discharges the hypothesis. -/
theorem medianStep_ge_stepSize_div (hn6 : 6 ≤ n) (hKc : Convex ℝ K) (hKm : MeasurableSet K)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K) (hγ : 63 / 64 ≤ γ) (hγ1 : γ ≤ 1)
    (hmove : hitAndRunProposal K x Set.univ = 1) :
    stepSize K γ x / 32 ≤ medianStep K x := by
  have hn : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn⟩
  rw [stepSize_eq_stepRadius K (by linarith : (0:ℝ) < γ)]
  exact Arlib.stepRadius_div_le_medianStep hn hKc hKm hx hγ hγ1 hmove

/-- **The chord estimate of §10.6**, the last step of the hit-and-run conductance proof:

`s(x) ≤ 16·√n·d_K(u,v)·D`

for `x` on the chord through `u` and `v`, with `d_K` the cross-ratio distance
(`Arlib.crossRatioDist`) and `D = diam K`.  Dividing by `48√n·D` turns it into
`h(x) ≤ d_K(u,v)/3`, the hypothesis of the weighted isoperimetric inequality
`thm:har_weighted_iso` for the book's weight `h(x) = s(x)/(48√n·D)`.

The chain is the book's: concavity of `s` (`concaveOn_stepSize`, applied as
`Arlib.theta_mul_stepRadius_le` with `θ = |u−p|/|x−p|`), then `s(u) ≤ 32·F(u)`
(`medianStep_ge_stepSize_div`), then the separation hypotheses `hFu`, `hFv`.  Every relation in
it is `≤`.  The book writes only "WLOG `x ∈ [u,q]`"; the mirror case is proved too, which is why
both `hFu` and `hFv` appear.  This is `Arlib.MarkovChains.stepRadius_le_of_chord` restated. -/
theorem chord_stepSize_le (hn : n ≠ 0) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKm : MeasurableSet K) (hKb : Bornology.IsBounded K) (hKfin : volume K ≠ ⊤)
    (hγ : 63 / 64 ≤ γ) (hγ1 : γ ≤ 1)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ interior K) (hv : v ∈ interior K) (huv : u ≠ v)
    (hmu : hitAndRunProposal K u Set.univ = 1) (hmv : hitAndRunProposal K v Set.univ = 1)
    (hFu : medianStep K u ≤ Real.sqrt n / 2 * dist u v)
    (hFv : medianStep K v ≤ Real.sqrt n / 2 * dist u v)
    {x : EuclideanSpace ℝ (Fin n)} (hxK : x ∈ K) {t : ℝ}
    (hxt : x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) :
    stepSize K γ x ≤ 16 * Real.sqrt n * Arlib.crossRatioDist K u v * Metric.diam K := by
  haveI : NeZero n := ⟨hn⟩
  rw [stepSize_eq_stepRadius K (by linarith : (0:ℝ) < γ)]
  exact stepRadius_le_of_chord hn hKc hKcl hKm hKb hKfin hγ hγ1 hu hv huv hmu hmv hFu hFv hxK hxt

/-- **Non-vacuity** (`CLAUDE.md` §11).  On the unit ball seen from its centre every hypothesis of
`medianStep_ge_stepSize_div` holds, the step size is *strictly positive*, and so is `F` — so the
conclusion is a genuine lower bound on `F` and not the vacuous `0 ≤ 32·F`.  Transported from
`Arlib.exists_stepRadius_le_medianStep_witness`. -/
theorem exists_stepSize_pos_witness (hn : n ≠ 0) (hγ : 63 / 64 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)),
      Convex ℝ K ∧ MeasurableSet K ∧ x ∈ K ∧
        hitAndRunProposal K x Set.univ = 1 ∧
        0 < stepSize K γ x ∧
        stepSize K γ x / 32 ≤ medianStep K x ∧ 0 < medianStep K x := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨K, x, hKc, hKm, hx, hmove, hpos, hle, hF⟩ :=
    Arlib.exists_stepRadius_le_medianStep_witness hn hγ hγ1
  refine ⟨K, x, hKc, hKm, hx, hmove, ?_, ?_, hF⟩
  · rwa [stepSize_eq_stepRadius K (by linarith : (0:ℝ) < γ)]
  · rw [stepSize_eq_stepRadius K (by linarith : (0:ℝ) < γ)]; linarith

end BookResults

/-! ### Axiom check (`CLAUDE.md` §4) -/

section AxiomCheck

#print axioms Arlib.MarkovChains.stepSize_apply
#print axioms Arlib.MarkovChains.stepRadiusSet_eq_insert_zero
#print axioms Arlib.MarkovChains.stepSize_eq_stepRadius
#print axioms Arlib.MarkovChains.concaveOn_stepSize
#print axioms Arlib.MarkovChains.stepOut_le
#print axioms Arlib.MarkovChains.expectation_stepSize_ge
#print axioms Arlib.MarkovChains.medianStep_ge_stepSize_div
#print axioms Arlib.MarkovChains.chord_stepSize_le
#print axioms Arlib.MarkovChains.exists_stepSize_pos_witness

end AxiomCheck

end Arlib.MarkovChains
