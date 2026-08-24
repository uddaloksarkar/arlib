/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.UnitBallMixing

/-!
# A genuinely non-stationary warm start for the ball walk on the unit ball

## The defect this file closes

`Arlib.MarkovChains.exists_unconditional_mixing_unitBall`
(`Arlib/MarkovChains/Continuous/UnitBallMixing.lean`) is the non-vacuity witness for the
whole mixing stack: it is supposed to show that the isoperimetric inequality, the
local-conductance floor, the Cheeger inequality, the `L²` decay and the total-variation
bound are *jointly satisfiable* by a real convex body.  It discharges the warm-start
hypothesis with `isWarm_one_self`, i.e. it takes the starting law `mu0` to be the walk's
own stationary measure `Arlib.uniformOn volume (Metric.ball 0 1)`, at warmness constant
`M = 1`.

That witness is inhabited and axiom-clean, and it is still not good enough.  A chain
started *at* stationarity is already mixed: `MixesWithin` then holds at every time `t` for
reasons that have nothing to do with conductance, isoperimetry or the step count.  The
witness therefore collapses precisely the quantity the theorem is about, and `#print
axioms` is blind to the collapse because nothing was ever assumed — this is the failure
mode where an extremal "ideal" instance satisfies almost anything (`CLAUDE.md` §11, the
non-vacuity bullet).

This file supplies a start that is **not** the stationary measure: the uniform
distribution on the *half*-ball `Metric.ball 0 (1/2)`, which is `2ⁿ`-warm with respect to
uniform on `Metric.ball 0 1` and provably different from it.  Feeding it to
`mixesWithin_lazy_ballWalk_unitBall_uncond` makes the witness exercise the mixing bound
instead of dodging it.

## Why `2ⁿ`, exactly

For measurable `S`, `uniformOn volume B_r S = vol (S ∩ B_r) / vol B_r`.  Since
`B_{1/2} ⊆ B_1` we have `vol (S ∩ B_{1/2}) ≤ vol (S ∩ B_1)`, so warmness reduces to the
volume ratio, and the ratio is exactly `2ⁿ` by the scaling of Haar measure under a
homothety (`MeasureTheory.Measure.addHaar_ball_of_pos`).  That exact ratio is isolated as
`volume_ball_one_eq`, the crux of the file; everything else is `ℝ≥0∞` bookkeeping around
it.

## Main results

* `Arlib.MarkovChains.volume_ball_one_eq` — the crux: `vol B_1 = 2ⁿ · vol B_{1/2}` in
  `EuclideanSpace ℝ (Fin n)`, exactly, with no hypothesis on `n`.
* `Arlib.MarkovChains.isWarm_uniformOn_ball_half` — the half-ball uniform law is a
  `2ⁿ`-warm start for the unit-ball uniform law.
* `Arlib.MarkovChains.uniformOn_ball_half_ne_uniformOn_ball` — **the point of the
  exercise**: that start is *not* the stationary measure.  Without this the new witness
  would be no better than the one it replaces.
* `Arlib.MarkovChains.one_lt_two_pow_ennreal` — the warmness constant is genuinely `> 1`
  in every dimension `n ≥ 1`, so the start is not `1`-warm for free.
* `Arlib.MarkovChains.exists_unconditional_mixing_unitBall_nonstationary` — the repaired
  non-vacuity witness, carrying the `≠`-to-stationary conjunct inside the `∃`.
-/

open MeasureTheory
open scoped ENNReal

namespace Arlib.MarkovChains

section HalfBall

variable {n : ℕ}

/-! ## The half-ball and its guards -/

/-- The first guard on the half-ball: it is not Lebesgue-null.  The analogue of
`volume_unitBall_ne_zero` at radius `1/2`. -/
theorem volume_ballHalf_ne_zero :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≠ 0 :=
  (Metric.measure_ball_pos volume 0 (by norm_num)).ne'

/-- The second guard on the half-ball: it has finite volume.  The analogue of
`volume_unitBall_ne_top` at radius `1/2`. -/
theorem volume_ballHalf_ne_top :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≠ ⊤ :=
  measure_ball_lt_top.ne

/-! ## The crux: the exact volume ratio -/

/-- **The crux.**  In `EuclideanSpace ℝ (Fin n)` the unit ball has *exactly* `2ⁿ` times
the volume of the ball of radius `1/2`:

    vol (B 0 1) = 2 ^ n * vol (B 0 (1/2)).

This is the scaling of Haar measure under the homothety `x ↦ x/2`
(`MeasureTheory.Measure.addHaar_ball_of_pos`) together with
`finrank_euclideanSpace_fin : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n`.  No hypothesis on
`n` is needed: at `n = 0` the space is a point, both balls are `{0}`, and `2 ^ 0 = 1`.

Everything else in this file is `ℝ≥0∞` bookkeeping around this identity. -/
theorem volume_ball_one_eq (n : ℕ) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      = 2 ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) := by
  have hhalf : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
      = ENNReal.ofReal (((1 : ℝ) / 2) ^ n)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    have := Measure.addHaar_ball_of_pos
      (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 (r := (1 : ℝ) / 2) (by norm_num)
    rwa [finrank_euclideanSpace_fin] at this
  have hcoe : ENNReal.ofReal (((1 : ℝ) / 2) ^ n) = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
    rw [div_pow, one_pow, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, one_div]
  rw [hhalf, hcoe, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-! ## The warmness constant is not `1` -/

/-- **The warmness constant is genuinely bigger than `1`.**  `1 < 2ⁿ` in `ℝ≥0∞` for every
`n ≥ 1`.

This is stated for the reader of `isWarm_uniformOn_ball_half`.  `Arlib.IsWarm.one_le` says
`1` is the smallest warmness constant available between probability measures, so `M = 1`
— the constant the old `isWarm_one_self` witness used — is the degenerate end of the
scale.  The half-ball start is warm at a strictly larger constant. -/
theorem one_lt_two_pow_ennreal (n : ℕ) [NeZero n] : 1 < (2 : ℝ≥0∞) ^ n :=
  one_lt_pow' (by norm_num) (NeZero.ne n)

/-! ## The warm start -/

/-- **The uniform law on the half-ball is a `2ⁿ`-warm start for the unit ball.**

For measurable `S`,

    uniformOn volume B_{1/2} S = vol (S ∩ B_{1/2}) / vol B_{1/2},
    uniformOn volume B_1     S = vol (S ∩ B_1)     / vol B_1,

and `vol B_1 = 2ⁿ · vol B_{1/2}` exactly (`volume_ball_one_eq`).  Multiplying the second
display by `2ⁿ` therefore cancels the `2ⁿ` in its denominator and leaves
`vol (S ∩ B_1) / vol B_{1/2}`, which dominates the first display because
`B_{1/2} ⊆ B_1`.  So the constant `2ⁿ` is not merely sufficient: it is exactly the volume
ratio, and the only slack in the inequality is the set inclusion.

This is the hypothesis `mixesWithin_lazy_ballWalk_unitBall_uncond` leaves open, discharged
at a start that is *not* the stationary measure — see
`uniformOn_ball_half_ne_uniformOn_ball`. -/
theorem isWarm_uniformOn_ball_half (n : ℕ) [NeZero n] :
    Arlib.IsWarm (2 ^ n)
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
  intro S hS
  -- Multiplying by `2ⁿ` cancels the `2ⁿ` that `volume_ball_one_eq` puts in the
  -- denominator, leaving the common denominator `vol B_{1/2}`.
  have key : ∀ a : ℝ≥0∞,
      (2 : ℝ≥0∞) ^ n * (a / (2 ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))))
        = a / volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) := by
    intro a
    rw [div_eq_mul_inv, ← mul_assoc, ← div_eq_mul_inv,
      ENNReal.mul_div_mul_left _ _ (by simp : (2 : ℝ≥0∞) ^ n ≠ 0)
        (by simp : (2 : ℝ≥0∞) ^ n ≠ ⊤)]
  rw [Arlib.uniformOn_apply volume measurableSet_ball hS,
    Arlib.uniformOn_apply volume measurableSet_ball hS, volume_ball_one_eq n, key]
  exact ENNReal.div_le_div_right
    (measure_mono (Set.inter_subset_inter_right _
      (Metric.ball_subset_ball (by norm_num)))) _

/-! ## The point of the exercise: the start is not stationary -/

/-- **The half-ball start is genuinely not the stationary measure.**

Without this the new witness would be no better than the `isWarm_one_self` one it
replaces: a chain started at stationarity satisfies `MixesWithin` at every time for
reasons unrelated to conductance, so a "non-vacuity witness" built from it certifies
nothing about mixing.

The separating set is the half-ball itself.  Under `uniformOn volume B_{1/2}` it has mass
`1` (`Arlib.uniformOn_self`, whose guards are `volume_ballHalf_ne_zero` and
`volume_ballHalf_ne_top`).  Under `uniformOn volume B_1` it has mass exactly `(2ⁿ)⁻¹`, by
`volume_ball_one_eq`, and `(2ⁿ)⁻¹ < 1` for `n ≥ 1` by `one_lt_two_pow_ennreal`. -/
theorem uniformOn_ball_half_ne_uniformOn_ball (n : ℕ) [NeZero n] :
    Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
      ≠ Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  intro heq
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    Metric.ball_subset_ball (by norm_num)
  -- The half-ball has full mass under the start.
  have h1 : Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) = 1 :=
    Arlib.uniformOn_self volume measurableSet_ball volume_ballHalf_ne_zero
      volume_ballHalf_ne_top
  -- and mass exactly `(2ⁿ)⁻¹` under the stationary measure.
  have h2 : Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
    rw [Arlib.uniformOn_apply volume measurableSet_ball measurableSet_ball,
      Set.inter_eq_left.2 hsub, volume_ball_one_eq n]
    calc volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
          / (2 ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)))
        = (1 * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)))
          / (2 ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))) := by
          rw [one_mul]
      _ = 1 / 2 ^ n :=
          ENNReal.mul_div_mul_right 1 (2 ^ n) volume_ballHalf_ne_zero volume_ballHalf_ne_top
      _ = ((2 : ℝ≥0∞) ^ n)⁻¹ := one_div _
  rw [heq, h2] at h1
  exact absurd h1 (ENNReal.inv_lt_one.2 (one_lt_two_pow_ennreal n)).ne

/-- The warmness constant in the real-valued form `mixesWithin_lazy_ballWalk_unitBall_uncond`
consumes: `ENNReal.ofReal (2ⁿ : ℝ) = (2 : ℝ≥0∞) ^ n`. -/
theorem ofReal_two_pow (n : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ n) = (2 : ℝ≥0∞) ^ n := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

end HalfBall

/-! ## The repaired non-vacuity witness -/

/-- **Non-vacuity, from a start that is not already stationary** (`CLAUDE.md` §11).

This is the theorem this file exists for.  It has the shape of
`exists_unconditional_mixing_unitBall` — a starting law, a step count, and the
`MixesWithin` conclusion of `mixesWithin_lazy_ballWalk_unitBall_uncond` — but with two
extra conjuncts inside the `∃` that the old witness could not supply:

* the warmness constant is `2ⁿ`, which by `one_lt_two_pow_ennreal` is `> 1`; and
* **the start is not the stationary measure**, `mu0 ≠ uniformOn volume B_1`.

The old witness took `mu0` to be the stationary measure itself at `M = 1`.  That satisfies
`MixesWithin` at every time `t` trivially — a chain begun at equilibrium never leaves it —
so it certifies nothing about the conductance bound, the isoperimetry, or the step count
that the surrounding stack computes.  Here the chain starts on the half-ball, at total
variation distance bounded away from `0` from its target, and must genuinely mix.

The step count is `conductanceMixingTime 2ⁿ …`, which is exponential in `n`; as the
`UnitBallMixing` module docstring says, this is not a polynomial-time sampler and must not
be quoted as one. -/
theorem exists_unconditional_mixing_unitBall_nonstationary (n : ℕ) (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {eps : ℝ} (heps : 0 < eps) :
    ∃ (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (_ : IsProbabilityMeasure mu0) (t : ℕ),
      Arlib.IsWarm (2 ^ n) mu0
          (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ∧
        mu0 ≠ Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
        MixesWithin (lazy (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ))
          (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) mu0 t
          (ENNReal.ofReal eps) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI hprob : IsProbabilityMeasure
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))) :=
    Arlib.isProbabilityMeasure_uniformOn volume volume_ballHalf_ne_zero volume_ballHalf_ne_top
  refine ⟨Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)), hprob,
    conductanceMixingTime ((2 : ℝ) ^ n)
      (min (((1:ℝ)/2 ^ n) / 32)
        ((1/2:ℝ) ^ (n+1) * ((1:ℝ)/2 ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps,
    isWarm_uniformOn_ball_half n, uniformOn_ball_half_ne_uniformOn_ball n, ?_⟩
  refine mixesWithin_lazy_ballWalk_unitBall_uncond n hn hδ hδ1 (M := (2 : ℝ) ^ n)
    (one_le_pow₀ (by norm_num)) ?_ heps le_rfl
  rw [ofReal_two_pow]
  exact isWarm_uniformOn_ball_half n

/-! ## Axiom audit (`CLAUDE.md` §4)

Every declaration in this file must depend on exactly `[propext, Classical.choice,
Quot.sound]`. -/

#print axioms volume_ballHalf_ne_zero
#print axioms volume_ballHalf_ne_top
#print axioms volume_ball_one_eq
#print axioms one_lt_two_pow_ennreal
#print axioms isWarm_uniformOn_ball_half
#print axioms uniformOn_ball_half_ne_uniformOn_ball
#print axioms ofReal_two_pow
#print axioms exists_unconditional_mixing_unitBall_nonstationary

end Arlib.MarkovChains
