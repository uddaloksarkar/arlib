/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.ConvexBodyMixing

/-!
# A genuinely non-stationary warm start for the ball walk on an *arbitrary* convex body

## What this file closes

`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_convex` and
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`
(`Arlib/MarkovChains/Continuous/ConvexBodyMixing.lean`) carry the hypothesis

    hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn volume K)

and nothing in the library discharged it for a general body `K`: the only proved warm start
was `Arlib.MarkovChains.isWarm_uniformOn_ball_half`
(`Arlib/MarkovChains/Continuous/WarmStart.lean`), which is about the Euclidean unit ball and
its half-ball.  Consequently every "non-vacuity" witness for a general `K`
(`exists_unconditional_mixing_convex`, `exists_unconditional_mixing_polytope`) had to fall
back on `isWarm_one_self`, i.e. on starting the chain *at its own stationary measure*.  A
chain started at stationarity is already mixed, so `MixesWithin` then holds at every time
`t` for reasons that have nothing to do with conductance, isoperimetry or the step count;
`#print axioms` is blind to that collapse because nothing was assumed (`CLAUDE.md` §11).

This file supplies, for any convex body `K` with an inscribed ball `B(c,γ) ⊆ K`, a start
that is *not* the stationary measure — the uniform law on the inscribed ball — together
with an explicit warmness constant, a proof that it is different from `uniformOn volume K`,
and the packaged mixing statement carrying the `≠` conjunct inside the existential.

## The constant

For measurable `S`,

    uniformOn volume (B c γ) S = vol (S ∩ B c γ) / vol (B c γ),
    uniformOn volume K       S = vol (S ∩ K)     / vol K,

and `B c γ ⊆ K` gives `vol (S ∩ B c γ) ≤ vol (S ∩ K)`.  Multiplying the second display by
`M := vol K / vol (B c γ)` cancels its denominator (this is `div_mul_div_cancel_mid`, the
only real `ℝ≥0∞` step, and it is where `vol K ∉ {0, ∞}` is used) and leaves
`vol (S ∩ K) / vol (B c γ)`.  So `M = vol K / vol (B c γ)` works, and it is the *exact*
volume ratio: the only slack is the set inclusion.  If moreover all pairwise distances in
`K` are bounded by `D`, then `K ⊆ closedBall c D` and Haar scaling
(`Measure.addHaar_closedBall`, `Measure.addHaar_ball_of_pos`) bounds the ratio by
`(D/γ)ⁿ` — exponentially large in `n`, as expected for this route, and not optimised.

## The degenerate cases, guarded explicitly

`uniformOn volume K` is the *zero* measure when `vol K ∈ {0, ∞}`, and `ENNReal.toReal ⊤ = 0`
turns an infinite constant into the real number `0`.  Every statement below that asserts
anything about masses carries `hK0 : volume K ≠ 0` and `hKtop : volume K ≠ ⊤` explicitly
(`hK0` is *derived* from properness in the packaged theorem), and `γ > 0` guards the start
in the same way.  `volume_div_volume_ball_ne_top` is what makes the real-valued constant
`(vol K / vol (B c γ)).toReal` an honest number rather than a collapsed `0`.

## Main results

* `Arlib.MarkovChains.isWarm_uniformOn_inscribed` — **the warm start**, at the exact ratio
  `M = vol K / vol (B c γ)`.
* `Arlib.MarkovChains.isWarm_uniformOn_inscribed_pow` — the same at the explicit
  `M = (D/γ)ⁿ`, via `volume_div_volume_ball_le`.
* `Arlib.MarkovChains.uniformOn_inscribed_ne_uniformOn` — **the point of the exercise**:
  when the inclusion is proper in measure, the start is *not* the stationary measure.
* `Arlib.MarkovChains.exists_nonstationary_warm_start_mixing_convex` — the package
  `mixesWithin_lazy_ballWalk_convex` consumes: a start, a probability-measure instance, a
  real `M ≥ 1`, a step count, warmness, **the `≠` conjunct**, and the mixing conclusion.
* `Arlib.MarkovChains.exists_nonstationary_warm_start_mixing_ball_two`,
  `Arlib.MarkovChains.exists_nonstationary_warm_start_mixing_cube` — the non-vacuity
  instances, on `B(0,1) ⊆ B(0,2)` (warm constant exactly `2ⁿ`) and on the inscribed ball
  `B(0,1/2)` of the cube `[-1,1]ⁿ` (warm constant `(4√n)ⁿ`).  Both are proper in measure in
  every dimension `n ≥ 1`.

## A remark on the cube

The obvious instance — the cube `[-1,1]ⁿ` with its *unit* inscribed ball — is **not** proper
at `n = 1`: there `B(0,1) = (-1,1)` and the cube `[-1,1]` have the same Lebesgue measure `2`,
so the start would equal the stationary measure and the witness would be worthless again.
The cube instance below therefore uses the inscribed ball of radius `1/2`, for which
properness holds in every dimension `n ≥ 1` (`volume_ball_half_lt_volume_cube`).

## Scope

Nothing here improves the mixing *rate*: the constants inherited from
`mixesWithin_lazy_ballWalk_convex` are exponentially small in `n` and the warm start adds a
further exponentially large `M`.  This is not a polynomial-time sampler and must not be
quoted as one.  What it adds is that the mixing theorem is now exercised from a start at
positive total-variation distance from its target, instead of being satisfied trivially.
-/

open MeasureTheory
open scoped ENNReal

namespace Arlib.MarkovChains

section Ratio

variable {n : ℕ}

/-- **The `ℝ≥0∞` cancellation behind the warm-start bound.**  Multiplying `u / a` by the
ratio `a / b` cancels the `a`, leaving `u / b`:

    (a / b) * (u / a) = u / b,   provided `a ≠ 0` and `a ≠ ∞`.

Both guards are essential and both are exactly the degenerate cases `volume K = 0` and
`volume K = ∞` in which `Arlib.uniformOn volume K` collapses to the zero measure.  This is
the analogue of the `ENNReal.mul_div_mul_left` step in
`Arlib/MarkovChains/Continuous/WarmStart.lean`, at a general ratio instead of `2ⁿ`. -/
theorem div_mul_div_cancel_mid {a b u : ℝ≥0∞} (ha0 : a ≠ 0) (hatop : a ≠ ⊤) :
    a / b * (u / a) = u / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  have hac : a * b⁻¹ * (u * a⁻¹) = a * a⁻¹ * (u * b⁻¹) := by
    simp only [mul_comm, mul_assoc, mul_left_comm]
  rw [hac, ENNReal.mul_inv_cancel ha0 hatop, one_mul]

/-- **The uniform law on an inscribed ball is a warm start for the uniform law on the
body**, at the exact volume ratio `M = vol K / vol (B c γ)`.

Assumed: `K` measurable with `0 < vol K < ∞`, and a ball `B(c,γ) ⊆ K` with `γ > 0`.  No
convexity, no diameter bound, no isoperimetry — the statement is pure measure theory and
holds for any measurable `K` containing the ball.

Proved: `IsWarm (vol K / vol (B c γ)) (uniformOn volume (B c γ)) (uniformOn volume K)`,
i.e. `uniformOn volume (B c γ) S ≤ (vol K / vol (B c γ)) * uniformOn volume K S` for every
measurable `S`.  Both `uniformOn` values expand by `Arlib.uniformOn_apply`; the constant
cancels the denominator on the right by `div_mul_div_cancel_mid` (this is where
`hK0`/`hKtop` are used), and what is left is monotonicity of `volume` under
`S ∩ B c γ ⊆ S ∩ K`.  So the constant is not merely sufficient — it is the volume ratio,
and the only slack is the inclusion.

`hγ` is not needed for the inequality (at `γ ≤ 0` the ball is empty and the left side is
`0`); it is kept because it is what makes the start a probability measure, and callers
have it.  It is `Arlib.isProbabilityMeasure_uniformOn` that consumes it, inside
`exists_nonstationary_warm_start_mixing_convex`. -/
theorem isWarm_uniformOn_inscribed {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K) :
    Arlib.IsWarm (volume K / volume (Metric.ball c γ))
      (Arlib.uniformOn volume (Metric.ball c γ)) (Arlib.uniformOn volume K) := by
  intro S hS
  -- the guard that makes the start a probability measure (`hγ`); not needed for the bound
  have : volume (Metric.ball c γ) ≠ 0 := (Metric.measure_ball_pos volume c hγ).ne'
  rw [Arlib.uniformOn_apply volume measurableSet_ball hS,
    Arlib.uniformOn_apply volume hK hS, div_mul_div_cancel_mid hK0 hKtop]
  exact ENNReal.div_le_div_right
    (measure_mono (Set.inter_subset_inter_right _ hball)) _

/-- **The warm-start ratio is at most `(D/γ)ⁿ`.**

Assumed: `c ∈ K`, all pairwise distances in `K` bounded by `D`, and `γ > 0`.  Proved:
`vol K / vol (B c γ) ≤ ofReal ((D/γ)ⁿ)`.

`K ⊆ closedBall c D`, so `vol K ≤ ofReal (Dⁿ) · vol (B 0 1)` by
`MeasureTheory.Measure.addHaar_closedBall`, while `vol (B c γ) = ofReal (γⁿ) · vol (B 0 1)`
exactly by `MeasureTheory.Measure.addHaar_ball_of_pos`; the common factor `vol (B 0 1)`
cancels because it is neither `0` nor `∞` (`volume_unitBall_ne_zero`,
`volume_unitBall_ne_top`).  The constant is exponentially large in `n` and no attempt is
made to improve it. -/
theorem volume_div_volume_ball_le {K : Set (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} (hcK : c ∈ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {γ : ℝ} (hγ : 0 < γ) :
    volume K / volume (Metric.ball c γ) ≤ ENNReal.ofReal ((D / γ) ^ n) := by
  have hD0 : (0:ℝ) ≤ D := by simpa using hD c hcK c hcK
  have hsub : K ⊆ Metric.closedBall c D := fun z hz => by
    simpa [Metric.mem_closedBall] using hD z hz c hcK
  have hVK : volume K ≤ ENNReal.ofReal (D ^ n)
      * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    refine (measure_mono hsub).trans ?_
    have h := Measure.addHaar_closedBall (volume : Measure (EuclideanSpace ℝ (Fin n))) c hD0
    rw [finrank_euclideanSpace_fin] at h
    exact h.le
  have hVb : volume (Metric.ball c γ) = ENNReal.ofReal (γ ^ n)
      * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    have h := Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) c hγ
    rwa [finrank_euclideanSpace_fin] at h
  calc volume K / volume (Metric.ball c γ)
      ≤ (ENNReal.ofReal (D ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
        / (ENNReal.ofReal (γ ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
        rw [hVb]; exact ENNReal.div_le_div_right hVK _
    _ = ENNReal.ofReal (D ^ n) / ENNReal.ofReal (γ ^ n) :=
        ENNReal.mul_div_mul_right _ _ volume_unitBall_ne_zero volume_unitBall_ne_top
    _ = ENNReal.ofReal ((D / γ) ^ n) := by
        rw [div_pow, ENNReal.ofReal_div_of_pos (by positivity)]

/-- **The warm start with an explicit constant**: `(D/γ)ⁿ`.  `isWarm_uniformOn_inscribed`
weakened along `volume_div_volume_ball_le` by `Arlib.IsWarm.mono`.  This is the form a
caller who knows only the inradius `γ` and the diameter bound `D` — the standard
"well-rounded body" data — can use without computing any volume. -/
theorem isWarm_uniformOn_inscribed_pow {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K) :
    Arlib.IsWarm (ENNReal.ofReal ((D / γ) ^ n))
      (Arlib.uniformOn volume (Metric.ball c γ)) (Arlib.uniformOn volume K) :=
  (isWarm_uniformOn_inscribed hK hK0 hKtop hγ hball).mono
    (volume_div_volume_ball_le (hball (Metric.mem_ball_self hγ)) hD hγ)

/-- **The point of the exercise: the start is genuinely not the stationary measure.**

Without this the warm start would be worthless.  A chain started *at* stationarity is
already mixed, so `MixesWithin` holds at every time `t` for reasons unrelated to
conductance, isoperimetry or the step count, and a "non-vacuity witness" built from such a
start certifies nothing about mixing — the defect this project has already been bitten by
once (`CLAUDE.md` §11; `Arlib/MarkovChains/Continuous/WarmStart.lean`).

Assumed: the usual guards, plus `hproper : vol (B c γ) < vol K` — the inclusion is proper
*in measure*, not merely as sets (a proper inclusion of null difference would leave the two
uniform laws equal, and then no separation is possible).

Proved: the two measures differ.  The separating set is the inscribed ball itself: it has
mass `1` under the start (`Arlib.uniformOn_self`) and mass `vol (B c γ) / vol K < 1` under
the target, the inequality being exactly `hproper` via `ENNReal.div_lt_iff`. -/
theorem uniformOn_inscribed_ne_uniformOn {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K)
    (hproper : volume (Metric.ball c γ) < volume K) :
    Arlib.uniformOn volume (Metric.ball c γ) ≠ Arlib.uniformOn volume K := by
  intro heq
  have h1 : Arlib.uniformOn volume (Metric.ball c γ) (Metric.ball c γ) = 1 :=
    Arlib.uniformOn_self volume measurableSet_ball
      (Metric.measure_ball_pos volume c hγ).ne' measure_ball_lt_top.ne
  have h2 : Arlib.uniformOn volume K (Metric.ball c γ)
      = volume (Metric.ball c γ) / volume K := by
    rw [Arlib.uniformOn_apply volume hK measurableSet_ball, Set.inter_eq_left.2 hball]
  have h3 : volume (Metric.ball c γ) / volume K < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl hK0) (Or.inl hKtop), one_mul]
    exact hproper
  rw [heq, h2] at h1
  exact absurd h1 h3.ne

/-- The warm-start constant is finite. -/
theorem volume_div_volume_ball_ne_top {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKtop : volume K ≠ ⊤) {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) :
    volume K / volume (Metric.ball c γ) ≠ ⊤ :=
  ENNReal.div_ne_top hKtop (Metric.measure_ball_pos volume c hγ).ne'

/-- The warm-start constant is at least `1`. -/
theorem one_le_volume_div_volume_ball {K : Set (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K) :
    1 ≤ volume K / volume (Metric.ball c γ) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (Metric.measure_ball_pos volume c hγ).ne')
    (Or.inl measure_ball_lt_top.ne), one_mul]
  exact measure_mono hball

/-- The real-valued form of the warm-start constant is at least `1`. -/
theorem one_le_toReal_volume_div_volume_ball {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKtop : volume K ≠ ⊤) {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball c γ ⊆ K) :
    (1:ℝ) ≤ (volume K / volume (Metric.ball c γ)).toReal := by
  have := ENNReal.toReal_mono (volume_div_volume_ball_ne_top hKtop hγ)
    (one_le_volume_div_volume_ball hγ hball)
  simpa using this

/-- **The package `mixesWithin_lazy_ballWalk_convex` consumes.**

Assumed: `1 ≤ n`; `K` measurable, convex, of finite volume, all pairwise distances bounded
by `D`, containing `B(c,γ)` with `γ > 0`; the inclusion proper in measure; a step size
`0 < δ ≤ γ`; an accuracy `eps > 0`.  `volume K ≠ 0` is *not* a hypothesis: it follows from
properness.  There is no warm-start hypothesis and no step-count hypothesis — both are
produced.

Proved: there are a starting law `mu0` (a genuine probability measure), a real warmness
constant `M ≥ 1` and a step count `t` such that `mu0` is `M`-warm for `uniformOn volume K`,
**`mu0 ≠ uniformOn volume K`**, and the lazy ball walk started from `mu0` is within `eps`
of `uniformOn volume K` after `t` steps.  The `≠` conjunct sits *inside* the existential
precisely so that the witness cannot degenerate to the stationary start that
`exists_unconditional_mixing_convex` uses.

The witness is `mu0 = uniformOn volume (B c γ)` with
`M = (vol K / vol (B c γ)).toReal`, which is a real number and not a collapsed `0` because
of `volume_div_volume_ball_ne_top`, and `t` the explicit
`conductanceMixingTime M (min …) eps` of `mixesWithin_lazy_ballWalk_convex`. -/
theorem exists_nonstationary_warm_start_mixing_convex (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hKtop : volume K ≠ ⊤)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K)
    (hproper : volume (Metric.ball c γ) < volume K)
    {δ : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ) {eps : ℝ} (heps : 0 < eps) :
    ∃ (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (_ : IsProbabilityMeasure mu0)
      (M : ℝ) (t : ℕ),
      1 ≤ M ∧
      Arlib.IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn volume K) ∧
      mu0 ≠ Arlib.uniformOn volume K ∧
      MixesWithin (lazy (ballWalk K δ)) (Arlib.uniformOn volume K) mu0 t
        (ENNReal.ofReal eps) := by
  have hK0 : volume K ≠ 0 := (pos_of_gt hproper).ne'
  have hb0 : volume (Metric.ball c γ) ≠ 0 := (Metric.measure_ball_pos volume c hγ).ne'
  have hbtop : volume (Metric.ball c γ) ≠ ⊤ := measure_ball_lt_top.ne
  haveI hprob : IsProbabilityMeasure (Arlib.uniformOn volume (Metric.ball c γ)) :=
    Arlib.isProbabilityMeasure_uniformOn volume hb0 hbtop
  have hMwarm : Arlib.IsWarm
      (ENNReal.ofReal (volume K / volume (Metric.ball c γ)).toReal)
      (Arlib.uniformOn volume (Metric.ball c γ)) (Arlib.uniformOn volume K) := by
    rw [ENNReal.ofReal_toReal (volume_div_volume_ball_ne_top hKtop hγ)]
    exact isWarm_uniformOn_inscribed hK hK0 hKtop hγ hball
  refine ⟨Arlib.uniformOn volume (Metric.ball c γ), hprob,
    (volume K / volume (Metric.ball c γ)).toReal,
    conductanceMixingTime ((volume K / volume (Metric.ball c γ)).toReal)
      (min ((γ / (γ + D)) ^ n / 32)
        ((1 / 2 : ℝ) ^ n / D * ((γ / (γ + D)) ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps,
    one_le_toReal_volume_div_volume_ball hKtop hγ hball, hMwarm,
    uniformOn_inscribed_ne_uniformOn hK hK0 hKtop hγ hball hproper, ?_⟩
  exact mixesWithin_lazy_ballWalk_convex hn hK hconv hK0 hKtop hD hγ hball hδ hδγ
    (one_le_toReal_volume_div_volume_ball hKtop hγ hball) hMwarm heps le_rfl

end Ratio

section ConcentricBalls

variable {n : ℕ}

/-- Haar scaling: the ball of radius `2` has `2ⁿ` times the volume of the unit ball. -/
theorem volume_ball_two (n : ℕ) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
      = ENNReal.ofReal ((2:ℝ) ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have h := Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0
    (r := (2:ℝ)) (by norm_num)
  rwa [finrank_euclideanSpace_fin] at h

/-- The inclusion `B(0,1) ⊆ B(0,2)` is proper in measure, for every `n ≥ 1`. -/
theorem volume_ball_one_lt_volume_ball_two (hn : 1 ≤ n) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2) := by
  have hone : 1 < ENNReal.ofReal ((2:ℝ) ^ n) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    exact one_lt_pow' (by norm_num) (by omega)
  calc volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      = 1 * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := (one_mul _).symm
    _ < ENNReal.ofReal ((2:ℝ) ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
        ENNReal.mul_lt_mul_left volume_unitBall_ne_zero volume_unitBall_ne_top hone
    _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2) := (volume_ball_two n).symm

/-- The warm-start constant for `B(0,1) ⊆ B(0,2)` is exactly `2ⁿ`. -/
theorem volume_ball_two_div_volume_ball_one (n : ℕ) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
      / volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      = ENNReal.ofReal ((2:ℝ) ^ n) := by
  rw [volume_ball_two n, mul_div_assoc,
    ENNReal.div_self volume_unitBall_ne_zero volume_unitBall_ne_top, mul_one]

/-- **The concrete warm start**: uniform on `B(0,1)` is `2ⁿ`-warm for uniform on `B(0,2)`,
and `2ⁿ` is the *exact* ratio, not an over-estimate (`volume_ball_two_div_volume_ball_one`).
Compare the crude general bound `(D/γ)ⁿ = 4ⁿ` available from
`isWarm_uniformOn_inscribed_pow` with `D = 4`, `γ = 1`. -/
theorem isWarm_uniformOn_ball_one_ball_two (n : ℕ) :
    Arlib.IsWarm (ENNReal.ofReal ((2:ℝ) ^ n))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)) := by
  rw [← volume_ball_two_div_volume_ball_one n]
  exact isWarm_uniformOn_inscribed measurableSet_ball
    (Metric.measure_ball_pos volume 0 (by norm_num)).ne' measure_ball_lt_top.ne
    (by norm_num) (Metric.ball_subset_ball (by norm_num))

/-- **The concrete start is not the stationary measure.** -/
theorem uniformOn_ball_one_ne_uniformOn_ball_two (hn : 1 ≤ n) :
    Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      ≠ Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2) :=
  uniformOn_inscribed_ne_uniformOn measurableSet_ball
    (Metric.measure_ball_pos volume 0 (by norm_num)).ne' measure_ball_lt_top.ne
    (by norm_num) (Metric.ball_subset_ball (by norm_num))
    (volume_ball_one_lt_volume_ball_two hn)

/-- All pairwise distances in `B(0,2)` are at most `4`. -/
theorem dist_le_four_of_mem_ball_two :
    ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2,
      ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2, dist x y ≤ (4:ℝ) := by
  intro x hx y hy
  rw [Metric.mem_ball] at hx hy
  have := dist_triangle x (0 : EuclideanSpace ℝ (Fin n)) y
  rw [dist_comm (0 : EuclideanSpace ℝ (Fin n)) y] at this
  linarith

/-- **Non-vacuity with a concrete body and an explicit constant** (`CLAUDE.md` §11).

Assumed: `1 ≤ n`, `0 < δ ≤ 1`, `eps > 0`.  Nothing else: the body is `B(0,2)`, the start is
uniform on `B(0,1)`, the warmness constant is the explicit `2ⁿ`, and the diameter bound is
the explicit `D = 4`.

Proved: a step count exists at which the lazy ball walk on `B(0,2)`, started from uniform
on `B(0,1)`, is within `eps` of its stationary measure — *and* that start is `2ⁿ`-warm and
**different from** the stationary measure.  This is the instance showing that the
hypothesis bundle of `exists_nonstationary_warm_start_mixing_convex` (in particular
`hproper`) is satisfiable in every dimension `n ≥ 1`. -/
theorem exists_nonstationary_warm_start_mixing_ball_two (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {eps : ℝ} (heps : 0 < eps) :
    ∃ t : ℕ,
      Arlib.IsWarm (ENNReal.ofReal ((2:ℝ) ^ n))
          (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
          (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)) ∧
        Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
          ≠ Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2) ∧
        MixesWithin (lazy (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2) δ))
          (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2))
          (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) t
          (ENNReal.ofReal eps) := by
  haveI hprob : IsProbabilityMeasure
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    Arlib.isProbabilityMeasure_uniformOn volume volume_unitBall_ne_zero volume_unitBall_ne_top
  refine ⟨conductanceMixingTime ((2:ℝ) ^ n)
      (min (((1:ℝ) / 5) ^ n / 32)
        ((1 / 2 : ℝ) ^ n / 4 * (((1:ℝ) / 5) ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps,
    isWarm_uniformOn_ball_one_ball_two n, uniformOn_ball_one_ne_uniformOn_ball_two hn, ?_⟩
  refine mixesWithin_lazy_ballWalk_convex hn measurableSet_ball (convex_ball _ _)
    (Metric.measure_ball_pos volume 0 (by norm_num)).ne' measure_ball_lt_top.ne
    (D := 4) dist_le_four_of_mem_ball_two (c := 0) (γ := 1) one_pos
    (Metric.ball_subset_ball (by norm_num)) hδ hδ1 (M := (2:ℝ) ^ n)
    (one_le_pow₀ (by norm_num)) (isWarm_uniformOn_ball_one_ball_two n) heps ?_
  rw [show ((1:ℝ) / (1 + 4)) = 1 / 5 by norm_num]

end ConcentricBalls

section Cube

variable {n : ℕ}

/-- Pure data: the `2n` normal vectors `±eᵢ`.  Asserts nothing; the body they cut out is
characterised by `mem_cube_iff`. -/
noncomputable def cubeA (n : ℕ) : Fin n × Bool → EuclideanSpace ℝ (Fin n) :=
  fun p => if p.2 then EuclideanSpace.single p.1 (1:ℝ) else -EuclideanSpace.single p.1 (1:ℝ)

/-- Pure data: the right-hand sides, all `1`. -/
def cubeb (n : ℕ) : Fin n × Bool → ℝ := fun _ => 1

/-- The cube `[-1,1]ⁿ`, as an (un-inflated) polytope. -/
abbrev cube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Arlib.Polytope.inflate (cubeA n) (cubeb n) 0

/-- The membership characterisation: `cube n` really is `[-1,1]ⁿ`. -/
theorem mem_cube_iff (x : EuclideanSpace ℝ (Fin n)) : x ∈ cube n ↔ ∀ i, |x i| ≤ 1 := by
  constructor
  · intro hx i
    have h1 := hx (i, true)
    have h2 := hx (i, false)
    simp [cubeA, cubeb, EuclideanSpace.inner_single_left, inner_neg_left] at h1 h2
    exact abs_le.2 ⟨by linarith, h1⟩
  · intro hx
    rw [Arlib.Polytope.mem_inflate]
    rintro ⟨i, s⟩
    have hxi := abs_le.1 (hx i)
    cases s <;>
      simp [cubeA, cubeb, EuclideanSpace.inner_single_left, inner_neg_left] <;>
      linarith [hxi.1, hxi.2]

/-- `cube n` is measurable. -/
theorem measurableSet_cube : MeasurableSet (cube n) :=
  Arlib.Polytope.measurableSet_inflate _ _ _

/-- `cube n` is convex. -/
theorem convex_cube : Convex ℝ (cube n) :=
  Arlib.Polytope.convex_inflate _ _ _

/-- The inscribed ball `B(0, 1/2) ⊆ [-1,1]ⁿ`. -/
theorem ball_half_subset_cube : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1/2) ⊆ cube n := by
  intro x hx
  have hxn : ‖x‖ < 1/2 := by simpa [Metric.mem_ball, dist_zero_right] using hx
  rw [mem_cube_iff]
  intro i
  have := PiLp.norm_apply_le (p := 2) x i
  rw [Real.norm_eq_abs] at this
  linarith

/-- The diameter bound `D = 2√n` for the cube. -/
theorem dist_le_of_mem_cube :
    ∀ x ∈ cube n, ∀ y ∈ cube n, dist x y ≤ 2 * Real.sqrt (n : ℝ) := by
  intro x hx y hy
  have hxi := (mem_cube_iff x).1 hx
  have hyi := (mem_cube_iff y).1 hy
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ 4 * (n : ℝ) := by
    have hle : ∀ i ∈ Finset.univ, dist (x i) (y i) ^ 2 ≤ (4:ℝ) := by
      intro i _
      have h1 := abs_le.1 (hxi i)
      have h2 := abs_le.1 (hyi i)
      have hd : dist (x i) (y i) = |x i - y i| := Real.dist_eq _ _
      rw [hd, sq_abs]
      nlinarith [h1.1, h1.2, h2.1, h2.2]
    calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin n, (4:ℝ) := Finset.sum_le_sum hle
      _ = 4 * (n : ℝ) := by simp [mul_comm]
  calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt (4 * (n:ℝ)) := Real.sqrt_le_sqrt hsum
    _ = 2 * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
          show Real.sqrt 4 = 2 by
            rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]

theorem zero_mem_cube : (0 : EuclideanSpace ℝ (Fin n)) ∈ cube n :=
  ball_half_subset_cube (Metric.mem_ball_self (by norm_num))

theorem volume_cube_ne_zero : volume (cube n) ≠ 0 :=
  volume_ne_zero_of_ball_subset (by norm_num) ball_half_subset_cube

theorem volume_cube_ne_top : volume (cube n) ≠ ⊤ :=
  volume_ne_top_of_diam_bound zero_mem_cube dist_le_of_mem_cube

/-- **The inclusion `B(0,1/2) ⊆ [-1,1]ⁿ` is proper in measure**, in every dimension
`n ≥ 1`: the ball `B(p, 1/20)` around `p = (9/10)·e₀` lies in the cube and misses
`B(0,1/2)`. -/
theorem volume_ball_half_lt_volume_cube (hn : 1 ≤ n) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1/2)) < volume (cube n) := by
  have hn0 : 0 < n := hn
  set j : Fin n := ⟨0, hn0⟩ with hj
  set p : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (9/10 : ℝ) with hp
  have hpnorm : ‖p‖ = 9/10 := by
    rw [hp, PiLp.norm_single]
    rw [Real.norm_eq_abs]
    norm_num
  have hpcoord : ∀ i, |p i| ≤ 9/10 := by
    intro i
    rcases eq_or_ne i j with h | h
    · rw [hp, PiLp.single_apply, if_pos h]; norm_num
    · rw [hp, PiLp.single_apply, if_neg h]; norm_num
  have hsub2 : Metric.ball p (1/20) ⊆ cube n := by
    intro z hz
    rw [mem_cube_iff]
    intro i
    have h2 : ‖z - p‖ < 1/20 := by
      rw [← dist_eq_norm]; exact hz
    have h1 : |z i - p i| ≤ ‖z - p‖ := by
      have hc : (z - p) i = z i - p i := rfl
      have := PiLp.norm_apply_le (p := 2) (z - p) i
      rw [hc, Real.norm_eq_abs] at this
      exact this
    have h3 := hpcoord i
    have h4 : |z i| ≤ |p i| + |z i - p i| := by
      calc |z i| = |p i + (z i - p i)| := by ring_nf
        _ ≤ |p i| + |z i - p i| := abs_add_le _ _
    linarith
  have hdisj : Disjoint (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1/2))
      (Metric.ball p (1/20)) := by
    refine Metric.ball_disjoint_ball ?_
    rw [dist_zero_left, hpnorm]
    norm_num
  calc volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1/2))
      < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1/2)) + volume (Metric.ball p (1/20)) :=
        ENNReal.lt_add_right measure_ball_lt_top.ne
          (Metric.measure_ball_pos volume p (by norm_num)).ne'
    _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1/2) ∪ Metric.ball p (1/20)) :=
        (measure_union hdisj measurableSet_ball).symm
    _ ≤ volume (cube n) :=
        measure_mono (Set.union_subset ball_half_subset_cube hsub2)

/-- **The explicit warm start on the cube**: uniform on the inscribed ball `B(0,1/2)` is
`(4√n)ⁿ`-warm for uniform on `[-1,1]ⁿ`.

This is `isWarm_uniformOn_inscribed_pow` at `γ = 1/2` and `D = 2√n`, so the constant is
`(D/γ)ⁿ = (4√n)ⁿ` — exponentially large, as expected, and unoptimised (the exact ratio is
`2ⁿ / vol B(0,1/2)`, which this file does not compute).  Unlike the ball-in-ball instance
the ambient body here is not a ball, so the warm start is genuinely the inscribed ball of a
differently shaped body. -/
theorem isWarm_uniformOn_ball_half_cube (n : ℕ) :
    Arlib.IsWarm (ENNReal.ofReal ((4 * Real.sqrt (n:ℝ)) ^ n))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1/2)))
      (Arlib.uniformOn volume (cube n)) := by
  have h := isWarm_uniformOn_inscribed_pow (K := cube n) measurableSet_cube
    volume_cube_ne_zero volume_cube_ne_top (D := 2 * Real.sqrt (n:ℝ)) dist_le_of_mem_cube
    (c := 0) (γ := 1/2) (by norm_num) ball_half_subset_cube
  rwa [show (2 * Real.sqrt (n:ℝ) / (1/2)) = 4 * Real.sqrt (n:ℝ) by ring] at h

/-- **The start on the cube is not the stationary measure**, in every dimension `n ≥ 1`. -/
theorem uniformOn_ball_half_ne_uniformOn_cube (hn : 1 ≤ n) :
    Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1/2))
      ≠ Arlib.uniformOn volume (cube n) :=
  uniformOn_inscribed_ne_uniformOn measurableSet_cube volume_cube_ne_zero volume_cube_ne_top
    (by norm_num) ball_half_subset_cube (volume_ball_half_lt_volume_cube hn)

/-- **Non-vacuity on the cube `[-1,1]ⁿ`** — the body `ConvexBodyMixing.lean` already uses as
its polytope witness, here carrying a non-stationary start.

Assumed: `1 ≤ n`, `0 < δ ≤ 1/2`, `eps > 0`.  The inscribed ball has radius `γ = 1/2` (not
`1`: see the module docstring — with the unit ball the inclusion is not proper at `n = 1`
and the witness would collapse), and `D = 2√n`.

Proved: the full package of `exists_nonstationary_warm_start_mixing_convex` for the cube,
including the `≠`-to-stationary conjunct.  The explicit warmness constant for this instance
is `(4√n)ⁿ` (`isWarm_uniformOn_ball_half_cube`); the `M` produced here is the smaller exact
ratio `(vol cube / vol B(0,1/2)).toReal`. -/
theorem exists_nonstationary_warm_start_mixing_cube (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) {eps : ℝ} (heps : 0 < eps) :
    ∃ (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (_ : IsProbabilityMeasure mu0)
      (M : ℝ) (t : ℕ),
      1 ≤ M ∧
      Arlib.IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn volume (cube n)) ∧
      mu0 ≠ Arlib.uniformOn volume (cube n) ∧
      MixesWithin (lazy (ballWalk (cube n) δ)) (Arlib.uniformOn volume (cube n)) mu0 t
        (ENNReal.ofReal eps) :=
  exists_nonstationary_warm_start_mixing_convex hn measurableSet_cube convex_cube
    volume_cube_ne_top dist_le_of_mem_cube (by norm_num) ball_half_subset_cube
    (volume_ball_half_lt_volume_cube hn) hδ hδ1 heps

end Cube


/-! ## Axiom audit (`CLAUDE.md` §4)

Every declaration in this file must depend on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms div_mul_div_cancel_mid
#print axioms isWarm_uniformOn_inscribed
#print axioms volume_div_volume_ball_le
#print axioms isWarm_uniformOn_inscribed_pow
#print axioms uniformOn_inscribed_ne_uniformOn
#print axioms volume_div_volume_ball_ne_top
#print axioms one_le_volume_div_volume_ball
#print axioms one_le_toReal_volume_div_volume_ball
#print axioms exists_nonstationary_warm_start_mixing_convex
#print axioms volume_ball_two
#print axioms volume_ball_one_lt_volume_ball_two
#print axioms volume_ball_two_div_volume_ball_one
#print axioms isWarm_uniformOn_ball_one_ball_two
#print axioms uniformOn_ball_one_ne_uniformOn_ball_two
#print axioms dist_le_four_of_mem_ball_two
#print axioms exists_nonstationary_warm_start_mixing_ball_two
#print axioms cubeA
#print axioms cubeb
#print axioms cube
#print axioms mem_cube_iff
#print axioms measurableSet_cube
#print axioms convex_cube
#print axioms ball_half_subset_cube
#print axioms dist_le_of_mem_cube
#print axioms zero_mem_cube
#print axioms volume_cube_ne_zero
#print axioms volume_cube_ne_top
#print axioms volume_ball_half_lt_volume_cube
#print axioms isWarm_uniformOn_ball_half_cube
#print axioms uniformOn_ball_half_ne_uniformOn_cube
#print axioms exists_nonstationary_warm_start_mixing_cube

end Arlib.MarkovChains
