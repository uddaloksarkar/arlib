/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.MetropolisConductanceSharp
import Arlib.MarkovChains.Continuous.LensSharp
import Arlib.MarkovChains.Continuous.ConvexBodyMixing

/-!
# The local-conductance floor `hell`: no uniform value exists on the consumer's class

`Arlib.conductance_metropolisGaussian_sharp_sqrt_ge_of_convex`
(`Arlib/Convexity/OneDimSharp.lean:1073`) is unconditional — `hiso` is discharged — but it
still carries two hypotheses about the *local conductance*
`ℓ(x) = vol(B(x,δ) ∩ K)/vol(δBₙ)`:

    hell   : ∀ x ∈ K, ofReal θ ≤ ell K δ x
    hfloor : 1 ≤ 20 · e^{-(2Rδ+δ²)/(2σ²)} · (1/4) · θ

`hfloor` forces `θ ≥ 1/5` (`Arlib.MarkovChains.floor_quarter_iff` plus
`Arlib.MarkovChains.acceptance_le_one`), so `hell` must hold with `θ ≥ 1/5`.  The
Gaussian-cooling consumer (`Ttc/Volume/CVInstantiate.lean:148,153`) quantifies over **all**
convex `K` with `Metric.ball 0 1 ⊆ K` and `volume K ≠ ⊤`.

**This file settles, by machine-checked counterexample, that no such `θ` exists on that
class from dimension 3 on, and that the obstruction is a corner.**

## The answer to "is a uniform `θ ≳ 1/5` achievable?" — no, and the rate is `2⁻ⁿ`

`two_pow_card_mul_ell_le_one` : if `k` of the closed coordinate half-spaces `{y j ≤ x j}`
support `K` at `x`, then `ell K δ x ≤ 2⁻ᵏ`, **at every step size `δ`** — a corner is scale
invariant, so the bound does not depend on `δ` and in particular holds at the operative
`δ = Θ(σ/√n)` of `Arlib.MarkovChains.metropolis_hfloor_forces_step_cap`.  No convexity,
measurability or boundedness is used.  The proof is the reflection group: flipping one
coordinate is a linear isometry (`LinearIsometryEquiv.piLpCongrRight`), hence measure
preserving, and it halves the surviving orthant each time.

The witness is the **cube** `[-1,1]ⁿ` at its all-ones corner
(`two_pow_mul_ell_cube_corner_le_one`, `ell_cube_corner_le`): `ell ≤ 2⁻ⁿ`.  The cube is in
the consumer's class — convex, measurable, `Metric.ball 0 1 ⊆ K` (`ball_subset_cube`),
`0 < vol K < ⊤`, `‖·‖ ≤ √n` on `K`.  Hence `le_two_pow_neg_of_ell_floor_cube`: any `θ`
meeting `hell` on the cube has `θ ≤ 2⁻ⁿ`, and `metropolis_ell_floor_unsatisfiable_on_cube`:
for `n ≥ 3` no `θ` meets `hell` and `hfloor` together.
`exists_convex_body_meeting_all_but_ell_floor` shows every *other* binder of the headline
(`hσ, hδ, hδσ, hR, hK, hKc, hKR, hKtop, hK0, hRσ`) is met at `σ = 1`, `δ = 1/(8√n)`,
`R = √n`, so the failure is attributable to the local-conductance floor alone.

**No smoothing of the constant helps.**  The best pointwise floor proved anywhere in the
repository, `Arlib.MarkovChains.le_ell_of_convex_of_ball_subset`
(`ConvexBodyMixing.lean:93`), reads `θ = (1/(1+2R))ⁿ` on this class
(`le_ell_of_ball_subset_of_radius`), and `R ≥ 1` is forced by `ball 0 1 ⊆ K`
(`one_le_of_ball_subset_of_radius`), so that floor is at most `3⁻ⁿ`
(`general_ell_floor_le_three_pow_neg`).  Pointwise floors on this class are exponentially
small; `hfloor` needs a constant.

**Which bodies do satisfy `hell`?**  Only bodies with no corner at the relevant scale.  The
existing non-vacuity witness of the headline (`MetropolisConductanceSharp.lean:505`) uses
`K = B(0,1/2) ⊆ ℝ²` with `δ = 1`, i.e. a body *contained* in the proposal ball — which is
**not** in the consumer's class (it violates `ball 0 1 ⊆ K`).  This file exhibits no
restricted class inside the consumer's class on which `hell` holds with `θ ≥ 1/5`, and §5
shows why one should not be expected: `R ≥ 1` alone already caps every floor of the proved
shape at `3⁻ⁿ`.

## What survives: the *average*, not the infimum

`isSmooth_of_ball_subset` — **every** convex `K` with `Metric.ball 0 1 ⊆ K` is
`(δ, 1 − (1−δ)ⁿ)`-smooth in the sense of `Arlib.MarkovChains.IsSmooth`, i.e.
`(1−δ)ⁿ·vol K ≤ ∫_K ℓ`, for every `0 < δ < 1`.  `IsSmooth` constrains the **average** of `ℓ`
and is blind to the corner where the infimum collapses; the witness is the homothety
`(1−δ)·K`, on which `B(x,δ) ⊆ K` and hence `ℓ = 1`.  This generalizes
`Arlib.MarkovChains.isSmooth_unitBall` (`BallWalk.lean:580`) from the unit ball to the whole
class, and it is the hypothesis `Arlib.MarkovChains.tvLe_ellProb_uniformOn`
(`SpeedyToUniform.lean:207`) consumes.  `cube_smooth_but_no_pointwise_floor` states the
contrast on one and the same body.

**This is a statement about `IsSmooth` only.**  It is *not* a conductance bound, and nothing
here discharges the speedy walk's own `hiso`.  That binder is the speedy route's remaining
obstruction, and it is a different one: `Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex`
(`StarPolar.lean:626`) requires *both* `hrev : IsReversible (speedyWalk K δ) pi` — and the only
measures proved reversible for `speedyWalk` are `ellMeasure K δ` and its scalar multiples
(`SpeedyWalk.lean:379, 403`) — *and* `hiso` for the density `h` that generates `pi`; whereas the
only n-dimensional isoperimetric inequality proved unconditionally in this repository,
`Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` (`OneDimSharp.lean:1040`), is proved for the
fixed density `Set.indicator K (gaussianWeightReal (σ^2))`, not for the `ℓ`-weighted one.  No
instantiation of `conductance_speedyWalk_ge_of_convex` occurs anywhere in the repository.

The one conductance bound that *is* unconditional on a general convex body is
`Arlib.MarkovChains.conductance_ballWalk_convex` (`ConvexBodyMixing.lean:196`), whose constants
`(γ/(γ+D))ⁿ` and `2⁻ⁿ/D` are exponentially small — and §4 shows that exponential cost is
**forced** for any bound routed through a pointwise `hell`, not an artefact of an unoptimised
lemma.

## The kernel bridge

`bridge_multiplier_le_two_pow_neg_on_cube` — the multiplier `a·ℓ(x)` of
`Arlib.MarkovChains.acceptance_mul_ell_mul_speedyWalk_le_metropolisGaussian`
(`LensSharp.lean:695`) is at most `2⁻ⁿ` at the cube's corner, since `a ≤ 1`.  The bridge is
one-sided, so transporting a *lower* bound on `speedyWalk` to `metropolisGaussian` through it
costs `inf_x a·ℓ(x)`; on the cube that is exponentially small.  The bridge therefore does not
rescue the Metropolis conductance bound on this class.

## Scope

Nothing here is a mixing-time or polynomial-time statement, and none of it may be quoted as
one.  Nothing here refutes `Arlib.conductance_metropolisGaussian_sharp_sqrt_ge_of_convex` —
that theorem is true; this file shows its hypotheses are **unsatisfiable** on a body of the
class its intended consumer needs, i.e. that it is vacuous there.  There is no `def`,
`structure`, `class` or `axiom` in this file; every declaration is a `theorem`.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1. Reflection in a coordinate hyperplane -/

/-- Coordinate evaluation on `EuclideanSpace` is measurable. -/
theorem measurable_coord (j : Fin n) :
    Measurable fun w : EuclideanSpace ℝ (Fin n) => w j :=
  (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable

/-- The closed coordinate half-space `{w | w j ≤ 0}` is measurable. -/
theorem measurableSet_coord_nonpos (j : Fin n) :
    MeasurableSet {w : EuclideanSpace ℝ (Fin n) | w j ≤ 0} :=
  measurableSet_le (measurable_coord j) measurable_const

/-- The coordinate hyperplane `{w | w j = 0}` is Lebesgue-null. -/
theorem volume_coord_eq_zero_eq_zero (j : Fin n) :
    volume {w : EuclideanSpace ℝ (Fin n) | w j = 0} = 0 := by
  have hne : (LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (ι := Fin n) j)) ≠ ⊤ := by
    intro h
    have : (EuclideanSpace.single j (1 : ℝ)) ∈
        LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (ι := Fin n) j) := by
      rw [h]; trivial
    simp [LinearMap.mem_ker] at this
  have := Measure.addHaar_submodule (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (ι := Fin n) j)) hne
  convert this using 2
  ext w
  simp [LinearMap.mem_ker]

/-- The intersection of finitely many closed coordinate half-spaces is measurable. -/
theorem measurableSet_coord_orthant (s : Finset (Fin n)) :
    MeasurableSet {w : EuclideanSpace ℝ (Fin n) | ∀ j ∈ s, w j ≤ 0} := by
  have h : {w : EuclideanSpace ℝ (Fin n) | ∀ j ∈ s, w j ≤ 0}
      = ⋂ j ∈ (s : Set (Fin n)), {w : EuclideanSpace ℝ (Fin n) | w j ≤ 0} := by
    ext w; simp
  rw [h]
  exact MeasurableSet.biInter s.countable_toSet fun j _ => measurableSet_coord_nonpos j

/-- **The `2⁻ᵏ` orthant bound.**  A ball centred at the origin meets the intersection of the
`k` closed coordinate half-spaces `{w j ≤ 0}`, `j ∈ s`, in at most a `2⁻ᵏ` fraction of its
volume, `k = s.card`.

The proof is the reflection group: flipping one coordinate not yet in `s` is a linear
isometry, hence measure preserving, and it exchanges the two halves of the already-cut set
while fixing the ball and the earlier cuts.  The two halves overlap in a coordinate
hyperplane, which is null. -/
theorem two_pow_card_mul_volume_ball_inter_orthant_le (δ : ℝ) (s : Finset (Fin n)) :
    2 ^ s.card *
        volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ ∩ {w | ∀ j ∈ s, w j ≤ 0})
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    set B : Set (EuclideanSpace ℝ (Fin n)) := ball 0 δ with hBdef
    set Q : Set (EuclideanSpace ℝ (Fin n)) := {w | ∀ j ∈ s, w j ≤ 0} with hQdef
    have hBm : MeasurableSet B := measurableSet_ball
    have hQm : MeasurableSet Q := measurableSet_coord_orthant s
    set D : Set (EuclideanSpace ℝ (Fin n)) := B ∩ Q with hDdef
    have hDm : MeasurableSet D := hBm.inter hQm
    set N : Set (EuclideanSpace ℝ (Fin n)) := D ∩ {w | w i ≤ 0} with hNdef
    set P : Set (EuclideanSpace ℝ (Fin n)) := D ∩ {w | 0 ≤ w i} with hPdef
    have hPm : MeasurableSet P :=
      hDm.inter (measurableSet_le measurable_const (measurable_coord i))
    -- the reflection in the `i`-th coordinate hyperplane
    set r : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
      LinearIsometryEquiv.piLpCongrRight 2
        (fun j => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
      with hrdef
    have hrcoord : ∀ (w : EuclideanSpace ℝ (Fin n)) (j : Fin n),
        r w j = if j = i then -(w j) else w j := by
      intro w j
      rw [hrdef]
      by_cases h : j = i <;> simp [h]
    have hrnorm : ∀ w : EuclideanSpace ℝ (Fin n), ‖r w‖ = ‖w‖ := fun w => r.norm_map w
    have hpre : r ⁻¹' P = N := by
      ext w
      simp only [Set.mem_preimage, hPdef, hNdef, hDdef, hBdef, hQdef, Set.mem_inter_iff,
        Set.mem_setOf_eq, mem_ball, dist_zero_right]
      constructor
      · rintro ⟨⟨hb, hq⟩, hc⟩
        refine ⟨⟨by rwa [hrnorm] at hb, fun j hj => ?_⟩, ?_⟩
        · have := hq j hj
          rwa [hrcoord w j, if_neg (by rintro rfl; exact hi hj)] at this
        · have := hc
          rwa [hrcoord w i, if_pos rfl, neg_nonneg] at this
      · rintro ⟨⟨hb, hq⟩, hc⟩
        refine ⟨⟨by rwa [hrnorm], fun j hj => ?_⟩, ?_⟩
        · rw [hrcoord w j, if_neg (by rintro rfl; exact hi hj)]; exact hq j hj
        · rw [hrcoord w i, if_pos rfl, neg_nonneg]; exact hc
    have hNP : volume N = volume P := by
      rw [← hpre]
      exact r.measurePreserving.measure_preimage hPm.nullMeasurableSet
    have hunion : N ∪ P = D := by
      ext w
      simp only [hNdef, hPdef, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; rcases le_total (w i) 0 with hc | hc
        · exact Or.inl ⟨h, hc⟩
        · exact Or.inr ⟨h, hc⟩
    have hzero : volume (N ∩ P) = 0 := by
      refine measure_mono_null ?_ (volume_coord_eq_zero_eq_zero i)
      rintro w ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
      exact le_antisymm h1 h2
    have hkey : volume D = 2 * volume N := by
      have h := measure_union_add_inter (μ := volume) N hPm
      rw [hunion, hzero, add_zero, ← hNP] at h
      rw [h]; ring
    have hins : B ∩ {w : EuclideanSpace ℝ (Fin n) | ∀ j ∈ insert i s, w j ≤ 0} = N := by
      ext w
      simp only [hNdef, hDdef, hQdef, Set.mem_inter_iff, Set.mem_setOf_eq,
        Finset.mem_insert, forall_eq_or_imp]
      tauto
    rw [hins, Finset.card_insert_of_notMem hi, pow_succ]
    calc 2 ^ s.card * 2 * volume N = 2 ^ s.card * (2 * volume N) := by ring
      _ = 2 ^ s.card * volume D := by rw [hkey]
      _ ≤ volume B := ih

/-! ## 2. A `k`-fold corner costs the local conductance a factor `2⁻ᵏ` -/

/-- **The corner bound.**  If `k = s.card` of the closed coordinate half-spaces
`{y | y j ≤ x j}`, `j ∈ s`, all support `K` at `x` — that is, `K` lies in all of them —
then `ell K δ x ≤ 2⁻ᵏ`, at **every** step size `δ`.

No convexity, no measurability, no boundedness is used: only that `K` is squeezed into an
axis-aligned corner at `x`.  The bound is `δ`-free because a corner is scale invariant. -/
theorem two_pow_card_mul_ell_le_one {K : Set (EuclideanSpace ℝ (Fin n))} (δ : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (s : Finset (Fin n))
    (hsupp : ∀ y ∈ K, ∀ j ∈ s, y j ≤ x j) :
    2 ^ s.card * ell K δ x ≤ 1 := by
  have hpre : (fun w : EuclideanSpace ℝ (Fin n) => x + w) ⁻¹' (ball x δ ∩ K)
      ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) δ ∩ {w | ∀ j ∈ s, w j ≤ 0} := by
    rintro w ⟨hb, hk⟩
    refine ⟨?_, fun j hj => ?_⟩
    · rw [mem_ball, dist_zero_right]
      rw [mem_ball, dist_eq_norm] at hb
      simpa using hb
    · have h := hsupp _ hk j hj
      simp only [PiLp.add_apply] at h
      linarith
  have h1 : volume (ball x δ ∩ K)
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ ∩ {w | ∀ j ∈ s, w j ≤ 0}) := by
    rw [← measure_preimage_add (volume : Measure (EuclideanSpace ℝ (Fin n))) x (ball x δ ∩ K)]
    exact measure_mono hpre
  have h2 : 2 ^ s.card * volume (ball x δ ∩ K)
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) :=
    le_trans (by gcongr) (two_pow_card_mul_volume_ball_inter_orthant_le δ s)
  rw [ell_apply, volume_ball_eq x δ, ← mul_div_assoc]
  exact ENNReal.div_le_of_le_mul (by rwa [one_mul])

/-! ## 3. The cube: a body of the consumer's class whose `ell` is `≤ 2⁻ⁿ` -/

/-- The cube `[-1,1]ⁿ` is convex. -/
theorem convex_supNormCube :
    Convex ℝ {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} := by
  intro a ha b hb t u ht hu htu j
  have h : (t • a + u • b) j = t * a j + u * b j := by simp
  rw [h]
  calc |t * a j + u * b j| ≤ |t * a j| + |u * b j| := abs_add_le _ _
    _ = t * |a j| + u * |b j| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg hu]
    _ ≤ t * 1 + u * 1 := by
        have := ha j; have := hb j; nlinarith [abs_nonneg (a j), abs_nonneg (b j)]
    _ = 1 := by rw [mul_one, mul_one, htu]

/-- The cube `[-1,1]ⁿ` is measurable. -/
theorem measurableSet_supNormCube :
    MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} := by
  have h : {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}
      = ⋂ j : Fin n, {y : EuclideanSpace ℝ (Fin n) | |y j| ≤ 1} := by
    ext y; simp
  rw [h]
  exact MeasurableSet.iInter fun j =>
    measurableSet_le (measurable_coord j).abs measurable_const

/-- A coordinate of a Euclidean vector is bounded by its norm. -/
theorem abs_coord_le_norm (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) : |x j| ≤ ‖x‖ := by
  have h := EuclideanSpace.norm_eq x
  have hle : ‖x j‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ j)
  have hnn : (0 : ℝ) ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have : |x j| ≤ Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
    rw [show |x j| = Real.sqrt (‖x j‖ ^ 2) by
      rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs, abs_abs]]
    exact Real.sqrt_le_sqrt hle
  rwa [← h] at this

/-- The unit ball is contained in the cube `[-1,1]ⁿ`. -/
theorem ball_subset_cube :
    ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} := by
  intro y hy j
  rw [mem_ball, dist_zero_right] at hy
  exact le_trans (abs_coord_le_norm y j) hy.le

/-- Every point of the cube `[-1,1]ⁿ` has norm at most `√n`. -/
theorem norm_le_sqrt_of_mem_cube {y : EuclideanSpace ℝ (Fin n)} (hy : ∀ j, |y j| ≤ 1) :
    ‖y‖ ≤ Real.sqrt n := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ j, ‖y j‖ ^ 2 ≤ ∑ _j : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have := hy j
        rw [Real.norm_eq_abs]
        nlinarith [abs_nonneg (y j)]
    _ = (n : ℝ) := by simp

/-- **The corner of the cube.**  `ell` at the all-ones corner of `[-1,1]ⁿ` is at most `2⁻ⁿ`,
for every step size `δ`. -/
theorem two_pow_mul_ell_cube_corner_le_one (δ : ℝ) :
    2 ^ n * ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ
        (WithLp.toLp 2 fun _ => (1 : ℝ)) ≤ 1 := by
  have h := two_pow_card_mul_ell_le_one
    (K := {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1})
    (x := (WithLp.toLp 2 fun _ => (1 : ℝ) : EuclideanSpace ℝ (Fin n)))
    δ Finset.univ (by
      intro y hy j _
      have := hy j
      cases abs_le.1 this with
      | intro _ h2 => exact h2)
  simpa using h

/-- **The corner of the cube, in `2⁻ⁿ` form.** -/
theorem ell_cube_corner_le (δ : ℝ) :
    ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ (WithLp.toLp 2 fun _ => (1 : ℝ))
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  have h2 : (2 : ℝ≥0∞) ^ n * ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ
      (WithLp.toLp 2 fun _ => (1 : ℝ)) ≤ 1 := two_pow_mul_ell_cube_corner_le_one (n := n) δ
  have hinv : ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ
      (WithLp.toLp 2 fun _ => (1 : ℝ)) ≤ ((2 : ℝ≥0∞) ^ n)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le, mul_comm]
    exact h2
  refine le_trans hinv (le_of_eq ?_)
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1 / 2), hhalf, ENNReal.inv_pow]

/-- **The refutation, in real-number form.**  Any `θ` that is a global `ell`-floor for the
cube `[-1,1]ⁿ` at any step size satisfies `θ ≤ 2⁻ⁿ`. -/
theorem le_two_pow_neg_of_ell_floor_cube {δ θ : ℝ}
    (hell : ∀ x ∈ {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1},
      ENNReal.ofReal θ ≤ ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ x) :
    θ ≤ (1 / 2 : ℝ) ^ n := by
  have hmem : (WithLp.toLp 2 fun _ => (1 : ℝ) : EuclideanSpace ℝ (Fin n))
      ∈ {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} := by
    intro j; simp
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1
    (le_trans (hell _ hmem) (ell_cube_corner_le δ))

/-! ## 4. `hell` and `hfloor` are jointly unsatisfiable from dimension 3 on -/

/-- **`hfloor` needs `θ ≳ 1/5`, and `2⁻ⁿ < 1/5` from `n = 3`.**

`hfloor` is `1 ≤ 20·a·(1/4)·θ` with `a = e^{-(2Rδ+δ²)/(2σ²)} ∈ (0,1]`, i.e. `1/5 ≤ a·θ`
(`Arlib.MarkovChains.floor_quarter_iff`).  Since `a ≤ 1`
(`Arlib.MarkovChains.acceptance_le_one`) this forces `θ ≥ 1/5`, which `θ ≤ 2⁻ⁿ ≤ 1/8`
contradicts. -/
theorem not_hfloor_of_le_two_pow_neg (hn : 3 ≤ n) {σ δ R θ : ℝ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hθ : θ ≤ (1 / 2 : ℝ) ^ n) :
    ¬ (1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ) := by
  intro hfloor
  set a : ℝ := Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) with hadef
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := acceptance_le_one hR hδ (by positivity)
  have h5 : 1 / 5 ≤ a * θ := (floor_quarter_iff a θ).1 hfloor
  have h8 : (1 / 2 : ℝ) ^ n ≤ 1 / 8 := by
    calc (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = 1 / 8 := by norm_num
  have hθpos : 0 < θ := by nlinarith
  nlinarith

/-- **The headline negative.**  For every `n ≥ 3`, every step size `δ ≥ 0`, every radius
bound `R ≥ 0` and every `σ > 0`, the pair of hypotheses

    hell   : ∀ x ∈ K, ofReal θ ≤ ell K δ x
    hfloor : 1 ≤ 20·e^{-(2Rδ+δ²)/(2σ²)}·(1/4)·θ

carried by `Arlib.conductance_metropolisGaussian_sharp_sqrt_ge_of_convex`
(`Arlib/Convexity/OneDimSharp.lean:1073`) is **contradictory** at `K = [-1,1]ⁿ`, a convex
body of the class the Gaussian-cooling consumer quantifies over (`Metric.ball 0 1 ⊆ K`,
`volume K ≠ ⊤`).  So that theorem, although unconditional, is **vacuous on the cube**. -/
theorem metropolis_ell_floor_unsatisfiable_on_cube (hn : 3 ≤ n) {σ δ R θ : ℝ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hell : ∀ x ∈ {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1},
      ENNReal.ofReal θ ≤ ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ) :
    False :=
  not_hfloor_of_le_two_pow_neg hn hσ hδ hR (le_two_pow_neg_of_ell_floor_cube hell) hfloor

/-- **Attribution: the cube meets every other hypothesis.**  At `n ≥ 3`, `σ = 1`,
`δ = 1/(8√n)`, `R = √n` the cube `[-1,1]ⁿ` satisfies `hσ`, `hδ`, `hδσ`, `hR`, `hK`, `hKc`,
`hKR`, `hKtop`, `hK0`, `hRσ` — every binder of
`Arlib.conductance_metropolisGaussian_sharp_sqrt_ge_of_convex` — and also the consumer's
`Metric.ball 0 1 ⊆ K`; and yet **no** `θ` satisfies `hell` and `hfloor` together.  The
failure is therefore attributable to the local-conductance floor alone, not to the step-size
cap, the radius bound, or convexity. -/
theorem exists_convex_body_meeting_all_but_ell_floor (hn : 3 ≤ n) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (σ δ R : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      0 < σ ∧ 0 < δ ∧ δ ≤ σ / (8 * Real.sqrt n) ∧ 0 ≤ R ∧
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ y ∈ K, ‖y‖ ≤ R) ∧
      volume K ≠ ⊤ ∧ volume K ≠ 0 ∧
      ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K ∧
      Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n ∧
      x ∈ K ∧ ell K δ x ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ∧
      (∀ θ : ℝ, (∀ y ∈ K, ENNReal.ofReal θ ≤ ell K δ y) →
        ¬ (1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  refine ⟨{y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, 1, 1 / (8 * Real.sqrt n),
    Real.sqrt n, WithLp.toLp 2 fun _ => (1 : ℝ), one_pos, by positivity, by
      simp, Real.sqrt_nonneg _, measurableSet_supNormCube, convex_supNormCube,
    fun y hy => norm_le_sqrt_of_mem_cube hy, ?_, ?_, ball_subset_cube, ?_,
    (by intro j; simp), ell_cube_corner_le _, ?_⟩
  · -- finite volume: the cube sits inside a closed ball
    refine ne_of_lt (lt_of_le_of_lt (measure_mono
      (show {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}
          ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) from
        fun y hy => mem_closedBall_zero_iff.2 (norm_le_sqrt_of_mem_cube hy)))
      measure_closedBall_lt_top)
  · -- positive volume: the cube contains the unit ball
    exact ne_of_gt (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 one_pos)
      (measure_mono ball_subset_cube))
  · -- `hRσ`
    have h3 : Real.sqrt 3 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith
  · exact fun θ hθ => not_hfloor_of_le_two_pow_neg hn one_pos (by positivity)
      (Real.sqrt_nonneg _) (le_two_pow_neg_of_ell_floor_cube hθ)

/-- **The other `hfloor` shape.**  `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`
(`MetropolisConductanceSharp.lean:431`) states `hfloor` with `(1 − 1/n)ⁿ` in place of `1/4`.
Since `(1 − 1/n)ⁿ ≤ 1`, that shape forces `θ ≥ 1/20`, which `θ ≤ 2⁻ⁿ ≤ 1/32` contradicts from
`n = 5` on. -/
theorem not_hfloor_dim_of_le_two_pow_neg (hn : 5 ≤ n) {σ δ R θ : ℝ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hθ : θ ≤ (1 / 2 : ℝ) ^ n) :
    ¬ (1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 - 1 / (n : ℝ)) ^ n * θ) := by
  intro hfloor
  have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv1 : 1 / (n : ℝ) < 1 := by rw [div_lt_one hnpos]; linarith
  have hinv0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hc0 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by linarith
  have hcpos : (0 : ℝ) < (1 - 1 / (n : ℝ)) ^ n := pow_pos hc0 n
  have hc1 : (1 - 1 / (n : ℝ)) ^ n ≤ 1 := pow_le_one₀ hc0.le (by linarith)
  set a : ℝ := Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) with hadef
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := acceptance_le_one hR hδ (by positivity)
  set b : ℝ := a * (1 - 1 / (n : ℝ)) ^ n with hbdef
  have hb0 : 0 < b := mul_pos ha0 hcpos
  have hb1 : b ≤ 1 := mul_le_one₀ ha1 hcpos.le hc1
  have key : 1 ≤ 20 * b * θ := by rw [hbdef, ← mul_assoc]; exact hfloor
  have h32 : (1 / 2 : ℝ) ^ n ≤ 1 / 32 := by
    calc (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 5 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = 1 / 32 := by norm_num
  have hθpos : 0 < θ := by nlinarith
  nlinarith

/-- **The headline negative for the `(1 − 1/n)ⁿ` shape**, at the cube, from `n = 5` on. -/
theorem metropolis_ell_floor_dim_unsatisfiable_on_cube (hn : 5 ≤ n) {σ δ R θ : ℝ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hell : ∀ x ∈ {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1},
      ENNReal.ofReal θ ≤ ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))
      * (1 - 1 / (n : ℝ)) ^ n * θ) :
    False :=
  not_hfloor_dim_of_le_two_pow_neg hn hσ hδ hR (le_two_pow_neg_of_ell_floor_cube hell) hfloor

/-! ## 5. The best available *pointwise* floor is exponentially small too -/

/-- **The repository's proved floor, read at the consumer's class.**  Instantiating
`Arlib.MarkovChains.le_ell_of_convex_of_ball_subset` (`ConvexBodyMixing.lean:93`) at
`γ = 1`, `c = 0`, `D = 2R` gives, for every convex `K` with `Metric.ball 0 1 ⊆ K` and
`‖·‖ ≤ R` on `K`, the floor `θ = (1/(1+2R))ⁿ` at every step `0 < δ ≤ 1`. -/
theorem le_ell_of_ball_subset_of_radius {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {R : ℝ} (hKR : ∀ x ∈ K, ‖x‖ ≤ R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ x ∈ K, ENNReal.ofReal ((1 / (1 + 2 * R)) ^ n) ≤ ell K δ x := by
  have hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ 2 * R := by
    intro x hx y hy
    calc dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact norm_sub_le x y
      _ ≤ 2 * R := by have := hKR x hx; have := hKR y hy; linarith
  have h := le_ell_of_convex_of_ball_subset hKc (γ := 1) one_pos hball hD hδ hδ1
  simpa using h

/-- The radius bound of a body containing the unit ball is at least `1`. -/
theorem one_le_of_ball_subset_of_radius (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {R : ℝ} (hKR : ∀ x ∈ K, ‖x‖ ≤ R) : 1 ≤ R := by
  have hj : (0 : ℕ) < n := hn
  refine le_of_forall_lt_imp_le_of_dense fun t ht => ?_
  rcases le_or_gt t 0 with h0 | h0
  · exact le_trans h0 (le_trans (norm_nonneg _)
      (hKR _ (hball (by rw [mem_ball, dist_self]; norm_num))))
  · set x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hj⟩ t with hxdef
    have hnx : ‖x‖ = t := by
      rw [hxdef, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos h0]
    have hxK : x ∈ K := hball (by rw [mem_ball, dist_zero_right, hnx]; exact ht)
    rw [← hnx]; exact hKR x hxK

/-- **The proved general floor can never satisfy `hfloor` either.**  With `R ≥ 1` forced by
`Metric.ball 0 1 ⊆ K`, the floor of `le_ell_of_ball_subset_of_radius` is at most `3⁻ⁿ`. -/
theorem general_ell_floor_le_three_pow_neg {R : ℝ} (hR : 1 ≤ R) :
    (1 / (1 + 2 * R)) ^ n ≤ (1 / 3 : ℝ) ^ n := by
  refine pow_le_pow_left₀ (by positivity) ?_ n
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-! ## 6. What survives: the **average** local conductance, on the whole class -/

/-- **Every convex body containing the unit ball is `(δ, 1 − (1−δ)ⁿ)`-smooth**, for every
step size `0 < δ < 1`.

This is the positive counterpart of §4, and it is what makes the *speedy-walk* route work
where the Metropolis route does not: `Arlib.MarkovChains.IsSmooth` constrains the **average**
of `ell` over `K` (`(1−s)·vol K ≤ ∫_K ℓ`), not its infimum, and the average is insensitive to
the corner where the infimum collapses.  `Arlib.MarkovChains.isSmooth_unitBall`
(`BallWalk.lean:580`) is the special case `K = B(0,1)`; the docstring of `IsSmooth` records
that it "is a hypothesis a caller supplies, never a conclusion this file provides for a
general `K`" — this theorem provides it for the whole class the Gaussian-cooling consumer
quantifies over.

The witness is the homothety `(1−δ)·K`, on which `B(x,δ) ⊆ K` and hence `ℓ = 1`; its volume
is `(1−δ)ⁿ·vol K` by `Measure.addHaar_smul`. -/
theorem isSmooth_of_ball_subset {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    IsSmooth K δ (1 - ENNReal.ofReal ((1 - δ) ^ n)) := by
  have hc0 : (0 : ℝ) < 1 - δ := by linarith
  have hc : (1 - δ : ℝ) ≠ 0 := ne_of_gt hc0
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    hball (by rw [mem_ball, dist_self]; norm_num)
  have hballsub : ∀ y ∈ K, ball ((1 - δ) • y) δ ⊆ K := by
    intro y hy z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hw : δ⁻¹ • (z - (1 - δ) • y) ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hδ)]
      calc δ⁻¹ * ‖z - (1 - δ) • y‖ < δ⁻¹ * δ := mul_lt_mul_of_pos_left hz (inv_pos.2 hδ)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hδ)
    have hmem := hKc hy (hball hw) hc0.le hδ.le (by ring)
    have heq : (1 - δ) • y + δ • (δ⁻¹ • (z - (1 - δ) • y)) = z := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hδ), one_smul]; abel
    rwa [heq] at hmem
  set S : Set (EuclideanSpace ℝ (Fin n)) := (1 - δ) • K with hSdef
  have hSm : MeasurableSet S := by
    have hSeq : S = (fun y : EuclideanSpace ℝ (Fin n) => (1 - δ)⁻¹ • y) ⁻¹' K := by
      rw [hSdef]; ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [Set.mem_preimage, smul_smul, inv_mul_cancel₀ hc, one_smul]
        exact hy
      · intro hz
        exact ⟨(1 - δ)⁻¹ • z, hz, by simp [smul_smul, mul_inv_cancel₀ hc]⟩
    rw [hSeq]
    exact hK.preimage (measurable_const_smul _)
  have hSK : S ⊆ K := by
    rintro x ⟨y, hy, rfl⟩
    have := hKc hy h0K hc0.le hδ.le (by ring)
    simpa using this
  have hell1 : ∀ x ∈ S, ell K δ x = 1 := by
    rintro x ⟨y, hy, rfl⟩
    rw [ell_apply, Set.inter_eq_self_of_subset_left (hballsub y hy)]
    exact ENNReal.div_self (Metric.measure_ball_pos volume _ hδ).ne' measure_ball_lt_top.ne
  have hvolS : volume S = ENNReal.ofReal ((1 - δ) ^ n) * volume K := by
    rw [hSdef, Measure.addHaar_smul, finrank_euclideanSpace_fin,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 - δ) ^ n)]
  have hint : volume S ≤ ∫⁻ x in K, ell K δ x := by
    calc volume S = ∫⁻ _ in S, 1 := (setLIntegral_one S).symm
      _ ≤ ∫⁻ x in S, ell K δ x := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict hSm] with x hx
          rw [hell1 x hx]
      _ ≤ ∫⁻ x in K, ell K δ x := lintegral_mono' (Measure.restrict_mono hSK le_rfl) le_rfl
  have hle1 : ENNReal.ofReal ((1 - δ) ^ n) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (pow_le_one₀ hc0.le (by linarith))
  rw [IsSmooth, ENNReal.sub_sub_cancel (by simp) hle1, ← hvolS]
  exact hint

/-- **The contrast, on one and the same body.**  On the cube `[-1,1]ⁿ` the *pointwise*
`ell`-floor is at most `2⁻ⁿ` — exponentially small for **every** `δ`, since a corner is
scale invariant — while the *average* floor is `(1−δ)ⁿ`, which is `≥ 1 − nδ` by Bernoulli and
hence a constant whenever `δ = O(1/n)`.  (At the operative `δ = Θ(σ/√n)` the average floor is
`(1−δ)ⁿ ≈ e^{−Θ(σ√n)}`, which is itself small unless `σ = O(1/√n)`; the point here is only
that the two quantities are different, and that the average is `δ`-sensitive where the
infimum is not.)  `hell` reads the infimum; `Arlib.MarkovChains.IsSmooth` reads the
average. -/
theorem cube_smooth_but_no_pointwise_floor {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    IsSmooth {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ
        (1 - ENNReal.ofReal ((1 - δ) ^ n)) ∧
      ∀ θ : ℝ, (∀ x ∈ {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1},
        ENNReal.ofReal θ ≤ ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ x) →
        θ ≤ (1 / 2 : ℝ) ^ n :=
  ⟨isSmooth_of_ball_subset measurableSet_supNormCube convex_supNormCube ball_subset_cube hδ hδ1,
    fun _ h => le_two_pow_neg_of_ell_floor_cube h⟩

/-! ## 7. The kernel bridge carries the same exponential loss -/

/-- **The `a·ℓ(x)` multiplier of the kernel bridge is `≤ 2⁻ⁿ` at the cube's corner.**

`Arlib.MarkovChains.acceptance_mul_ell_mul_speedyWalk_le_metropolisGaussian`
(`LensSharp.lean:695`) proves `a·ℓ(x)·speedyWalk K δ x A ≤ metropolisGaussian K δ s x A`.
Transporting a *lower* bound on the speedy walk to the Metropolis kernel through it therefore
costs `inf_x a·ℓ(x)`, and on the cube that infimum is at most `2⁻ⁿ`, since `a ≤ 1`
(`Arlib.MarkovChains.acceptance_le_one`).  So the bridge does **not** rescue the Metropolis
conductance bound: it converts an `Ω(δ/(σ√n))` speedy bound into an `Ω(2⁻ⁿ·δ/(σ√n))`
Metropolis bound. -/
theorem bridge_multiplier_le_two_pow_neg_on_cube {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 ≤ δ)
    (hR : 0 ≤ R) :
    ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)))
        * ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ
            (WithLp.toLp 2 fun _ => (1 : ℝ))
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  have ha : ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (acceptance_le_one hR hδ (by positivity))
  calc ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)))
          * ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ
              (WithLp.toLp 2 fun _ => (1 : ℝ))
      ≤ 1 * ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ
              (WithLp.toLp 2 fun _ => (1 : ℝ)) := by gcongr
    _ = ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ
              (WithLp.toLp 2 fun _ => (1 : ℝ)) := one_mul _
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := ell_cube_corner_le δ

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.measurable_coord
#print axioms Arlib.MarkovChains.measurableSet_coord_nonpos
#print axioms Arlib.MarkovChains.volume_coord_eq_zero_eq_zero
#print axioms Arlib.MarkovChains.measurableSet_coord_orthant
#print axioms Arlib.MarkovChains.two_pow_card_mul_volume_ball_inter_orthant_le
#print axioms Arlib.MarkovChains.two_pow_card_mul_ell_le_one
#print axioms Arlib.MarkovChains.convex_supNormCube
#print axioms Arlib.MarkovChains.measurableSet_supNormCube
#print axioms Arlib.MarkovChains.abs_coord_le_norm
#print axioms Arlib.MarkovChains.ball_subset_cube
#print axioms Arlib.MarkovChains.norm_le_sqrt_of_mem_cube
#print axioms Arlib.MarkovChains.two_pow_mul_ell_cube_corner_le_one
#print axioms Arlib.MarkovChains.ell_cube_corner_le
#print axioms Arlib.MarkovChains.le_two_pow_neg_of_ell_floor_cube
#print axioms Arlib.MarkovChains.not_hfloor_of_le_two_pow_neg
#print axioms Arlib.MarkovChains.metropolis_ell_floor_unsatisfiable_on_cube
#print axioms Arlib.MarkovChains.exists_convex_body_meeting_all_but_ell_floor
#print axioms Arlib.MarkovChains.not_hfloor_dim_of_le_two_pow_neg
#print axioms Arlib.MarkovChains.metropolis_ell_floor_dim_unsatisfiable_on_cube
#print axioms Arlib.MarkovChains.le_ell_of_ball_subset_of_radius
#print axioms Arlib.MarkovChains.one_le_of_ball_subset_of_radius
#print axioms Arlib.MarkovChains.general_ell_floor_le_three_pow_neg
#print axioms Arlib.MarkovChains.isSmooth_of_ball_subset
#print axioms Arlib.MarkovChains.cube_smooth_but_no_pointwise_floor
#print axioms Arlib.MarkovChains.bridge_multiplier_le_two_pow_neg_on_cube

