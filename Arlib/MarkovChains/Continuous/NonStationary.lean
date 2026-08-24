/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.WarmStart
import Arlib.MarkovChains.Continuous.ConvexBodyMixing

/-!
# The finite-time law of the lazy ball walk is not the uniform law — for small `t`

## The gap this file attacks

Every capstone in this development carries the same caveat: the total-variation bound
`law_tv` is *proved*, so no accuracy assumption about the sampler is made, but it was **not**
proved that the finite-time iterate of the lazy ball walk actually *differs* from the uniform
law on the body.  Without such a statement a reader cannot tell whether the sampler's law is
a genuine approximation or has been silently replaced by its own target.

This file proves the difference — **but only for `t` below an explicit, elementary
threshold**, by two independent routes.  Neither route reaches the step count the
development actually runs the chain for.  Read §"Honest scope" before quoting anything here.

## Route 1: support growth (`ballWalkLaw_ne_uniformOn_of_lt`)

One step of `lazy (ballWalk K δ)` moves the current point by strictly less than `δ`
(`lazy_ballWalk_apply_compl_closedBall`): the proposal is drawn from `Metric.ball x δ`, the
rejection atom sits at `x`, and the laziness atom sits at `x`.  Hence a law supported in
`Metric.closedBall c r` is pushed to a law supported in `Metric.closedBall c (r + δ)`, and
by induction the `t`-step law is supported in `Metric.closedBall c (r + t·δ)`
(`measure_compl_closedBall_ballWalkLaw`).  If the body `K` contains a ball `Metric.ball c R`
with

    r + t·δ < R,

then `K` has positive volume outside `Metric.closedBall c (r + t·δ)`, the target charges
that region and the `t`-step law does not, so the two measures are different.

**Range of validity: `t < (R − r)/δ`,** where `r` is the radius of a ball supporting the
start and `R` is the radius of a ball inscribed in `K` around the *same centre*.  The
threshold is `Θ(R/δ)`, and since `R` is at most the inradius of `K`, the Cousins–Vempala
step `δ ≍ γ/√n` in a body with inscribed ball of radius `γ` makes it `O(√n)` — polynomial
in `n`, and in fact only `O(√n)`.

## Route 2: laziness lower bound (`ballWalkLaw_ne_uniformOn_of_lt_inv_pow_mul`)

`lazy P x ≥ ½·δ_x` pointwise, so a single step of the lazy chain retains at least half the
mass of every event (`inv_two_mul_le_step_lazy_apply`) and therefore

    μ_t S  ≥  2^(−t) · μ_0 S      for every measurable `S`

(`inv_pow_mul_le_iterate_lazy_apply`).  If `S` is an event that the start charges much more
heavily than the target, this forces `μ_t ≠ π` for as long as `2^(−t)·μ_0 S > π S`.

**Range of validity: `t < log₂(μ_0 S / π S)`.**  For the half-ball start on the unit ball
(`μ_0 S = 1`, `π S = 2^(−n)`) this is `t < n` — *independent of `δ`*, which is exactly where
it beats Route 1: at `δ = 1` Route 1 gives nothing beyond `t = 0`, while Route 2 still
reaches `t = n − 1`.

## Honest scope — what is NOT proved

The step count this development actually uses is `Ttc.mixSteps`, i.e.
`Arlib.MarkovChains.conductanceMixingTime` at a conductance floor that is **exponentially
small in the dimension**; the resulting `t` is exponentially large in `n`.  Both thresholds
above are far below it: Route 1 reaches `Θ(R/δ)`, which is `O(√n)` in that regime, and
Route 2 reaches `Θ(n)`, while `mixSteps` is `2^(Θ(n))`.

**Nothing in this file establishes that the law at `t = mixSteps` differs from the uniform
law.**  The caveat in the capstone docstrings remains true at that step count and must not
be deleted on the strength of this file.  What is now available is the statement at small
`t`, with the threshold written into the hypothesis so that no reader can mistake its reach.

A route that reached arbitrary `t` would need genuine spectral input — that the lazy chain's
transition operator has no eigenvalue `−1` and that the non-constant part of `μ_0 − π` is not
annihilated in finite time — which is not in this tree and is not attempted here.  Neither
route below is a substitute for it, and neither is presented as one.

## Main results

* `Arlib.MarkovChains.ballWalkLaw` — the `t`-step law of the lazy ball walk.  Definitionally
  equal to `Ttc.ballWalkLaw`, which is the same iterate under a different namespace.
* `Arlib.MarkovChains.measure_compl_closedBall_ballWalkLaw` — Route 1's crux: the support
  grows by at most `δ` per step.
* `Arlib.MarkovChains.ballWalkLaw_ne_uniformOn_of_lt` — **Route 1's headline**, with the
  range `r + t·δ < R` in the statement.
* `Arlib.MarkovChains.inv_pow_mul_le_iterate_lazy_apply` — Route 2's crux: `μ_t ≥ 2^(−t)·μ_0`
  setwise.
* `Arlib.MarkovChains.ballWalkLaw_ne_uniformOn_of_lt_inv_pow_mul` — **Route 2's headline**.
* `Arlib.MarkovChains.exists_two_nonstationary_step_sizes` and
  `Arlib.MarkovChains.exists_two_nonstationary_dimension_ranges` — the two required
  *pairs* of structurally different instances (differing in `δ`), each with the numeric
  thresholds proved strictly positive inside the statement, so that neither headline is a
  theorem about an empty range.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Arlib.MarkovChains

variable {n : ℕ}

/-! ## The law of the chain

`ballWalkLaw K δ mu0 t` is *literally* the `t`-fold iterate of the lazy ball-walk kernel
applied to `mu0`.  Nothing about the uniform law on `K` enters its definition; that is what
makes the `≠` statements below meaningful rather than circular. -/

/-- **The law of the lazy ball walk on `K` with step `δ` after `t` steps from `mu0`.**

This is definitionally `Ttc.ballWalkLaw`, which is the same iterate spelled in the
project namespace; `Arlib` may not import `Ttc`, so the definition is repeated here rather
than shared.  It is an iterate of a Markov kernel — the target `Arlib.uniformOn volume K`
does not appear in it. -/
noncomputable def ballWalkLaw (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (t : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  iterate (lazy (ballWalk K δ)) mu0 t

/-- `ballWalkLaw` is what it says it is: the `t`-th iterate of the lazy ball-walk kernel. -/
theorem ballWalkLaw_eq_iterate (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (t : ℕ) :
    ballWalkLaw K δ mu0 t = iterate (lazy (ballWalk K δ)) mu0 t := rfl

/-- At `t = 0` the law is the start. -/
@[simp] theorem ballWalkLaw_zero (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (mu0 : Measure (EuclideanSpace ℝ (Fin n))) : ballWalkLaw K δ mu0 0 = mu0 := rfl

/-- The recursion: one more step of the lazy walk. -/
@[simp] theorem ballWalkLaw_succ (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (t : ℕ) :
    ballWalkLaw K δ mu0 (t + 1) = step (lazy (ballWalk K δ)) (ballWalkLaw K δ mu0 t) := rfl

/-- The law is a probability measure at every time. -/
instance isProbabilityMeasure_ballWalkLaw (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (mu0 : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure mu0] (t : ℕ) :
    IsProbabilityMeasure (ballWalkLaw K δ mu0 t) :=
  isProbabilityMeasure_iterate _ _ t

/-! ## Route 1, step one: a single step moves the point by less than `δ` -/

/-- **One step of the lazy ball walk cannot leave `Metric.closedBall c (r + δ)` from a point
of `Metric.closedBall c r`.**

All three pieces of `lazy (ballWalk K δ) x` sit within distance `δ` of `x`: the proposal is
supported in `Metric.ball x δ`, the rejection atom is `dirac x`, and the laziness atom is
`dirac x`.  With `dist x c ≤ r` the triangle inequality puts every one of them inside
`Metric.closedBall c (r + δ)`.

`0 ≤ δ` is needed and not removable: it is what makes `Metric.closedBall c r` a subset of
`Metric.closedBall c (r + δ)`, i.e. what keeps the two atoms inside the larger ball. -/
theorem lazy_ballWalk_apply_compl_closedBall {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 ≤ δ) {c x : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hx : x ∈ Metric.closedBall c r) :
    lazy (ballWalk K δ) x (Metric.closedBall c (r + δ))ᶜ = 0 := by
  have hS : MeasurableSet ((Metric.closedBall c (r + δ))ᶜ) := measurableSet_closedBall.compl
  have hxS : x ∉ (Metric.closedBall c (r + δ))ᶜ := by
    simp only [Set.mem_compl_iff, not_not]
    exact Metric.closedBall_subset_closedBall (by linarith) hx
  have hxc : dist x c ≤ r := Metric.mem_closedBall.1 hx
  have hempty : (Metric.closedBall c (r + δ))ᶜ ∩ (Metric.ball x δ ∩ K) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro y ⟨hyS, hyb, -⟩
    refine hyS ?_
    have h1 : dist y x < δ := Metric.mem_ball.1 hyb
    refine Metric.mem_closedBall.2 (le_of_lt ?_)
    calc dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
      _ < r + δ := by linarith
  rw [lazy_apply_set _ x hS, ballWalk_apply_set hK δ x hS, hempty, measure_empty]
  simp [Set.indicator_of_notMem hxS]

/-- **One step of the lazy ball walk grows the support by at most `δ`.**  If the law `mu`
gives no mass outside `Metric.closedBall c r`, the law after one step gives no mass outside
`Metric.closedBall c (r + δ)`.

The proof integrates `lazy_ballWalk_apply_compl_closedBall` against `mu`: the integrand
vanishes on `Metric.closedBall c r`, and the complement of that ball is `mu`-null. -/
theorem measure_compl_closedBall_step_lazy_ballWalk {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 ≤ δ) {mu : Measure (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hmu : mu (Metric.closedBall c r)ᶜ = 0) :
    step (lazy (ballWalk K δ)) mu (Metric.closedBall c (r + δ))ᶜ = 0 := by
  have hS : MeasurableSet ((Metric.closedBall c (r + δ))ᶜ) := measurableSet_closedBall.compl
  rw [step_apply _ _ hS]
  refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ hS)).2 ?_
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hmu
  simp only [Set.mem_setOf_eq, Pi.zero_apply] at hx
  exact fun hxin => hx (lazy_ballWalk_apply_compl_closedBall hK hδ hxin)

/-- **Route 1's crux: after `t` steps the support has grown by at most `t·δ`.**

If the start gives no mass outside `Metric.closedBall c r` then the `t`-step law gives no
mass outside `Metric.closedBall c (r + t·δ)`.  Induction on `t` from
`measure_compl_closedBall_step_lazy_ballWalk`.

This is an *exact* statement about the chain, not an approximation: the bound `r + t·δ` is
the largest distance any trajectory of `t` steps can cover, since every step moves by
strictly less than `δ`. -/
theorem measure_compl_closedBall_ballWalkLaw {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 ≤ δ)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} {c : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hmu0 : mu0 (Metric.closedBall c r)ᶜ = 0) (t : ℕ) :
    ballWalkLaw K δ mu0 t (Metric.closedBall c (r + t * δ))ᶜ = 0 := by
  induction t with
  | zero => simpa using hmu0
  | succ t ih =>
      have hstep := measure_compl_closedBall_step_lazy_ballWalk hK hδ ih
      have hcast : r + (t : ℝ) * δ + δ = r + ((t + 1 : ℕ) : ℝ) * δ := by push_cast; ring
      rw [hcast] at hstep
      exact hstep

/-! ## Route 1, step two: from support to distinctness -/

/-- **A law supported in a ball is not the uniform law on a body that sticks out of it.**

If the `t`-step law charges nothing outside `Metric.closedBall c s` while `K` has positive
volume outside it, the two measures disagree on `(Metric.closedBall c s)ᶜ`.

`volume K ≠ ⊤` is needed: `Arlib.uniformOn` divides by `volume K`, and at `volume K = ⊤` the
quotient collapses to `0` and the argument would prove nothing. -/
theorem ballWalkLaw_ne_uniformOn_of_measure_sdiff_ne_zero
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 ≤ δ)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} {c : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hmu0 : mu0 (Metric.closedBall c r)ᶜ = 0) (hKtop : volume K ≠ ⊤) {t : ℕ}
    (ht : volume (K \ Metric.closedBall c (r + t * δ)) ≠ 0) :
    ballWalkLaw K δ mu0 t ≠ Arlib.uniformOn volume K := by
  intro heq
  have h0 := measure_compl_closedBall_ballWalkLaw hK hδ hmu0 t
  rw [heq, Arlib.uniformOn_apply volume hK measurableSet_closedBall.compl] at h0
  have hset : ((Metric.closedBall c (r + (t : ℝ) * δ))ᶜ ∩ K)
      = K \ Metric.closedBall c (r + (t : ℝ) * δ) := by
    rw [Set.sdiff_eq, Set.inter_comm]
  rw [hset, ENNReal.div_eq_zero_iff] at h0
  exact h0.elim ht hKtop

/-- **Positive volume just outside a concentric ball.**  If `0 ≤ s < R` and the dimension is
at least `1`, the ball `Metric.ball c R` has positive volume outside
`Metric.closedBall c s`.

The proof compares Haar volumes of two concentric balls: `Metric.closedBall c s` is contained
in `Metric.ball c R'` for the intermediate radius `R' = (s + R)/2`, and
`vol (Metric.ball c R') = (R')ⁿ · vol B₁ < Rⁿ · vol B₁ = vol (Metric.ball c R)` because
`n ≥ 1`.  At `n = 0` the claim is false — every ball is the whole one-point space — which is
why `[NeZero n]` is present. -/
theorem measure_ball_sdiff_closedBall_ne_zero [NeZero n] (c : EuclideanSpace ℝ (Fin n))
    {s R : ℝ} (hs : 0 ≤ s) (hsR : s < R) :
    volume (Metric.ball c R \ Metric.closedBall c s) ≠ 0 := by
  set V : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hV
  set R' : ℝ := (s + R) / 2 with hR'
  have hR'0 : 0 ≤ R' := by rw [hR']; linarith
  have hsR' : s < R' := by rw [hR']; linarith
  have hR'R : R' < R := by rw [hR']; linarith
  have hRpos : (0 : ℝ) < R := lt_of_le_of_lt hs hsR
  have hR0 : (0 : ℝ) ≤ R := hRpos.le
  -- volumes of the two concentric balls
  have hvolR : volume (Metric.ball c R) = ENNReal.ofReal (R ^ n) * V := by
    rw [hV, Measure.addHaar_ball volume c hR0, finrank_euclideanSpace_fin]
  have hvolR' : volume (Metric.ball c R') = ENNReal.ofReal (R' ^ n) * V := by
    rw [hV, Measure.addHaar_ball volume c hR'0, finrank_euclideanSpace_fin]
  -- the strict comparison
  have hpow : R' ^ n < R ^ n := pow_lt_pow_left₀ hR'R hR'0 (NeZero.ne n)
  have hlt : volume (Metric.ball c R') < volume (Metric.ball c R) := by
    rw [hvolR, hvolR']
    exact ENNReal.mul_lt_mul_left volume_unitBall_ne_zero volume_unitBall_ne_top
      ((ENNReal.ofReal_lt_ofReal_iff (pow_pos hRpos n)).2 hpow)
  intro hzero
  have hsub : Metric.closedBall c s ⊆ Metric.ball c R' := Metric.closedBall_subset_ball hsR'
  have hsplit : volume (Metric.ball c R ∩ Metric.closedBall c s)
      + volume (Metric.ball c R \ Metric.closedBall c s) = volume (Metric.ball c R) :=
    measure_inter_add_sdiff _ measurableSet_closedBall
  rw [hzero, add_zero] at hsplit
  have hle : volume (Metric.ball c R) ≤ volume (Metric.ball c R') := by
    rw [← hsplit]
    exact measure_mono (Set.inter_subset_right.trans hsub)
  exact absurd hle (not_le.2 hlt)

/-- **Route 1's headline: for every `t` with `r + t·δ < R`, the `t`-step law of the lazy ball
walk is *not* the uniform law on the body.**

Assumptions, all geometric and all checkable:

* `K` is measurable and of finite volume, and contains `Metric.ball c R`;
* the step is non-negative, `0 ≤ δ`;
* the starting law charges nothing outside `Metric.closedBall c r`, with `0 ≤ r`;
* the dimension is at least `1` (`[NeZero n]`; at `n = 0` the space is one point and every
  probability measure on it is the uniform one, so the statement is genuinely false there).

**Range of validity.**  The conclusion is asserted exactly for those `t` with

    r + t·δ < R,        i.e.   t < (R − r)/δ.

Since `Metric.ball c R ⊆ K`, the radius `R` is at most the inradius of `K`, so the threshold
is `Θ(R/δ)` and no better: in the Cousins–Vempala regime `δ ≍ γ/√n` with inscribed radius
`γ` it is `O(√n)`.  It is **far below** the step count `Ttc.mixSteps` at which this
development runs the chain, which is exponential in the dimension: **this theorem says
nothing at `t = mixSteps`.**

The mechanism is support growth, not mixing: a `t`-step trajectory cannot travel further
than `t·δ`, so the law simply has not reached the far side of `K` yet.  Beyond the threshold
the argument gives nothing at all, and no continuity or spectral input replaces it here. -/
theorem ballWalkLaw_ne_uniformOn_of_lt [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤) {c : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hKball : Metric.ball c R ⊆ K) {δ : ℝ} (hδ : 0 ≤ δ)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} {r : ℝ} (hr : 0 ≤ r)
    (hmu0 : mu0 (Metric.closedBall c r)ᶜ = 0) {t : ℕ} (ht : r + t * δ < R) :
    ballWalkLaw K δ mu0 t ≠ Arlib.uniformOn volume K := by
  refine ballWalkLaw_ne_uniformOn_of_measure_sdiff_ne_zero hK hδ hmu0 hKtop ?_
  have hs : (0 : ℝ) ≤ r + (t : ℝ) * δ := by positivity
  have hpos := measure_ball_sdiff_closedBall_ne_zero (n := n) c hs ht
  refine fun hzero => hpos ?_
  refine measure_mono_null ?_ hzero
  exact Set.sdiff_subset_sdiff_left hKball

/-! ## Route 2: the laziness lower bound

Independent of Route 1, and with a different reach: the threshold below does not involve `δ`
at all. -/

section Lazy

variable {Om : Type*} [MeasurableSpace Om]

/-- **A lazy step keeps at least half the mass of every event.**  `lazy P x ≥ ½·δ_x`
pointwise, so `step (lazy P) mu S ≥ ½·mu S`.  No hypothesis on `P` beyond being a kernel. -/
theorem inv_two_mul_le_step_lazy_apply (P : Kernel Om Om) (mu : Measure Om) {S : Set Om}
    (hS : MeasurableSet S) : (2 : ℝ≥0∞)⁻¹ * mu S ≤ step (lazy P) mu S := by
  rw [step_apply _ _ hS]
  have hconst : (2 : ℝ≥0∞)⁻¹ * mu S
      = ∫⁻ x, (2 : ℝ≥0∞)⁻¹ * S.indicator (1 : Om → ℝ≥0∞) x ∂mu := by
    rw [lintegral_const_mul _ (measurable_one.indicator hS), lintegral_indicator hS]
    simp
  rw [hconst]
  refine lintegral_mono fun x => ?_
  rw [lazy_apply_set P x hS]
  exact le_add_self

/-- **Route 2's crux: the lazy chain loses at most a factor `2` of mass per step.**
For every measurable `S` and every `t`,

    μ_t S  ≥  2^(−t) · μ_0 S.

Induction on `t` from `inv_two_mul_le_step_lazy_apply`.  This is the whole content of
"a lazy chain cannot forget its start too fast", and it is completely elementary: no
conductance, no isoperimetry, no spectral gap. -/
theorem inv_pow_mul_le_iterate_lazy_apply (P : Kernel Om Om) (mu : Measure Om) {S : Set Om}
    (hS : MeasurableSet S) (t : ℕ) :
    ((2 : ℝ≥0∞) ^ t)⁻¹ * mu S ≤ iterate (lazy P) mu t S := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hsplit : ((2 : ℝ≥0∞) ^ (t + 1))⁻¹ = (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) ^ t)⁻¹ := by
        rw [pow_succ, ENNReal.mul_inv (Or.inl (by simp)) (Or.inr (by simp))]
        ring
      calc ((2 : ℝ≥0∞) ^ (t + 1))⁻¹ * mu S
          = (2 : ℝ≥0∞)⁻¹ * (((2 : ℝ≥0∞) ^ t)⁻¹ * mu S) := by rw [hsplit, mul_assoc]
        _ ≤ (2 : ℝ≥0∞)⁻¹ * iterate (lazy P) mu t S := by gcongr
        _ ≤ iterate (lazy P) mu (t + 1) S := by
            rw [iterate_succ]
            exact inv_two_mul_le_step_lazy_apply P _ hS

end Lazy

/-- **Route 2's headline: while `2^(−t)·μ₀ S` still exceeds the target's mass of `S`, the
`t`-step law is not the uniform law.**

**Range of validity.**  The conclusion is asserted exactly for those `t` with

    uniformOn volume K S  <  2^(−t) · mu0 S,     i.e.   t < log₂(mu0 S / uniformOn volume K S).

Unlike Route 1 this threshold does **not** involve the step size `δ` — the bound holds for
every `δ`, including steps so large that Route 1 gives nothing past `t = 0`.  It is still
only logarithmic in the warmness ratio, hence `Θ(n)` for the half-ball start on the unit ball
(`ballWalkLaw_ballHalf_ne_uniformOn_unitBall_of_lt_dim`), and therefore **far below**
`Ttc.mixSteps`, which is exponential in `n`.  **This theorem says nothing at
`t = mixSteps`.** -/
theorem ballWalkLaw_ne_uniformOn_of_lt_inv_pow_mul {K : Set (EuclideanSpace ℝ (Fin n))}
    (δ : ℝ) {mu0 : Measure (EuclideanSpace ℝ (Fin n))} {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) {t : ℕ}
    (ht : Arlib.uniformOn volume K S < ((2 : ℝ≥0∞) ^ t)⁻¹ * mu0 S) :
    ballWalkLaw K δ mu0 t ≠ Arlib.uniformOn volume K := by
  intro heq
  have hle : ((2 : ℝ≥0∞) ^ t)⁻¹ * mu0 S ≤ ballWalkLaw K δ mu0 t S :=
    inv_pow_mul_le_iterate_lazy_apply (ballWalk K δ) mu0 hS t
  rw [heq] at hle
  exact absurd hle (not_le.2 ht)

/-! ## The concrete body: the unit ball with the half-ball start

The start is `Arlib.uniformOn volume (Metric.ball 0 (1/2))`, which
`Arlib.MarkovChains.isWarm_uniformOn_ball_half` shows is a `2ⁿ`-warm start for the target and
`Arlib.MarkovChains.uniformOn_ball_half_ne_uniformOn_ball` shows is *not* the target.  The
results below extend that `t = 0` statement to positive `t`. -/

/-- The half-ball start charges nothing outside `Metric.closedBall 0 (1/2)`. -/
theorem measure_compl_closedBall_uniformOn_ballHalf :
    Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))ᶜ = 0 := by
  refine measure_mono_null ?_
    (Arlib.uniformOn_compl_eq_zero volume
      (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1 / 2)))
  exact Set.compl_subset_compl.2 Metric.ball_subset_closedBall

/-- **Route 1 on the unit ball.**  For every step `0 ≤ δ` and every `t` with
`1/2 + t·δ < 1` — that is, `t < 1/(2δ)` — the `t`-step law of the lazy ball walk started
uniformly on `Metric.ball 0 (1/2)` is not the uniform law on `Metric.ball 0 1`.

The threshold `1/(2δ)` is exactly the number of steps the walk needs before a trajectory can
possibly reach the boundary of the body; it is `Θ(1/δ)` and **not** the step count the
development uses. -/
theorem ballWalkLaw_ballHalf_ne_uniformOn_unitBall [NeZero n] {δ : ℝ} (hδ : 0 ≤ δ) {t : ℕ}
    (ht : (1 : ℝ) / 2 + t * δ < 1) :
    ballWalkLaw (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))) t
      ≠ Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  ballWalkLaw_ne_uniformOn_of_lt measurableSet_ball volume_unitBall_ne_top
    (R := 1) subset_rfl hδ (r := (1 : ℝ) / 2) (by norm_num)
    measure_compl_closedBall_uniformOn_ballHalf ht

/-- The target's mass of the half-ball is exactly `2^(-n)`.  Extracted from
`Arlib.MarkovChains.volume_ball_one_eq`, which is the exact volume ratio. -/
theorem uniformOn_unitBall_ballHalf :
    Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    Metric.ball_subset_ball (by norm_num)
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

/-- **Route 2 on the unit ball.**  For *every* step size `δ` and every `t < n`, the `t`-step
law of the lazy ball walk started uniformly on `Metric.ball 0 (1/2)` is not the uniform law
on `Metric.ball 0 1`.

The separating event is the half-ball itself: the start gives it mass `1`, the target gives
it mass `2^(-n)` (`uniformOn_unitBall_ballHalf`), and laziness keeps the `t`-step law's mass
of it at least `2^(-t)`, which exceeds `2^(-n)` exactly while `t < n`.

**Range of validity: `t < n`.**  This is `Θ(n)` and **far below** `Ttc.mixSteps`, which is
`2^(Θ(n))`.  Its point is that it is *independent of `δ`*: at `δ = 1` Route 1
(`ballWalkLaw_ballHalf_ne_uniformOn_unitBall`) gives nothing beyond `t = 0`, while this
reaches `t = n − 1`. -/
theorem ballWalkLaw_ballHalf_ne_uniformOn_unitBall_of_lt_dim (δ : ℝ) {t : ℕ} (ht : t < n) :
    ballWalkLaw (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))) t
      ≠ Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  refine ballWalkLaw_ne_uniformOn_of_lt_inv_pow_mul δ
    (S := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) measurableSet_ball ?_
  rw [uniformOn_unitBall_ballHalf,
    Arlib.uniformOn_self volume measurableSet_ball volume_ballHalf_ne_zero
      volume_ballHalf_ne_top, mul_one]
  refine ENNReal.inv_lt_inv.2 ?_
  have h1 : (1 : ℝ≥0∞) < 2 ^ (n - t) := one_lt_pow' (by norm_num) (by omega)
  have h2 : (2 : ℝ≥0∞) ^ t * 1 < 2 ^ t * 2 ^ (n - t) :=
    ENNReal.mul_lt_mul_right (by simp) (ENNReal.pow_ne_top (by simp)) h1
  rwa [mul_one, ← pow_add, Nat.add_sub_cancel' ht.le] at h2

/-! ## Non-vacuity: two structurally different instances of each range

`CLAUDE.md` §11 asks for a *pair* of inhabitants differing in a parameter, not a single
example, because a single extremal instance satisfies almost anything.  Both pairs below
differ in the step size `δ`, and both carry the numeric thresholds as strictly-positive
conjuncts inside the statement, so a reader can see the `t`-ranges are non-empty and
genuinely different. -/

/-- **Non-vacuity for Route 1: two step sizes, two different non-empty `t`-ranges.**

At `δ₁ = 1/8` the conclusion holds for every `t ≤ 3`; at the smaller `δ₂ = 1/16` it holds for
every `t ≤ 7`.  Both thresholds are proved positive inside the statement (`0 < T₁`,
`T₁ < T₂`), so the ranges are non-empty and the smaller step really does buy more steps —
which is what makes this a pair rather than an example.

Note what the pair does *not* show: `T₂ = 7` is still a constant, and both are far below
`Ttc.mixSteps`. -/
theorem exists_two_nonstationary_step_sizes (n : ℕ) [NeZero n] :
    ∃ δ₁ δ₂ : ℝ, ∃ T₁ T₂ : ℕ,
      0 < δ₁ ∧ 0 < δ₂ ∧ δ₂ < δ₁ ∧ 0 < T₁ ∧ T₁ < T₂ ∧
      (∀ t ≤ T₁, ballWalkLaw (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ₁
          (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))) t
        ≠ Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ∧
      (∀ t ≤ T₂, ballWalkLaw (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ₂
          (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))) t
        ≠ Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
  refine ⟨1 / 8, 1 / 16, 3, 7, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, fun t ht => ?_, fun t ht => ?_⟩
  · refine ballWalkLaw_ballHalf_ne_uniformOn_unitBall (by norm_num) ?_
    have : (t : ℝ) ≤ 3 := by exact_mod_cast ht
    nlinarith
  · refine ballWalkLaw_ballHalf_ne_uniformOn_unitBall (by norm_num) ?_
    have : (t : ℝ) ≤ 7 := by exact_mod_cast ht
    nlinarith

/-- **Non-vacuity for Route 2: the `t`-range does not depend on the step size.**

Two structurally different step sizes — `δ₁ = 1` and the smaller `δ₂ = 1/2` — for which the
*same* range `t < n` is covered.  This is the point of Route 2 and the reason both routes are
kept: at `δ₁ = 1` Route 1's range `1/2 + t·δ < 1` contains no `t ≥ 1` at all, so Route 2 is
not subsumed.

`1 < n` is a conjunct inside the statement, so the range `t < n` provably contains a `t ≥ 1`
and the instance is not the trivial `t = 0` one (`t = 0` is
`Arlib.MarkovChains.uniformOn_ball_half_ne_uniformOn_ball`, which was already known). -/
theorem exists_two_nonstationary_dimension_ranges (n : ℕ) (hn : 2 ≤ n) :
    ∃ δ₁ δ₂ : ℝ, 0 < δ₁ ∧ 0 < δ₂ ∧ δ₂ < δ₁ ∧ 1 < n ∧
      (∀ t < n, ballWalkLaw (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ₁
          (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))) t
        ≠ Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ∧
      (∀ t < n, ballWalkLaw (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ₂
          (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))) t
        ≠ Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
  ⟨1, 1 / 2, by norm_num, by norm_num, by norm_num, by omega,
    fun t ht => ballWalkLaw_ballHalf_ne_uniformOn_unitBall_of_lt_dim 1 ht,
    fun t ht => ballWalkLaw_ballHalf_ne_uniformOn_unitBall_of_lt_dim (1 / 2) ht⟩

/-! ## Axiom audit (`CLAUDE.md` §4)

Every declaration in this file must depend on exactly `[propext, Classical.choice,
Quot.sound]`. -/

#print axioms ballWalkLaw
#print axioms lazy_ballWalk_apply_compl_closedBall
#print axioms measure_compl_closedBall_step_lazy_ballWalk
#print axioms measure_compl_closedBall_ballWalkLaw
#print axioms ballWalkLaw_ne_uniformOn_of_measure_sdiff_ne_zero
#print axioms measure_ball_sdiff_closedBall_ne_zero
#print axioms ballWalkLaw_ne_uniformOn_of_lt
#print axioms inv_two_mul_le_step_lazy_apply
#print axioms inv_pow_mul_le_iterate_lazy_apply
#print axioms ballWalkLaw_ne_uniformOn_of_lt_inv_pow_mul
#print axioms measure_compl_closedBall_uniformOn_ballHalf
#print axioms ballWalkLaw_ballHalf_ne_uniformOn_unitBall
#print axioms uniformOn_unitBall_ballHalf
#print axioms ballWalkLaw_ballHalf_ne_uniformOn_unitBall_of_lt_dim
#print axioms exists_two_nonstationary_step_sizes
#print axioms exists_two_nonstationary_dimension_ranges

end Arlib.MarkovChains
