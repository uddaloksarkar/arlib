/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.IsoIndicator
import Arlib.Convexity.EllLogConcave
import Arlib.MarkovChains.Continuous.SpeedyWalk
import Arlib.MarkovChains.Continuous.SpeedyToUniform

/-!
# A dimension-free isoperimetric inequality for a log-concave density on a bounded convex body

## What this file proves

For a convex `K ⊆ B(0,R)` and a **continuous log-concave** weight `w` with `0 ≤ w ≤ 1`, the
probability measure with density proportional to `1_K·w` satisfies, for every pair of
**measurable** sets `A, B` at distance `d`,

    π((A ∪ B)ᶜ)  ≥  d/(8R) · π(A) · π(B)      (`Arlib.logConcave_isoperimetry_of_ball_bound`)

The coefficient `1/(8R)` **does not depend on `n`**.  Instantiated at `w = ell K δ` this is
exactly the `hiso` binder of
`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn`
(`Arlib/MarkovChains/Continuous/SpeedyToUniform.lean:230-234`) at `kappa = 1/(8R)`
(`Arlib.hiso_ellProb_of_ball_bound`), and
`Arlib.mixesWithin_lazy_speedyWalk_uniformOn_of_ball_bound` plugs it in — so the match of
that binder is machine-checked, not asserted.

Since the consumers assume `ball 0 1 ⊆ K`, in particular `0 ∈ K`, one may take `R = diam K`;
the constant is then `1/(8·diam K)`, i.e. `Θ(1/D)`.  The sharp constant is `2/D`, in the
`min` rather than the product form: `ball_walk.tex:1011-1019` (`ISO2`, Dyer–Frieze /
Lovász–Simonovits / Karzanov–Khachiyan) for a log-concave measure whose support has diameter
`D`, `ball_walk.tex:555-562` (`thm:isoD`) for the uniform measure, and `har_dikin.tex:121-182`
(`thm:iso-cross-ratio`) for the cross-ratio metric.  All three are proved there by
exponential-needle localization, and the book leaves the one-dimensional base case as an
exercise (`ball_walk.tex:1304-1309`).  **This file does not achieve `2/D`, only `1/(8D)`;
dimension-freeness is what it delivers.**

## How, and why it is not the degenerate limit

The repository already had the `n`-dimensional isoperimetric inequality for a density
`f·e^{−‖x‖²/(2σ²)}` with `f ≥ 0` log-concave — `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`
(`Arlib/Convexity/OneDimSharp.lean:631`) — at coefficient `d/σ`, for `S₁, S₂` **open** and `S₃`
**closed**.  Two obstructions stood between it and `1_K·ell`, both recorded in
`Arlib/Convexity/EllLogConcave.lean`'s "What it does not unlock":

* **the Gaussian factor.**  `1_K·ell` is not `f·e^{−‖x‖²/(2σ²)}` with `f` log-concave, and
  deleting the factor by `σ → ∞` sends the coefficient `d/σ` to `0`.  *Resolved by fixing
  `σ = 2R`.*  On `K ⊆ B(0,R)` the Gaussian is then pinched between `e^{−1/8}` and `1`, so
  `e^{−1/8}·(1_K w) ≤ 1_K w e^{−‖x‖²/(8R²)} ≤ 1_K w` pointwise and the tilt can be removed at
  a **constant** cost `e^{−1/4} ≥ 49/64`, leaving a coefficient `Θ(1/R)`.  The localization
  argument is **not** re-run; one comparison of integrals replaces it.
* **open/closed versus measurable.**  The general reduction
  `Arlib.gaussianRestricted_isoperimetry_of_openClosed_enlargement` needs disjoint open
  enlargements, which `Arlib.exists_separated_no_disjoint_open_enlargement` shows need not
  exist.  *Resolved because the hypothesis here is a genuine **metric** separation*
  (`d ≤ dist u v` for all pairs), not the `densDist` disjunction: the `d/8`-thickenings of `A`
  and `B` are then disjoint, open, and still separated by `3d/4`.  Shrinking back to `A`, `B`
  and `(A ∪ B)ᶜ` at the end is monotonicity of the integral, so no tightness is needed.
* the residual discontinuity of `1_K` is handled the way `Arlib/Convexity/IsoIndicator.lean`
  handles it: apply the capstone to `e^{−j·dist(x, closure K)}·w·e^{−‖x‖²/(2σ²)}`, which is
  continuous with log-concave cofactor, and let `j → ∞` by dominated convergence
  (`Arlib.tendsto_setIntegral_expNegInfDist_mul_weight`), the frontier of a convex set being
  Lebesgue-null.

## Scope

`w` is required **continuous** (as `ell` is, `Arlib.continuous_ell_toReal`).  An arbitrary
measurable log-concave density is *not* covered, and this file does not claim to have removed
that obstruction.  `2 ≤ n` throughout; `n = 1` is the regime of
`Arlib.uniformOn_dyerFrieze_dim_one` and is not claimed here.

Nothing here is a conductance, mixing or runtime statement.

## Main results

* `Arlib.tendsto_setIntegral_expNegInfDist_mul_weight` — the dominated-convergence step.
* `Arlib.gaussianWeighted_isoperimetry_of_separated` — the tilted inequality, measurable `A, B`.
* `Arlib.logConcave_isoperimetry_of_ball_bound` — **the crux**, dimension-free `d/(8R)`.
* `Arlib.ellMeasure_eq_ofReal_setIntegral` — `ellMeasure` as an `ofReal` of a Bochner integral.
* `Arlib.hiso_ellProb_of_ball_bound` — **the deliverable**: the `hiso` binder for `ellProb K δ`.
* `Arlib.mixesWithin_lazy_speedyWalk_uniformOn_of_ball_bound` — the binder consumed, which is
  the machine check that its shape matches.
* `Arlib.hiso_ellProb_of_ball_bound_strict_witness` — non-vacuity, with the left-hand side
  **strictly positive**.

There is no `def`, `structure`, `class` or `axiom` in this file; every declaration is a
`theorem`.
-/

open MeasureTheory Set Filter Metric

open Arlib.MarkovChains

open scoped ENNReal Topology

namespace Arlib

/-! ### The continuous outer approximation, with an extra continuous weight -/

section Approximation

variable {n : ℕ}

/-- **Dominated convergence for `e^{−j·dist(x, closure K)}·w(x)·e^{−‖x‖²/(2σ²)}`.**

`Arlib.tendsto_setIntegral_expNegInfDist_mul_gaussian` with a continuous weight `w ∈ [0,1]`
carried along, and the closure already swapped back to `K` by
`Arlib.setIntegral_indicator_closure_eq` (the frontier of a convex set is Lebesgue-null). -/
theorem tendsto_setIntegral_expNegInfDist_mul_weight {σ : ℝ} (hσ : 0 < σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K) (hKne : K.Nonempty)
    {w : EuclideanSpace ℝ (Fin n) → ℝ} (hwc : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    Tendsto (fun j : ℕ => ∫ x in S,
        Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
          gaussianWeightReal (σ ^ 2) x)
      atTop (𝓝 (∫ x in S,
        Set.indicator K (fun y => w y * gaussianWeightReal (σ ^ 2) y) x)) := by
  have hgi : Integrable (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal (σ ^ 2) x) :=
    integrable_gaussianWeightReal hσ
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal (σ ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hcInf : Continuous
      (fun x : EuclideanSpace ℝ (Fin n) => Metric.infDist x (closure K)) :=
    Metric.continuous_infDist_pt (closure K)
  have hInf0 : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ Metric.infDist x (closure K) :=
    fun _ => Metric.infDist_nonneg
  have hCcl : IsClosed (closure K) := isClosed_closure
  have hCne : (closure K).Nonempty := hKne.closure
  have key : Tendsto (fun j : ℕ => ∫ x in S,
      Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
        gaussianWeightReal (σ ^ 2) x)
      atTop (𝓝 (∫ x in S,
        Set.indicator (closure K) (fun y => w y * gaussianWeightReal (σ ^ 2) y) x)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => gaussianWeightReal (σ ^ 2) x) (fun j => ?_) hgi.restrict (fun j => ?_) ?_
    · exact (((Real.continuous_exp.comp ((continuous_const.mul hcInf).neg)).mul hwc).mul
        (continuous_gaussianWeightReal _)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have hle : Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg (Nat.cast_nonneg j) (hInf0 x)
      have h0 : 0 < Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) := Real.exp_pos _
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg h0.le (hw0 x)) (hgpos x).le)]
      have h1 : Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x ≤ 1 := by
        nlinarith [hw0 x, hw1 x]
      nlinarith [hgpos x, mul_nonneg h0.le (hw0 x)]
    · refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ closure K
      · have hz : Metric.infDist x (closure K) = 0 := Metric.infDist_zero_of_mem hx
        rw [Set.indicator_of_mem hx]
        simp only [hz, mul_zero, neg_zero, Real.exp_zero, one_mul]
        exact tendsto_const_nhds
      · have hz : 0 < Metric.infDist x (closure K) :=
          (hCcl.notMem_iff_infDist_pos hCne).mp hx
        rw [Set.indicator_of_notMem hx]
        have hbot : Tendsto (fun j : ℕ => -((j : ℝ) * Metric.infDist x (closure K)))
            atTop atBot := by
          have h1 : Tendsto (fun j : ℕ => (j : ℝ) * Metric.infDist x (closure K))
              atTop atTop :=
            Filter.Tendsto.atTop_mul_const hz tendsto_natCast_atTop_atTop
          exact tendsto_neg_atTop_atBot.comp h1
        have h2 : Tendsto
            (fun j : ℕ => Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp hbot
        simpa using (h2.mul_const (w x)).mul_const (gaussianWeightReal (σ ^ 2) x)
  rwa [setIntegral_indicator_closure_eq hKc
    (fun y => w y * gaussianWeightReal (σ ^ 2) y) S] at key

end Approximation

/-! ### The Gaussian-tilted inequality, for arbitrary metrically separated sets -/

section Tilted

variable {n : ℕ}

/-- **`thm:iso` for the density `1_K·w·e^{−‖x‖²/(2σ²)}`, at a pure metric separation and with
`A`, `B` arbitrary.**

`Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo` asks for `S₁, S₂` *open* and `S₃`
*closed*; the hypothesis here is that `A` and `B` are at distance `d`, which is exactly what the
`d/8`-thickenings `U₁ ⊇ A`, `U₂ ⊇ B` need in order to be **disjoint open** sets still separated by
`3d/4` (`Arlib.norm_sub_ge_of_mem_thickening`).  This is the step that
`Arlib.exists_separated_no_disjoint_open_enlargement` shows is impossible in general: it is
possible here because the separation hypothesis is metric, not a `densDist` disjunction.

The capstone is applied to the *continuous* densities
`h_j(x) = e^{−j·dist(x, closure K)}·w(x)·e^{−‖x‖²/(2σ²)}`, whose cofactor is log-concave
(`Arlib.isLogConcave_exp_neg_infDist` times `w`); `j → ∞` by
`Arlib.tendsto_setIntegral_expNegInfDist_mul_weight`. -/
theorem gaussianWeighted_isoperimetry_of_separated (hn : 2 ≤ n) {σ d : ℝ} (hσ : 0 < σ)
    (hd : 0 < d)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKne : K.Nonempty) (hKbd : Bornology.IsBounded K)
    {w : EuclideanSpace ℝ (Fin n) → ℝ} (hwc : Continuous w) (hwlc : IsLogConcave w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hmass : 0 < ∫ x, Set.indicator K (fun y => w y * gaussianWeightReal (σ ^ 2) y) x)
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hsep : ∀ u ∈ A, ∀ v ∈ B, d ≤ ‖u - v‖) :
    3 * d / 4 * Real.log 2 / σ *
        ((∫ x in A, Set.indicator K (fun y => w y * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in B, Set.indicator K (fun y => w y * gaussianWeightReal (σ ^ 2) y) x)
      ≤ (∫ x, Set.indicator K (fun y => w y * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in (A ∪ B)ᶜ,
            Set.indicator K (fun y => w y * gaussianWeightReal (σ ^ 2) y) x := by
  classical
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal (σ ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hgi : Integrable (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal (σ ^ 2) x) :=
    integrable_gaussianWeightReal hσ
  have hCne : (closure K).Nonempty := hKne.closure
  have hCconv : Convex ℝ (closure K) := hKc.closure
  have hCcomp : IsCompact (closure K) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hKbd.closure
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgle : ∀ x : EuclideanSpace ℝ (Fin n), gaussianWeightReal (σ ^ 2) x ≤ 1 := by
    intro x
    rw [gaussianWeightReal, Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg (sq_nonneg _) (by positivity))
  -- pointwise facts about the approximating densities
  have hj0 : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      0 ≤ Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
        gaussianWeightReal (σ ^ 2) x := fun j x =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (hw0 x)) (hgpos x).le
  have hjle : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
        gaussianWeightReal (σ ^ 2) x ≤ gaussianWeightReal (σ ^ 2) x := by
    intro j x
    have he1 : Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg (Nat.cast_nonneg j) Metric.infDist_nonneg
    have hp : Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x ≤ 1 :=
      (mul_le_of_le_one_left (hw0 x) he1).trans (hw1 x)
    calc Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
          gaussianWeightReal (σ ^ 2) x
        ≤ 1 * gaussianWeightReal (σ ^ 2) x :=
          mul_le_mul_of_nonneg_right hp (hgpos x).le
      _ = gaussianWeightReal (σ ^ 2) x := one_mul _
  have hjcont : ∀ j : ℕ, Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
        gaussianWeightReal (σ ^ 2) x := by
    intro j
    exact ((Real.continuous_exp.comp
      ((continuous_const.mul (Metric.continuous_infDist_pt (closure K))).neg)).mul hwc).mul
      (continuous_gaussianWeightReal _)
  have hjint : ∀ j : ℕ, Integrable fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
        gaussianWeightReal (σ ^ 2) x := by
    intro j
    refine hgi.mono' (hjcont j).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hj0 j x)]
    exact hjle j x
  have hindint : Integrable
      (Set.indicator K (fun y : EuclideanSpace ℝ (Fin n) =>
        w y * gaussianWeightReal (σ ^ 2) y)) := by
    refine hgi.mono'
      ((hwc.mul (continuous_gaussianWeightReal _)).aestronglyMeasurable.indicator hK)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, abs_of_nonneg (mul_nonneg (hw0 x) (hgpos x).le)]
      nlinarith [hgpos x, hw0 x, hw1 x]
    · rw [Set.indicator_of_notMem hx]
      simpa using (hgpos x).le
  have hindle : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      Set.indicator K (fun y => w y * gaussianWeightReal (σ ^ 2) y) x
        ≤ Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
          gaussianWeightReal (σ ^ 2) x := by
    intro j x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx,
        Metric.infDist_zero_of_mem (subset_closure hx)]
      simp
    · rw [Set.indicator_of_notMem hx]
      exact hj0 j x
  -- the thickenings
  have hρ : (0 : ℝ) < d / 8 := by positivity
  have hUsep : ∀ u ∈ Metric.thickening (d / 8) A, ∀ v ∈ Metric.thickening (d / 8) B,
      3 * d / 4 ≤ ‖u - v‖ := by
    intro u hu v hv
    have hcontr := norm_sub_ge_of_mem_thickening hsep hu hv
    have harith : d - 2 * (d / 8) = 3 * d / 4 := by ring
    linarith [hcontr]
  have hUdisj : Disjoint (Metric.thickening (d / 8) A) (Metric.thickening (d / 8) B) := by
    rw [Set.disjoint_left]
    intro a ha hb
    have hcontr := hUsep a ha a hb
    rw [sub_self, norm_zero] at hcontr
    linarith
  have hpart : IsPartition3 Set.univ (Metric.thickening (d / 8) A) (Metric.thickening (d / 8) B)
      (Metric.thickening (d / 8) A ∪ Metric.thickening (d / 8) B)ᶜ :=
    { union := Set.union_compl_self _
      disjoint₁₂ := hUdisj
      disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
      disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) }
  -- the capstone, at each `j`
  have hcap : ∀ j : ℕ,
      3 * d / 4 * Real.log 2 / σ *
          ((∫ x in Metric.thickening (d / 8) A,
              Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
                gaussianWeightReal (σ ^ 2) x)
            * ∫ x in Metric.thickening (d / 8) B,
              Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
                gaussianWeightReal (σ ^ 2) x)
        ≤ (∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
              gaussianWeightReal (σ ^ 2) x)
          * ∫ x in (Metric.thickening (d / 8) A ∪ Metric.thickening (d / 8) B)ᶜ,
              Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
                gaussianWeightReal (σ ^ 2) x := by
    intro j
    have hfc : IsLogConcave fun x : EuclideanSpace ℝ (Fin n) =>
        Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x :=
      IsLogConcave.mul
        (isLogConcave_exp_neg_infDist hCconv hCcomp hCne (Nat.cast_nonneg j)) hwlc
        (fun _ => (Real.exp_pos _).le) hw0
    have hmassj : 0 < ∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
        gaussianWeightReal (σ ^ 2) x :=
      lt_of_lt_of_le hmass (integral_mono hindint (hjint j) (hindle j))
    refine gaussianRestricted_isoperimetry_openClosed_logTwo (d := 3 * d / 4 * Real.log 2) hn hσ
      (f := fun x => Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x)
      (h := fun x => Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
        gaussianWeightReal (σ ^ 2) x)
      (fun x => mul_nonneg (Real.exp_pos _).le (hw0 x)) hfc (fun _ => rfl) (hjcont j)
      (fun x => (hjle j x).trans (hgle x)) (hjint j) hpart Metric.isOpen_thickening Metric.isOpen_thickening
      (Metric.isOpen_thickening.union Metric.isOpen_thickening).isClosed_compl hmassj ?_
    intro u hu v hv
    refine Or.inl ?_
    rw [mul_div_assoc, div_self (ne_of_gt hlog2), mul_one]
    exact hUsep u hu v hv
  -- shrink back to `A`, `B` and `(A ∪ B)ᶜ`
  have hAU : A ⊆ Metric.thickening (d / 8) A := Metric.self_subset_thickening hρ _
  have hBU : B ⊆ Metric.thickening (d / 8) B := Metric.self_subset_thickening hρ _
  have hCsub : (Metric.thickening (d / 8) A ∪ Metric.thickening (d / 8) B)ᶜ ⊆ (A ∪ B)ᶜ :=
    Set.compl_subset_compl.mpr (Set.union_subset_union hAU hBU)
  have hstep : ∀ j : ℕ,
      3 * d / 4 * Real.log 2 / σ *
          ((∫ x in A, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
              gaussianWeightReal (σ ^ 2) x)
            * ∫ x in B, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
              gaussianWeightReal (σ ^ 2) x)
        ≤ (∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
              gaussianWeightReal (σ ^ 2) x)
          * ∫ x in (A ∪ B)ᶜ, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
              gaussianWeightReal (σ ^ 2) x := by
    intro j
    have hae : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        0 ≤ᵐ[volume.restrict S]
          fun x => Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
            gaussianWeightReal (σ ^ 2) x :=
      fun S => Filter.Eventually.of_forall fun x => hj0 j x
    have hmono₁ : (∫ x in A, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
          gaussianWeightReal (σ ^ 2) x)
        ≤ ∫ x in Metric.thickening (d / 8) A,
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
            gaussianWeightReal (σ ^ 2) x :=
      setIntegral_mono_set (hjint j).integrableOn (hae _) (Filter.Eventually.of_forall fun x hx => hAU hx)
    have hmono₂ : (∫ x in B, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
          gaussianWeightReal (σ ^ 2) x)
        ≤ ∫ x in Metric.thickening (d / 8) B,
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
            gaussianWeightReal (σ ^ 2) x :=
      setIntegral_mono_set (hjint j).integrableOn (hae _) (Filter.Eventually.of_forall fun x hx => hBU hx)
    have hmono₃ : (∫ x in (Metric.thickening (d / 8) A ∪ Metric.thickening (d / 8) B)ᶜ,
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
            gaussianWeightReal (σ ^ 2) x)
        ≤ ∫ x in (A ∪ B)ᶜ, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
            gaussianWeightReal (σ ^ 2) x :=
      setIntegral_mono_set (hjint j).integrableOn (hae _) (Filter.Eventually.of_forall fun x hx => hCsub hx)
    have h1 : (0 : ℝ) ≤ ∫ x in A, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
        gaussianWeightReal (σ ^ 2) x := integral_nonneg fun x => hj0 j x
    have h2 : (0 : ℝ) ≤ ∫ x in B, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
        gaussianWeightReal (σ ^ 2) x := integral_nonneg fun x => hj0 j x
    have hMj : (0 : ℝ) ≤ ∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
        gaussianWeightReal (σ ^ 2) x := integral_nonneg fun x => hj0 j x
    have hcoef : (0 : ℝ) ≤ 3 * d / 4 * Real.log 2 / σ := by positivity
    calc 3 * d / 4 * Real.log 2 / σ *
            ((∫ x in A, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
                gaussianWeightReal (σ ^ 2) x)
              * ∫ x in B, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
                gaussianWeightReal (σ ^ 2) x)
        ≤ 3 * d / 4 * Real.log 2 / σ *
            ((∫ x in Metric.thickening (d / 8) A,
                Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
                  gaussianWeightReal (σ ^ 2) x)
              * ∫ x in Metric.thickening (d / 8) B,
                Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
                  gaussianWeightReal (σ ^ 2) x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hmono₁ hmono₂ h2 (h1.trans hmono₁)) hcoef
      _ ≤ (∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
              gaussianWeightReal (σ ^ 2) x)
            * ∫ x in (Metric.thickening (d / 8) A ∪ Metric.thickening (d / 8) B)ᶜ,
              Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
                gaussianWeightReal (σ ^ 2) x := hcap j
      _ ≤ (∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
              gaussianWeightReal (σ ^ 2) x)
            * ∫ x in (A ∪ B)ᶜ, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
                gaussianWeightReal (σ ^ 2) x :=
          mul_le_mul_of_nonneg_left hmono₃ hMj
  -- `j → ∞`
  have hlim : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      Tendsto (fun j : ℕ => ∫ x in S,
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
            gaussianWeightReal (σ ^ 2) x)
        atTop (𝓝 (∫ x in S,
          Set.indicator K (fun y => w y * gaussianWeightReal (σ ^ 2) y) x)) :=
    fun S => tendsto_setIntegral_expNegInfDist_mul_weight hσ hKc hKne hwc hw0 hw1 S
  have hlimU : Tendsto (fun j : ℕ => ∫ x,
      Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * w x *
        gaussianWeightReal (σ ^ 2) x)
      atTop (𝓝 (∫ x, Set.indicator K (fun y => w y * gaussianWeightReal (σ ^ 2) y) x)) := by
    simpa only [Measure.restrict_univ] using hlim Set.univ
  exact le_of_tendsto_of_tendsto' (((hlim A).mul (hlim B)).const_mul _)
    (hlimU.mul (hlim (A ∪ B)ᶜ)) hstep

end Tilted

/-! ### The crux: the tilt removed, at a dimension-free constant -/

section Crux

variable {n : ℕ}

/-- **The crux.  A dimension-free isoperimetric inequality for a log-concave density on a
bounded convex body.**

For `K ⊆ B(0,R)` convex and `w` a continuous log-concave weight with `0 ≤ w ≤ 1`, the measure
with density `1_K·w` satisfies, for every pair `A, B` at distance `d`,

    d/(8R) · (∫_A 1_K w)(∫_B 1_K w)  ≤  (∫ 1_K w)(∫_{(A∪B)ᶜ} 1_K w),

i.e. after normalising, `π((A ∪ B)ᶜ) ≥ (d/(8R))·π(A)·π(B)`.  **The coefficient `1/(8R)` does
not depend on `n`.**

**Why this is not the forbidden `σ → ∞` limit.**  The only `n`-dimensional isoperimetric
inequality available for a general log-concave cofactor is
`Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`, whose density carries a Gaussian
factor and whose coefficient is `d/σ`; letting `σ → ∞` to delete the factor sends the
coefficient to `0`.  Here `σ` is instead **fixed at `2R`**, at which scale the Gaussian is
pinched between `e^{−1/8}` and `1` on all of `K`, so deleting it costs a *constant* factor
`e^{−1/4} ≥ 49/64` and the coefficient survives.  The localization argument is not re-run;
what is re-run is one comparison of integrals.

`8` is not optimal: the true constant is `2/D` with `D` the diameter (Kannan–Lovász–Simonovits;
`har_dikin.tex:121-182` proves the cross-ratio form by localization).  Dimension-freeness, not
the constant, is the point. -/
theorem logConcave_isoperimetry_of_ball_bound (hn : 2 ≤ n) {R d : ℝ} (hR : 0 < R) (hd : 0 < d)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {w : EuclideanSpace ℝ (Fin n) → ℝ} (hwc : Continuous w) (hwlc : IsLogConcave w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hmass : 0 < ∫ x, Set.indicator K w x)
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hsep : ∀ u ∈ A, ∀ v ∈ B, d ≤ ‖u - v‖) :
    d / (8 * R) * ((∫ x in A, Set.indicator K w x) * ∫ x in B, Set.indicator K w x)
      ≤ (∫ x, Set.indicator K w x) * ∫ x in (A ∪ B)ᶜ, Set.indicator K w x := by
  classical
  have hRne : R ≠ 0 := ne_of_gt hR
  have hσ : (0 : ℝ) < 2 * R := by linarith
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal ((2 * R) ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hgle : ∀ x : EuclideanSpace ℝ (Fin n), gaussianWeightReal ((2 * R) ^ 2) x ≤ 1 := by
    intro x
    rw [gaussianWeightReal, Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg (sq_nonneg _) (by positivity))
  have hglow : ∀ x ∈ K, Real.exp (-(1 / 8)) ≤ gaussianWeightReal ((2 * R) ^ 2) x := by
    intro x hx
    rw [gaussianWeightReal]
    refine Real.exp_le_exp.mpr ?_
    have hden : (0 : ℝ) < 2 * (2 * R) ^ 2 := by positivity
    rw [le_div_iff₀ hden]
    nlinarith [hKR x hx, norm_nonneg x]
  -- `K` is nonempty, bounded, of finite volume
  have hKne : K.Nonempty := by
    rcases Set.eq_empty_or_nonempty K with he | hne
    · exfalso; rw [he] at hmass; simp at hmass
    · exact hne
  have hKball : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hKR x hx
  have hKbd : Bornology.IsBounded K :=
    (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := R)).subset hKball
  have hvolK : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hKball)
  -- integrability of the two densities
  have hgint : Integrable (Set.indicator K w) := by
    rw [integrable_indicator_iff hK]
    exact Measure.integrableOn_of_bounded hvolK hwc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact hw1 x)
  have hGint : Integrable
      (Set.indicator K (fun y : EuclideanSpace ℝ (Fin n) =>
        w y * gaussianWeightReal ((2 * R) ^ 2) y)) := by
    refine (integrable_gaussianWeightReal hσ).mono'
      ((hwc.mul (continuous_gaussianWeightReal _)).aestronglyMeasurable.indicator hK)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, abs_of_nonneg (mul_nonneg (hw0 x) (hgpos x).le)]
      nlinarith [hgpos x, hw0 x, hw1 x]
    · rw [Set.indicator_of_notMem hx]
      simpa using (hgpos x).le
  -- the two pointwise comparisons
  have hGle : ∀ x, Set.indicator K (fun y => w y * gaussianWeightReal ((2 * R) ^ 2) y) x
      ≤ Set.indicator K w x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      nlinarith [hgpos x, hgle x, hw0 x]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  have hGlow : ∀ x, Real.exp (-(1 / 8)) * Set.indicator K w x
      ≤ Set.indicator K (fun y => w y * gaussianWeightReal ((2 * R) ^ 2) y) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      nlinarith [hglow x hx, hw0 x]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  -- and the two integral comparisons
  have hlow : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      Real.exp (-(1 / 8)) * (∫ x in S, Set.indicator K w x)
        ≤ ∫ x in S, Set.indicator K (fun y => w y * gaussianWeightReal ((2 * R) ^ 2) y) x := by
    intro S
    rw [← integral_const_mul]
    exact setIntegral_mono (hgint.const_mul _).integrableOn hGint.integrableOn hGlow
  have hupp : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      (∫ x in S, Set.indicator K (fun y => w y * gaussianWeightReal ((2 * R) ^ 2) y) x)
        ≤ ∫ x in S, Set.indicator K w x :=
    fun S => setIntegral_mono hGint.integrableOn hgint.integrableOn hGle
  have hlowU : Real.exp (-(1 / 8)) * (∫ x, Set.indicator K w x)
      ≤ ∫ x, Set.indicator K (fun y => w y * gaussianWeightReal ((2 * R) ^ 2) y) x := by
    simpa only [Measure.restrict_univ] using hlow Set.univ
  have huppU : (∫ x, Set.indicator K (fun y => w y * gaussianWeightReal ((2 * R) ^ 2) y) x)
      ≤ ∫ x, Set.indicator K w x := by
    simpa only [Measure.restrict_univ] using hupp Set.univ
  have hcpos : (0 : ℝ) < Real.exp (-(1 / 8)) := Real.exp_pos _
  have hmass' : 0 < ∫ x, Set.indicator K (fun y => w y * gaussianWeightReal ((2 * R) ^ 2) y) x :=
    lt_of_lt_of_le (mul_pos hcpos hmass) hlowU
  -- the tilted inequality
  have htilt := gaussianWeighted_isoperimetry_of_separated hn hσ hd hK hKc hKne hKbd hwc hwlc
    hw0 hw1 hmass' hsep
  -- the arithmetic
  have hnn : ∀ S : Set (EuclideanSpace ℝ (Fin n)), (0 : ℝ) ≤ ∫ x in S, Set.indicator K w x :=
    fun S => integral_nonneg fun x => Set.indicator_nonneg (fun y _ => hw0 y) x
  have hMnn : (0 : ℝ) ≤ ∫ x, Set.indicator K w x :=
    integral_nonneg fun x => Set.indicator_nonneg (fun y _ => hw0 y) x
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hc78 : (7 / 8 : ℝ) ≤ Real.exp (-(1 / 8)) := by
    have := Real.add_one_le_exp (-(1 / 8) : ℝ); linarith
  have hcc : (49 / 64 : ℝ) ≤ Real.exp (-(1 / 8)) * Real.exp (-(1 / 8)) := by
    nlinarith [hc78, hcpos]
  have hprod : (0.6931471803 : ℝ) * (49 / 64)
      ≤ Real.log 2 * (Real.exp (-(1 / 8)) * Real.exp (-(1 / 8))) :=
    mul_le_mul hlog2.le hcc (by norm_num) (by linarith)
  have hcoefpos : (0 : ℝ) ≤ 3 * d / 4 * Real.log 2 / (2 * R) := by positivity
  have hcoef : d / (8 * R)
      ≤ 3 * d / 4 * Real.log 2 / (2 * R) * (Real.exp (-(1 / 8)) * Real.exp (-(1 / 8))) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * R)]
    have hrw : 3 * d / 4 * Real.log 2 / (2 * R) *
          (Real.exp (-(1 / 8)) * Real.exp (-(1 / 8))) * (8 * R)
        = 3 * (Real.log 2 * (Real.exp (-(1 / 8)) * Real.exp (-(1 / 8)))) * d := by
      field_simp; ring
    rw [hrw]
    nlinarith [hprod, hd]
  calc d / (8 * R) * ((∫ x in A, Set.indicator K w x) * ∫ x in B, Set.indicator K w x)
      ≤ 3 * d / 4 * Real.log 2 / (2 * R) *
            (Real.exp (-(1 / 8)) * Real.exp (-(1 / 8))) *
          ((∫ x in A, Set.indicator K w x) * ∫ x in B, Set.indicator K w x) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg (hnn A) (hnn B))
    _ = 3 * d / 4 * Real.log 2 / (2 * R) *
          ((Real.exp (-(1 / 8)) * ∫ x in A, Set.indicator K w x) *
            (Real.exp (-(1 / 8)) * ∫ x in B, Set.indicator K w x)) := by ring
    _ ≤ 3 * d / 4 * Real.log 2 / (2 * R) *
          ((∫ x in A, Set.indicator K
                (fun y => w y * gaussianWeightReal ((2 * R) ^ 2) y) x)
            * ∫ x in B, Set.indicator K
                (fun y => w y * gaussianWeightReal ((2 * R) ^ 2) y) x) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hlow A) (hlow B) (mul_nonneg hcpos.le (hnn B))
            (le_trans (mul_nonneg hcpos.le (hnn A)) (hlow A))) hcoefpos
    _ ≤ (∫ x, Set.indicator K (fun y => w y * gaussianWeightReal ((2 * R) ^ 2) y) x)
          * ∫ x in (A ∪ B)ᶜ, Set.indicator K
              (fun y => w y * gaussianWeightReal ((2 * R) ^ 2) y) x := htilt
    _ ≤ (∫ x, Set.indicator K w x) * ∫ x in (A ∪ B)ᶜ, Set.indicator K w x :=
        mul_le_mul huppU (hupp _) (integral_nonneg fun x =>
          Set.indicator_nonneg (fun y _ => mul_nonneg (hw0 y) (hgpos y).le) x) hMnn

end Crux

/-! ### The bridge from set integrals of `1_K·ell` to `ellMeasure` -/

section Bridge

variable {n : ℕ}

/-- `Arlib.MarkovChains.ellMeasure K δ S` is the `ENNReal.ofReal` of the ordinary Bochner
integral of `1_K·ell` over `S`. -/
theorem ellMeasure_eq_ofReal_setIntegral {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hvolK : volume K ≠ ⊤) (δ : ℝ)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    ellMeasure K δ S
      = ENNReal.ofReal (∫ x in S, Set.indicator K (fun y => (ell K δ y).toReal) x) := by
  classical
  have hell1 : ∀ x : EuclideanSpace ℝ (Fin n), (ell K δ x).toReal ≤ 1 := by
    intro x
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K δ x)
  have hellm : Measurable fun x : EuclideanSpace ℝ (Fin n) => (ell K δ x).toReal :=
    (measurable_ell hK δ).ennreal_toReal
  have hgint : Integrable (Set.indicator K (fun y : EuclideanSpace ℝ (Fin n) =>
      (ell K δ y).toReal)) := by
    rw [integrable_indicator_iff hK]
    exact Measure.integrableOn_of_bounded hvolK hellm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]; exact hell1 x)
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint.integrableOn
    (Filter.Eventually.of_forall fun x =>
      Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x)]
  have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (Set.indicator K (fun y => (ell K δ y).toReal) x)
        = Set.indicator K (fun y => ell K δ y) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ x))]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  rw [lintegral_congr hpt, lintegral_indicator hK, Measure.restrict_restrict hK,
    ellMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS, Set.inter_comm]

end Bridge

/-! ### The deliverable: the `hiso` binder of `SpeedyToUniform.lean`, at `κ = 1/(8R)` -/

section Deliverable

variable {n : ℕ}

/-- **The isoperimetric binder of
`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn`
(`Arlib/MarkovChains/Continuous/SpeedyToUniform.lean:230-234`), discharged at
`κ = 1/(8R)`.**

Verbatim the shape that theorem asks for, with `kappa := 1/(8*R)` where `R` is any bound on
`‖x‖` over `K`.  **`κ` does not depend on `n`.**  When `0 ∈ K` — in particular whenever
`ball 0 1 ⊆ K`, the standing hypothesis of the consumers — one may take `R = diam K`, so this
is `κ = 1/(8·diam K)`, i.e. `Θ(1/D)`.

The density of `Arlib.MarkovChains.ellProb K δ` is `1_K·ell`, and `ell` is continuous
(`Arlib.continuous_ell_toReal`), log-concave (`Arlib.isLogConcave_ell_toReal`) and bounded by
`1` (`Arlib.MarkovChains.ell_le_one`), so `Arlib.logConcave_isoperimetry_of_ball_bound` applies
directly; the rest is the passage from Bochner integrals to the measure
(`Arlib.ellMeasure_eq_ofReal_setIntegral`) and the normalisation `Z⁻¹`.

This covers `2 ≤ n` only; `n = 1` is `Arlib.uniformOn_dyerFrieze_dim_one`'s regime and is not
claimed here. -/
theorem hiso_ellProb_of_ball_bound (hn : 2 ≤ n) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hK0 : volume K ≠ 0) :
    ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal (1 / (8 * R)) * ENNReal.ofReal d * ellProb K δ A * ellProb K δ B
        ≤ ellProb K δ ((K \ A) \ B) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hKball : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hKR x hx
  have hvolK : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hKball)
  have hell1 : ∀ x : EuclideanSpace ℝ (Fin n), (ell K δ x).toReal ≤ 1 := by
    intro x
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K δ x)
  have hwc : Continuous fun x : EuclideanSpace ℝ (Fin n) => (ell K δ x).toReal :=
    continuous_ell_toReal hn0 hδ.le
  have hwlc : IsLogConcave fun x : EuclideanSpace ℝ (Fin n) => (ell K δ x).toReal :=
    isLogConcave_ell_toReal hK hKc δ
  have hw0 : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ (ell K δ x).toReal :=
    fun _ => ENNReal.toReal_nonneg
  -- the total mass
  have hZ0 : ellMeasure K δ Set.univ ≠ 0 := ellMeasure_univ_ne_zero hK hK0 hδ
  have hZt : ellMeasure K δ Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top hvolK (ellMeasure_univ_le K δ)
  have hMass0 : (0 : ℝ) ≤ ∫ x, Set.indicator K (fun y => (ell K δ y).toReal) x :=
    integral_nonneg fun x => Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x
  have hZeq : ellMeasure K δ Set.univ
      = ENNReal.ofReal (∫ x, Set.indicator K (fun y => (ell K δ y).toReal) x) := by
    simpa only [Measure.restrict_univ] using
      ellMeasure_eq_ofReal_setIntegral hK hvolK δ (MeasurableSet.univ)
  have hmass : 0 < ∫ x, Set.indicator K (fun y => (ell K δ y).toReal) x := by
    rcases hMass0.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hZeq, ← h, ENNReal.ofReal_zero]) hZ0
  -- the binder
  intro d hd A B hA hB _hAK _hBK hsep
  have hsep' : ∀ u ∈ A, ∀ v ∈ B, d ≤ ‖u - v‖ := by
    intro u hu v hv
    simpa only [dist_eq_norm] using hsep u hu v hv
  have hreal := logConcave_isoperimetry_of_ball_bound hn hR hd hK hKc hKR hwc hwlc hw0 hell1
    hmass hsep'
  -- the conclusion set
  have hsets : ((K \ A) \ B) ∩ K = (A ∪ B)ᶜ ∩ K := by
    ext x
    constructor
    · rintro ⟨⟨⟨hxK, hxA⟩, hxB⟩, -⟩
      refine ⟨?_, hxK⟩
      rintro (h | h)
      · exact hxA h
      · exact hxB h
    · rintro ⟨hx, hxK⟩
      exact ⟨⟨⟨hxK, fun h => hx (Or.inl h)⟩, fun h => hx (Or.inr h)⟩, hxK⟩
  have hset : (∫ x in (K \ A) \ B, Set.indicator K (fun y => (ell K δ y).toReal) x)
      = ∫ x in (A ∪ B)ᶜ, Set.indicator K (fun y => (ell K δ y).toReal) x := by
    rw [setIntegral_indicator hK, setIntegral_indicator hK, hsets]
  -- to `ENNReal`
  have hAeq := ellMeasure_eq_ofReal_setIntegral hK hvolK δ hA
  have hBeq := ellMeasure_eq_ofReal_setIntegral hK hvolK δ hB
  have h3eq := ellMeasure_eq_ofReal_setIntegral hK hvolK δ ((hK.diff hA).diff hB)
  rw [hset] at h3eq
  have hknn : (0 : ℝ) ≤ d / (8 * R) := by positivity
  have hann : (0 : ℝ) ≤ ∫ x in A, Set.indicator K (fun y => (ell K δ y).toReal) x :=
    integral_nonneg fun x => Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x
  have hkey : ENNReal.ofReal (1 / (8 * R)) * ENNReal.ofReal d * ellMeasure K δ A *
      ellMeasure K δ B
      ≤ ellMeasure K δ Set.univ * ellMeasure K δ ((K \ A) \ B) := by
    have h1 : ENNReal.ofReal (d / (8 * R) *
        ((∫ x in A, Set.indicator K (fun y => (ell K δ y).toReal) x)
          * ∫ x in B, Set.indicator K (fun y => (ell K δ y).toReal) x))
        ≤ ENNReal.ofReal ((∫ x, Set.indicator K (fun y => (ell K δ y).toReal) x)
          * ∫ x in (A ∪ B)ᶜ, Set.indicator K (fun y => (ell K δ y).toReal) x) :=
      ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul hknn, ENNReal.ofReal_mul hann, ENNReal.ofReal_mul hMass0,
      ← mul_assoc] at h1
    have hkeq : ENNReal.ofReal (1 / (8 * R)) * ENNReal.ofReal d
        = ENNReal.ofReal (d / (8 * R)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    rw [hkeq, hAeq, hBeq, hZeq, h3eq]
    exact h1
  -- normalise
  have hprob : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      ellProb K δ S = (ellMeasure K δ Set.univ)⁻¹ * ellMeasure K δ S := by
    intro S
    rw [ellProb, Measure.smul_apply, smul_eq_mul]
  rw [hprob A, hprob B, hprob ((K \ A) \ B)]
  calc ENNReal.ofReal (1 / (8 * R)) * ENNReal.ofReal d *
        ((ellMeasure K δ Set.univ)⁻¹ * ellMeasure K δ A) *
        ((ellMeasure K δ Set.univ)⁻¹ * ellMeasure K δ B)
      = (ENNReal.ofReal (1 / (8 * R)) * ENNReal.ofReal d * ellMeasure K δ A *
            ellMeasure K δ B) *
          ((ellMeasure K δ Set.univ)⁻¹ * (ellMeasure K δ Set.univ)⁻¹) := by ring
    _ ≤ (ellMeasure K δ Set.univ * ellMeasure K δ ((K \ A) \ B)) *
          ((ellMeasure K δ Set.univ)⁻¹ * (ellMeasure K δ Set.univ)⁻¹) :=
        mul_le_mul' hkey (le_refl _)
    _ = (ellMeasure K δ Set.univ * (ellMeasure K δ Set.univ)⁻¹) *
          ((ellMeasure K δ Set.univ)⁻¹ * ellMeasure K δ ((K \ A) \ B)) := by ring
    _ = (ellMeasure K δ Set.univ)⁻¹ * ellMeasure K δ ((K \ A) \ B) := by
        rw [ENNReal.mul_inv_cancel hZ0 hZt, one_mul]

/-- **The binder consumed.**  `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn`
(`Arlib/MarkovChains/Continuous/SpeedyToUniform.lean:226`) with its `hkappa` and `hiso`
hypotheses discharged at `kappa = 1/(8R)` by `Arlib.hiso_ellProb_of_ball_bound`.

The only content of this corollary is that the discharge **type-checks**: it is the machine
check that `hiso_ellProb_of_ball_bound`'s statement is that theorem's `hiso` binder, rather
than something merely similar.  `hwarm` and `hsmooth` are still hypotheses here — they are not
this file's business. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_of_ball_bound (hn : 2 ≤ n) {R δ : ℝ} (hR : 0 < R)
    (hδ : 0 < δ) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hconv : Convex ℝ K) (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {s : ℝ≥0∞} (hsmooth : IsSmooth K δ s)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellProb K δ))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M (min (1 / 32) (1 / (8 * R) * δ / (256 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (speedyWalk K δ)) (Arlib.uniformOn volume K) mu0 t
      (ENNReal.ofReal eps + s / (1 - s)) :=
  mixesWithin_lazy_speedyWalk_uniformOn (by omega) hK hconv hK0 hKtop hδ
    (by positivity) (hiso_ellProb_of_ball_bound hn hR hδ hK hconv hKR hK0) hsmooth hM hwarm
    heps ht

end Deliverable

/-! ### Non-vacuity -/

section Witness

/-- **A strict non-vacuity witness.**  In dimension `2`, for the unit ball `K = B(0,1)` with
`δ = 1/4`, `R = 1`, `d = 1/2` and `A`, `B` the two balls of radius `1/8` about `±c` with
`‖c‖ = 1/2`, every hypothesis of `Arlib.hiso_ellProb_of_ball_bound` holds **and its left-hand
side is strictly positive** — so the conclusion delivered there is an inequality between two
positive quantities, not the trivial `0 ≤ _`.

`ell K (1/4)` equals `1` on both `A` and `B` (`Arlib.MarkovChains.ell_unitBall_eq_one_of_mem`:
both lie inside `B(0, 3/4)`), so `ellMeasure K δ A = vol(A) > 0`. -/
theorem hiso_ellProb_of_ball_bound_strict_witness :
    ∃ (K A B : Set (EuclideanSpace ℝ (Fin 2))) (δ d R : ℝ),
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧ volume K ≠ 0 ∧
        0 < R ∧ 0 < δ ∧ 0 < d ∧
        MeasurableSet A ∧ MeasurableSet B ∧ A ⊆ K ∧ B ⊆ K ∧
        (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) ∧
        0 < ENNReal.ofReal (1 / (8 * R)) * ENNReal.ofReal d * ellProb K δ A *
              ellProb K δ B ∧
        ENNReal.ofReal (1 / (8 * R)) * ENNReal.ofReal d * ellProb K δ A * ellProb K δ B
          ≤ ellProb K δ ((K \ A) \ B) := by
  classical
  set c : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (0 : Fin 2) (1 / 2 : ℝ) with hcdef
  have hcn : ‖c‖ = 1 / 2 := by
    rw [hcdef, PiLp.norm_single]
    norm_num
  set K : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 1 with hKdef
  set A : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball c (1 / 8) with hAdef
  set B : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball (-c) (1 / 8) with hBdef
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  have hc0 : dist c 0 = 1 / 2 := by rw [dist_zero_right, hcn]
  have hnc0 : dist (-c) 0 = 1 / 2 := by rw [dist_zero_right, norm_neg, hcn]
  -- both balls sit deep inside the unit ball
  have hdeepA : ∀ x ∈ A, dist x 0 < 3 / 4 := by
    intro x hx
    have h1 : dist x c < 1 / 8 := Metric.mem_ball.1 hx
    have h2 : dist x 0 ≤ dist x c + dist c 0 := dist_triangle _ _ _
    rw [hc0] at h2
    linarith
  have hdeepB : ∀ x ∈ B, dist x 0 < 3 / 4 := by
    intro x hx
    have h1 : dist x (-c) < 1 / 8 := Metric.mem_ball.1 hx
    have h2 : dist x 0 ≤ dist x (-c) + dist (-c) 0 := dist_triangle _ _ _
    rw [hnc0] at h2
    linarith
  have hAK : A ⊆ K := fun x hx => Metric.mem_ball.2 (by linarith [hdeepA x hx])
  have hBK : B ⊆ K := fun x hx => Metric.mem_ball.2 (by linarith [hdeepB x hx])
  have hellA : ∀ x ∈ A, ell K (1 / 4) x = 1 := by
    intro x hx
    exact ell_unitBall_eq_one_of_mem hδ (Metric.mem_ball.2 (by linarith [hdeepA x hx]))
  have hellB : ∀ x ∈ B, ell K (1 / 4) x = 1 := by
    intro x hx
    exact ell_unitBall_eq_one_of_mem hδ (Metric.mem_ball.2 (by linarith [hdeepB x hx]))
  -- the separation
  have hdcc : dist c (-c) = 1 := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ c, norm_smul, hcn]
    norm_num
  have hsep : ∀ u ∈ A, ∀ v ∈ B, (1 / 2 : ℝ) ≤ dist u v := by
    intro u hu v hv
    have h1 : dist c u < 1 / 8 := by rw [dist_comm]; exact Metric.mem_ball.1 hu
    have h2 : dist v (-c) < 1 / 8 := Metric.mem_ball.1 hv
    have h3 : dist c (-c) ≤ dist c u + (dist u v + dist v (-c)) :=
      le_trans (dist_triangle c u (-c)) (by gcongr; exact dist_triangle u v (-c))
    rw [hdcc] at h3
    linarith
  -- the masses
  have hKm : MeasurableSet K := measurableSet_ball
  have hAm : MeasurableSet A := measurableSet_ball
  have hBm : MeasurableSet B := measurableSet_ball
  have hK0 : volume K ≠ 0 := volume_unitBall_ne_zero
  have hKtop : volume K ≠ ⊤ := volume_unitBall_ne_top
  have hZ0 : ellMeasure K (1 / 4) Set.univ ≠ 0 := ellMeasure_univ_ne_zero hKm hK0 hδ
  have hZt : ellMeasure K (1 / 4) Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (ellMeasure_univ_le K (1 / 4))
  have hmassA : ellMeasure K (1 / 4) A = volume A := by
    rw [ellMeasure, withDensity_apply _ hAm, Measure.restrict_restrict hAm,
      Set.inter_eq_self_of_subset_left hAK,
      setLIntegral_congr_fun (g := fun _ => (1 : ℝ≥0∞)) hAm (fun x hx => hellA x hx),
      setLIntegral_one]
  have hmassB : ellMeasure K (1 / 4) B = volume B := by
    rw [ellMeasure, withDensity_apply _ hBm, Measure.restrict_restrict hBm,
      Set.inter_eq_self_of_subset_left hBK,
      setLIntegral_congr_fun (g := fun _ => (1 : ℝ≥0∞)) hBm (fun x hx => hellB x hx),
      setLIntegral_one]
  have hvA : volume A ≠ 0 := (Metric.measure_ball_pos volume c (by norm_num)).ne'
  have hvB : volume B ≠ 0 := (Metric.measure_ball_pos volume (-c) (by norm_num)).ne'
  have hprobA : ellProb K (1 / 4) A ≠ 0 := by
    rw [ellProb, Measure.smul_apply, smul_eq_mul, hmassA]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hZt) hvA
  have hprobB : ellProb K (1 / 4) B ≠ 0 := by
    rw [ellProb, Measure.smul_apply, smul_eq_mul, hmassB]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hZt) hvB
  refine ⟨K, A, B, 1 / 4, 1 / 2, 1, hKm, convex_ball _ _, ?_, hK0, by norm_num, hδ,
    by norm_num, hAm, hBm, hAK, hBK, hsep, ?_, ?_⟩
  · intro x hx
    rw [← dist_zero_right]
    exact le_of_lt (Metric.mem_ball.1 hx)
  · rw [pos_iff_ne_zero]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) hprobA) hprobB
    · exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
    · exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  · exact hiso_ellProb_of_ball_bound (le_refl 2) (by norm_num) hδ hKm (convex_ball _ _)
      (fun x hx => by rw [← dist_zero_right]; exact le_of_lt (Metric.mem_ball.1 hx)) hK0
      (1 / 2) (by norm_num) A B hAm hBm hAK hBK hsep

end Witness

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.tendsto_setIntegral_expNegInfDist_mul_weight
#print axioms Arlib.gaussianWeighted_isoperimetry_of_separated
#print axioms Arlib.logConcave_isoperimetry_of_ball_bound
#print axioms Arlib.ellMeasure_eq_ofReal_setIntegral
#print axioms Arlib.hiso_ellProb_of_ball_bound
#print axioms Arlib.mixesWithin_lazy_speedyWalk_uniformOn_of_ball_bound
#print axioms Arlib.hiso_ellProb_of_ball_bound_strict_witness
