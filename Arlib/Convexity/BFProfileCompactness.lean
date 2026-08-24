/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFSimplexSlice

/-!
# Compactness interfaces for BF feasible profiles

Two closure facts are needed to justify BF's support-minimal profile selection.

* Uniformly bounded pointwise-convergent profiles preserve every weighted moment constraint by
  dominated convergence.
* If the support intervals and profiles converge pointwise, the limiting support is contained in
  the limiting interval.  Thus support width cannot jump upward in the limit.

These are the analytic and semicontinuity components of extremizer attainment.  Subsequence
selection itself is already `Arlib.exists_subseq_tendsto_of_concaveOn_Ioo`.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace Arlib

/-- Weighted profile moments pass to a uniformly bounded pointwise limit. -/
theorem tendsto_integral_pow_mul_of_uniform {u : ℕ → ℝ → ℝ} {V g : ℝ → ℝ}
    {d : ℕ} {M : ℝ}
    (hu0 : ∀ k t, 0 ≤ u k t) (huM : ∀ k t, u k t ≤ M)
    (humeas : ∀ k, AEStronglyMeasurable (u k))
    (hg : Integrable g)
    (hlim : ∀ t, Tendsto (fun k => u k t) atTop (𝓝 (V t))) :
    Tendsto (fun k => ∫ t : ℝ, u k t ^ d * g t) atTop
      (𝓝 (∫ t : ℝ, V t ^ d * g t)) := by
  have hmeas : ∀ k, AEStronglyMeasurable (fun t => u k t ^ d * g t) := fun k =>
    ((humeas k).pow d).mul hg.aestronglyMeasurable
  have hbound : Integrable (fun t : ℝ => M ^ d * ‖g t‖) := hg.norm.const_mul _
  have hdom : ∀ k, ∀ᵐ t : ℝ, ‖u k t ^ d * g t‖ ≤ M ^ d * ‖g t‖ := by
    intro k
    refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Real.norm_eq_abs, abs_pow, abs_of_nonneg (hu0 k t)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hu0 k t) (huM k t) d) (norm_nonneg _)
  have hpt : ∀ᵐ t : ℝ, Tendsto (fun k => u k t ^ d * g t) atTop
      (𝓝 (V t ^ d * g t)) :=
    Eventually.of_forall fun t => (hlim t).pow d |>.mul tendsto_const_nhds
  exact tendsto_integral_of_dominated_convergence _ hmeas hbound hdom hpt

/-- Equality and nonnegative-inequality constraints are closed under the preceding convergence. -/
theorem profile_constraints_closed_of_uniform {u : ℕ → ℝ → ℝ} {V g h : ℝ → ℝ}
    {d : ℕ} {M : ℝ}
    (hu0 : ∀ k t, 0 ≤ u k t) (huM : ∀ k t, u k t ≤ M)
    (humeas : ∀ k, AEStronglyMeasurable (u k))
    (hg : Integrable g) (hh : Integrable h)
    (hlim : ∀ t, Tendsto (fun k => u k t) atTop (𝓝 (V t)))
    (hzero : ∀ k, (∫ t : ℝ, u k t ^ d * g t) = 0)
    (hpos : ∀ k, 0 ≤ ∫ t : ℝ, u k t ^ d * h t) :
    (∫ t : ℝ, V t ^ d * g t) = 0 ∧ 0 ≤ ∫ t : ℝ, V t ^ d * h t := by
  have hgconv := tendsto_integral_pow_mul_of_uniform (d := d) hu0 huM humeas hg hlim
  have hhconv := tendsto_integral_pow_mul_of_uniform (d := d) hu0 huM humeas hh hlim
  constructor
  · exact tendsto_nhds_unique hgconv
      (tendsto_atTop_of_eventually_const (i₀ := 0) fun k _ => hzero k)
  · exact ge_of_tendsto hhconv (Eventually.of_forall hpos)

/-- **Upper semicontinuity of profile support width.**

If `u k` vanishes off `[a k,b k]`, the endpoints converge to `a,b`, and `u k` converges
pointwise to `V`, then `V` vanishes off `[a,b]`.  Consequently an infimizing sequence cannot
acquire a wider support at its limit. -/
theorem limit_profile_eq_zero_off_limit_interval {u : ℕ → ℝ → ℝ} {V : ℝ → ℝ}
    {a b : ℕ → ℝ} {a₀ b₀ : ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (hoff : ∀ k t, t ∉ Icc (a k) (b k) → u k t = 0)
    (hlim : ∀ t, Tendsto (fun k => u k t) atTop (𝓝 (V t))) :
    ∀ t, t ∉ Icc a₀ b₀ → V t = 0 := by
  intro t ht
  rw [mem_Icc, not_and_or] at ht
  have heq : ∀ᶠ k in atTop, u k t = 0 := by
    rcases ht with ht | ht
    · have ht' : t < a₀ := lt_of_not_ge ht
      filter_upwards [(tendsto_order.mp ha).1 t ht'] with k hk
      exact hoff k t (by simp only [mem_Icc, not_and_or]; exact Or.inl (not_le_of_gt hk))
    · have ht' : b₀ < t := lt_of_not_ge ht
      filter_upwards [(tendsto_order.mp hb).2 t ht'] with k hk
      exact hoff k t (by simp only [mem_Icc, not_and_or]; exact Or.inr (not_le_of_gt hk))
  have hz : Tendsto (fun k => u k t) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (heq.mono fun k hk => hk.symm)
  exact tendsto_nhds_unique (hlim t) hz

/-- The corresponding numerical width cannot exceed the limiting endpoint width. -/
theorem limit_profile_support_width_le {V : ℝ → ℝ} {a₀ b₀ w : ℝ}
    (hoff : ∀ t, t ∉ Icc a₀ b₀ → V t = 0) (hw : b₀ - a₀ ≤ w) :
    (∀ t, V t ≠ 0 → a₀ ≤ t ∧ t ≤ b₀) ∧ b₀ - a₀ ≤ w := by
  exact ⟨fun t ht => by
    by_contra hmem
    exact ht (hoff t hmem), hw⟩

/-- **Attainment from a normalized minimizing sequence.**

This packages endpoint compactness, Helly/Arzelà--Ascoli profile selection, dominated convergence
of the two constraints, and support-width semicontinuity.  It is the reusable existence theorem
needed after producing a minimizing sequence of feasible normalized profiles. -/
theorem exists_limit_feasible_profile_of_minimizing_sequence
    {u : ℕ → ℝ → ℝ} {a b : ℕ → ℝ} {g h : ℝ → ℝ} {d : ℕ} {M w : ℝ}
    (hconc : ∀ k, ConcaveOn ℝ (Ioo (0 : ℝ) 1) (u k))
    (hu0 : ∀ k t, 0 ≤ u k t) (huM : ∀ k t, u k t ≤ M)
    (hfixed : ∀ k t, t ∉ Icc (0 : ℝ) 1 → u k t = 0)
    (ha : ∀ k, a k ∈ Icc (0 : ℝ) 1) (hb : ∀ k, b k ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ k t, t ∉ Icc (a k) (b k) → u k t = 0)
    (humeas : ∀ k, AEStronglyMeasurable (u k))
    (hg : Integrable g) (hh : Integrable h)
    (hzero : ∀ k, (∫ t : ℝ, u k t ^ d * g t) = 0)
    (hpos : ∀ k, 0 ≤ ∫ t : ℝ, u k t ^ d * h t)
    (hw : Tendsto (fun k => b k - a k) atTop (𝓝 w)) :
    ∃ a₀ b₀ : ℝ, ∃ V : ℝ → ℝ,
      a₀ ∈ Icc (0 : ℝ) 1 ∧ b₀ ∈ Icc (0 : ℝ) 1 ∧ b₀ - a₀ = w ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) V ∧ (∀ t, 0 ≤ V t) ∧
      (∀ t, t ∉ Icc a₀ b₀ → V t = 0) ∧
      (∫ t : ℝ, V t ^ d * g t) = 0 ∧ 0 ≤ ∫ t : ℝ, V t ^ d * h t := by
  obtain ⟨p, hp, φ₁, hφ₁, hplim⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq
      (x := fun k => (a k, b k)) (fun k => ⟨ha k, hb k⟩)
  obtain ⟨φ₂, hφ₂, V, hVlim⟩ :=
    exists_subseq_tendsto_of_concaveOn_Ioo
      (u := fun k => u (φ₁ k)) (fun k => hconc (φ₁ k))
      (fun k => hu0 (φ₁ k)) (fun k => huM (φ₁ k)) (fun k => hfixed (φ₁ k))
  let φ : ℕ → ℕ := φ₁ ∘ φ₂
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  have hpt : ∀ t, Tendsto (fun k => u (φ k) t) atTop (𝓝 (V t)) := hVlim
  have hapair : Tendsto (fun k => a (φ k)) atTop (𝓝 p.1) := by
    exact ((continuous_fst.tendsto p).comp hplim).comp hφ₂.tendsto_atTop
  have hbpair : Tendsto (fun k => b (φ k)) atTop (𝓝 p.2) := by
    exact ((continuous_snd.tendsto p).comp hplim).comp hφ₂.tendsto_atTop
  have hwidth : p.2 - p.1 = w := by
    exact tendsto_nhds_unique (hbpair.sub hapair) (hw.comp hφ.tendsto_atTop)
  have hconstraints := profile_constraints_closed_of_uniform (d := d)
    (fun k => hu0 (φ k)) (fun k => huM (φ k)) (fun k => humeas (φ k)) hg hh hpt
    (fun k => hzero (φ k)) (fun k => hpos (φ k))
  refine ⟨p.1, p.2, V, hp.1, hp.2, hwidth,
    concaveOn_of_tendsto (convex_Ioo (0 : ℝ) 1) (fun k => hconc (φ k))
      (fun t ht => hpt t),
    fun t => ge_of_tendsto (hpt t) (Eventually.of_forall fun k => hu0 (φ k) t), ?_,
    hconstraints.1, hconstraints.2⟩
  exact limit_profile_eq_zero_off_limit_interval hapair hbpair
    (fun k => hsupp (φ k)) hpt

end Arlib

#print axioms Arlib.tendsto_integral_pow_mul_of_uniform
#print axioms Arlib.profile_constraints_closed_of_uniform
#print axioms Arlib.limit_profile_eq_zero_off_limit_interval
#print axioms Arlib.limit_profile_support_width_le
#print axioms Arlib.exists_limit_feasible_profile_of_minimizing_sequence
