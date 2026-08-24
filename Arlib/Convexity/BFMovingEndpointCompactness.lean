/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFProfileCompactness

/-!
# Dominated convergence along moving BF needles

BF's support-minimizing sequence varies both its profile and its physical segment.  This file
extends the fixed-integrand compactness theorem to the pulled-back integrands
`t ↦ g ((1-t) • aₖ + t • bₖ)`.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace Arlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine segment parametrization used by BF. -/
def bfSegmentPoint (a b : E) (t : ℝ) : E := (1 - t) • a + t • b

/-- Moving endpoints give pointwise convergence of every continuous line restriction. -/
theorem tendsto_comp_bfSegmentPoint {a b : ℕ → E} {a₀ b₀ : E} {g : E → ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀)) (hg : Continuous g)
    (t : ℝ) :
    Tendsto (fun k => g (bfSegmentPoint (a k) (b k) t)) atTop
      (𝓝 (g (bfSegmentPoint a₀ b₀ t))) := by
  apply hg.continuousAt.tendsto.comp
  exact ((ha.const_smul (1 - t)).add (hb.const_smul t))

/-- **Dominated convergence for a profile and moving physical needle.** -/
theorem tendsto_integral_profile_mul_movingSegment
    {u : ℕ → ℝ → ℝ} {V : ℝ → ℝ} {a b : ℕ → E} {a₀ b₀ : E}
    {g : E → ℝ} {d : ℕ} {M G : ℝ}
    (hd : d ≠ 0)
    (hu0 : ∀ k t, 0 ≤ u k t) (huM : ∀ k t, u k t ≤ M)
    (hoff : ∀ k t, t ∉ Icc (0 : ℝ) 1 → u k t = 0)
    (humeas : ∀ k, AEStronglyMeasurable (u k))
    (hlim : ∀ t, Tendsto (fun k => u k t) atTop (𝓝 (V t)))
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (hg : Continuous g)
    (hG : ∀ k t, t ∈ Icc (0 : ℝ) 1 → |g (bfSegmentPoint (a k) (b k) t)| ≤ G) :
    Tendsto
      (fun k => ∫ t : ℝ, u k t ^ d * g (bfSegmentPoint (a k) (b k) t)) atTop
      (𝓝 (∫ t : ℝ, V t ^ d * g (bfSegmentPoint a₀ b₀ t))) := by
  have hlineMeas : ∀ k, Measurable fun t : ℝ => g (bfSegmentPoint (a k) (b k) t) := by
    intro k
    apply (hg.comp ?_).measurable
    unfold bfSegmentPoint
    fun_prop
  have hM0 : 0 ≤ M := (hu0 0 0).trans (huM 0 0)
  have hmeas : ∀ k, AEStronglyMeasurable
      (fun t => u k t ^ d * g (bfSegmentPoint (a k) (b k) t)) := fun k =>
    ((humeas k).pow d).mul (hlineMeas k).aestronglyMeasurable
  have hbound : Integrable ((Icc (0 : ℝ) 1).indicator fun _ => M ^ d * G) := by
    refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hdom : ∀ k, ∀ᵐ t : ℝ,
      ‖u k t ^ d * g (bfSegmentPoint (a k) (b k) t)‖ ≤
        (Icc (0 : ℝ) 1).indicator (fun _ => M ^ d * G) t := by
    intro k
    refine Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem ht, norm_mul, Real.norm_eq_abs, abs_pow,
        abs_of_nonneg (hu0 k t)]
      exact mul_le_mul (pow_le_pow_left₀ (hu0 k t) (huM k t) d) (hG k t ht)
        (abs_nonneg _) (pow_nonneg hM0 d)
    · rw [indicator_of_notMem ht, hoff k t ht]
      simp [hd]
  have hpt : ∀ᵐ t : ℝ, Tendsto
      (fun k => u k t ^ d * g (bfSegmentPoint (a k) (b k) t)) atTop
      (𝓝 (V t ^ d * g (bfSegmentPoint a₀ b₀ t))) :=
    Eventually.of_forall fun t => (hlim t).pow d |>.mul
      (tendsto_comp_bfSegmentPoint ha hb hg t)
  exact tendsto_integral_of_dominated_convergence _ hmeas hbound hdom hpt

/-- Continuity on a compact convex body supplies the uniform segment bound required above. -/
theorem exists_uniform_abs_bound_bfSegmentPoint
    {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    {a b : ℕ → E} (haK : ∀ k, a k ∈ K) (hbK : ∀ k, b k ∈ K)
    {g : E → ℝ} (hg : Continuous g) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ k t, t ∈ Icc (0 : ℝ) 1 → |g (bfSegmentPoint (a k) (b k) t)| ≤ G := by
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (IsCompact.bddAbove_image hK (hg.abs.continuousOn))
  refine ⟨max C 0, le_max_right _ _, fun k t ht => ?_⟩
  apply (hC _ (mem_image_of_mem (fun x => |g x|) ?_)).trans (le_max_left _ _)
  exact hKconv (haK k) (hbK k) (sub_nonneg.mpr ht.2) ht.1 (by ring)

/-- The moving-endpoint equality and inequality constraints are closed on a compact convex body. -/
theorem movingSegment_constraints_closed
    {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    {u : ℕ → ℝ → ℝ} {V : ℝ → ℝ} {a b : ℕ → E} {a₀ b₀ : E}
    {g h : E → ℝ} {d : ℕ} {M : ℝ}
    (hd : d ≠ 0)
    (hu0 : ∀ k t, 0 ≤ u k t) (huM : ∀ k t, u k t ≤ M)
    (hoff : ∀ k t, t ∉ Icc (0 : ℝ) 1 → u k t = 0)
    (humeas : ∀ k, AEStronglyMeasurable (u k))
    (hlim : ∀ t, Tendsto (fun k => u k t) atTop (𝓝 (V t)))
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (haK : ∀ k, a k ∈ K) (hbK : ∀ k, b k ∈ K)
    (hg : Continuous g) (hh : Continuous h)
    (hzero : ∀ k, (∫ t : ℝ, u k t ^ d * g (bfSegmentPoint (a k) (b k) t)) = 0)
    (hpos : ∀ k, 0 ≤ ∫ t : ℝ, u k t ^ d * h (bfSegmentPoint (a k) (b k) t)) :
    (∫ t : ℝ, V t ^ d * g (bfSegmentPoint a₀ b₀ t)) = 0 ∧
      0 ≤ ∫ t : ℝ, V t ^ d * h (bfSegmentPoint a₀ b₀ t) := by
  obtain ⟨G, -, hG⟩ := exists_uniform_abs_bound_bfSegmentPoint hK hKconv haK hbK hg
  obtain ⟨H, -, hH⟩ := exists_uniform_abs_bound_bfSegmentPoint hK hKconv haK hbK hh
  have hgconv := tendsto_integral_profile_mul_movingSegment (d := d) hd hu0 huM hoff humeas hlim
    ha hb hg hG
  have hhconv := tendsto_integral_profile_mul_movingSegment (d := d) hd hu0 huM hoff humeas hlim
    ha hb hh hH
  constructor
  · exact tendsto_nhds_unique hgconv
      (tendsto_atTop_of_eventually_const (i₀ := 0) fun k _ => hzero k)
  · exact ge_of_tendsto hhconv (Eventually.of_forall hpos)

/-- **BF support-length attainment from a minimizing sequence of physical needles.**

Compactness selects limiting endpoints, profile Helly selection supplies `V`, the moving-segment
DCT preserves both constraints, and continuity of distance identifies the limiting physical
support length with the infimizing limit `w`. -/
theorem exists_movingNeedle_limit_of_minimizing_sequence
    {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    {u : ℕ → ℝ → ℝ} {a b : ℕ → E} {g h : E → ℝ} {d : ℕ} {M w : ℝ}
    (hd : d ≠ 0)
    (hconc : ∀ k, ConcaveOn ℝ (Ioo (0 : ℝ) 1) (u k))
    (hu0 : ∀ k t, 0 ≤ u k t) (huM : ∀ k t, u k t ≤ M)
    (hoff : ∀ k t, t ∉ Icc (0 : ℝ) 1 → u k t = 0)
    (humeas : ∀ k, AEStronglyMeasurable (u k))
    (haK : ∀ k, a k ∈ K) (hbK : ∀ k, b k ∈ K)
    (hg : Continuous g) (hh : Continuous h)
    (hzero : ∀ k, (∫ t : ℝ, u k t ^ d * g (bfSegmentPoint (a k) (b k) t)) = 0)
    (hpos : ∀ k, 0 ≤ ∫ t : ℝ, u k t ^ d * h (bfSegmentPoint (a k) (b k) t))
    (hw : Tendsto (fun k => dist (a k) (b k)) atTop (𝓝 w)) :
    ∃ a₀ ∈ K, ∃ b₀ ∈ K, ∃ V : ℝ → ℝ,
      dist a₀ b₀ = w ∧ ConcaveOn ℝ (Ioo (0 : ℝ) 1) V ∧
      (∀ t, 0 ≤ V t) ∧
      (∫ t : ℝ, V t ^ d * g (bfSegmentPoint a₀ b₀ t)) = 0 ∧
      0 ≤ ∫ t : ℝ, V t ^ d * h (bfSegmentPoint a₀ b₀ t) := by
  obtain ⟨a₀, ha₀K, φ₁, hφ₁, halim⟩ := hK.tendsto_subseq (x := a) haK
  obtain ⟨b₀, hb₀K, φ₂, hφ₂, hblim⟩ :=
    hK.tendsto_subseq (x := fun k => b (φ₁ k)) (fun k => hbK (φ₁ k))
  obtain ⟨φ₃, hφ₃, V, hVlim⟩ :=
    exists_subseq_tendsto_of_concaveOn_Ioo
      (u := fun k => u (φ₁ (φ₂ k))) (fun k => hconc (φ₁ (φ₂ k)))
      (fun k => hu0 (φ₁ (φ₂ k))) (fun k => huM (φ₁ (φ₂ k)))
      (fun k => hoff (φ₁ (φ₂ k)))
  let φ : ℕ → ℕ := φ₁ ∘ φ₂ ∘ φ₃
  have hφ : StrictMono φ := hφ₁.comp (hφ₂.comp hφ₃)
  have halim' : Tendsto (fun k => a (φ k)) atTop (𝓝 a₀) :=
    (halim.comp hφ₂.tendsto_atTop).comp hφ₃.tendsto_atTop
  have hblim' : Tendsto (fun k => b (φ k)) atTop (𝓝 b₀) :=
    hblim.comp hφ₃.tendsto_atTop
  have hdist : dist a₀ b₀ = w :=
    tendsto_nhds_unique (halim'.dist hblim') (hw.comp hφ.tendsto_atTop)
  have hconstraints := movingSegment_constraints_closed hK hKconv hd
    (fun k => hu0 (φ k)) (fun k => huM (φ k)) (fun k => hoff (φ k))
    (fun k => humeas (φ k)) hVlim halim' hblim'
    (fun k => haK (φ k)) (fun k => hbK (φ k)) hg hh
    (fun k => hzero (φ k)) (fun k => hpos (φ k))
  refine ⟨a₀, ha₀K, b₀, hb₀K, V, hdist,
    concaveOn_of_tendsto (convex_Ioo (0 : ℝ) 1) (fun k => hconc (φ k))
      (fun t ht => hVlim t),
    fun t => ge_of_tendsto (hVlim t) (Eventually.of_forall fun k => hu0 (φ k) t),
    hconstraints.1, hconstraints.2⟩

end Arlib

#print axioms Arlib.tendsto_comp_bfSegmentPoint
#print axioms Arlib.tendsto_integral_profile_mul_movingSegment
#print axioms Arlib.exists_uniform_abs_bound_bfSegmentPoint
#print axioms Arlib.movingSegment_constraints_closed
#print axioms Arlib.exists_movingNeedle_limit_of_minimizing_sequence
