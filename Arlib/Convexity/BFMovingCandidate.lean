/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFMovingEndpointCompactness

/-!
# Attainment of a support-minimal moving BF needle

This file packages the normalized feasible class used in the variational step of
Borell--Fradelizi localization.  Normalizing the `d`-th-power mass does not change either
homogeneous moment constraint.  The normalization also gives the uniform profile bound needed
for compactness.  A decreasing sequence realizing the infimum of physical support lengths then
has a literal feasible minimizer.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace Arlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The common pointwise bound for mass-one `d`-concave needle profiles. -/
def bfNormalizedProfileBound (d : ℕ) : ℝ := 2 ^ (d + 1)

/-- An unnormalized moving BF needle.  Positivity of its `d`-th-power mass permits rescaling. -/
structure BFMovingRawCandidate (K : Set E) (g h : E → ℝ) (d : ℕ) where
  left : E
  right : E
  left_mem : left ∈ K
  right_mem : right ∈ K
  profile : ℝ → ℝ
  profile_concave : ConcaveOn ℝ (Icc (0 : ℝ) 1) profile
  profile_nonneg : ∀ t, 0 ≤ profile t
  profile_off : ∀ t, t ∉ Icc (0 : ℝ) 1 → profile t = 0
  profile_measurable : Measurable profile
  mass_pos : 0 < ∫ t : ℝ, profile t ^ d
  g_zero : (∫ t : ℝ, profile t ^ d * g (bfSegmentPoint left right t)) = 0
  h_nonneg : 0 ≤ ∫ t : ℝ, profile t ^ d * h (bfSegmentPoint left right t)

/-- A normalized feasible moving BF needle.  The explicit common bound is part of the bundle so
that any sequence of candidates is immediately admissible for profile compactness. -/
structure BFMovingCandidate (K : Set E) (g h : E → ℝ) (d : ℕ) where
  left : E
  right : E
  left_mem : left ∈ K
  right_mem : right ∈ K
  profile : ℝ → ℝ
  profile_concave : ConcaveOn ℝ (Ioo (0 : ℝ) 1) profile
  profile_nonneg : ∀ t, 0 ≤ profile t
  profile_bound : ∀ t, profile t ≤ bfNormalizedProfileBound d
  profile_off : ∀ t, t ∉ Icc (0 : ℝ) 1 → profile t = 0
  profile_measurable : Measurable profile
  mass_one : (∫ t : ℝ, profile t ^ d) = 1
  g_zero : (∫ t : ℝ, profile t ^ d * g (bfSegmentPoint left right t)) = 0
  h_nonneg : 0 ≤ ∫ t : ℝ, profile t ^ d * h (bfSegmentPoint left right t)

/-- Physical support length of a moving candidate. -/
def BFMovingCandidate.supportLength {K : Set E} {g h : E → ℝ} {d : ℕ}
    (c : BFMovingCandidate K g h d) : ℝ :=
  dist c.left c.right

/-- A nonnegative concave profile of mass one has the common BF bound. -/
theorem profile_le_bfNormalizedProfileBound {d : ℕ} (hd : d ≠ 0) {ψ : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hψ0 : ∀ t, 0 ≤ ψ t)
    (hoff : ∀ t, t ∉ Icc (0 : ℝ) 1 → ψ t = 0)
    (hmass : (∫ t : ℝ, ψ t ^ d) = 1) :
    ∀ t, ψ t ≤ bfNormalizedProfileBound d := by
  have hroot : (fun t : ℝ => (ψ t ^ d) ^ (1 / (d : ℝ))) = ψ := by
    funext t
    rw [one_div]
    exact Real.pow_rpow_inv_natCast (hψ0 t) hd
  have hpowBound : ∀ t, ψ t ^ d ≤ bfNormalizedProfileBound d := by
    intro t
    exact le_two_pow_of_concaveOn_rpow hd (fun s => pow_nonneg (hψ0 s) d)
      (by simpa only [hroot] using hconc)
      (fun s hs => by rw [hoff s hs]; simp [hd]) hmass t
  intro t
  by_cases ht : ψ t ≤ 1
  · exact ht.trans (by
      unfold bfNormalizedProfileBound
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  · exact (le_self_pow₀ (le_of_not_ge ht) hd).trans (hpowBound t)

/-- Scale used to turn a positive-mass raw profile into a mass-one profile. -/
noncomputable def BFMovingRawCandidate.normalizingScale
    {K : Set E} {g h : E → ℝ} {d : ℕ}
    (c : BFMovingRawCandidate K g h d) : ℝ :=
  (∫ t : ℝ, c.profile t ^ d)⁻¹ ^ ((d : ℝ)⁻¹)

/-- Normalization is positive and its `d`-th power is the reciprocal mass. -/
theorem BFMovingRawCandidate.normalizingScale_pos {d : ℕ} (_hd : d ≠ 0)
    {K : Set E} {g h : E → ℝ}
    (c : BFMovingRawCandidate K g h d) : 0 < c.normalizingScale := by
  unfold BFMovingRawCandidate.normalizingScale
  exact Real.rpow_pos_of_pos (inv_pos.mpr c.mass_pos) _

theorem BFMovingRawCandidate.normalizingScale_pow {d : ℕ} (hd : d ≠ 0)
    {K : Set E} {g h : E → ℝ}
    (c : BFMovingRawCandidate K g h d) :
    c.normalizingScale ^ d = (∫ t : ℝ, c.profile t ^ d)⁻¹ := by
  unfold BFMovingRawCandidate.normalizingScale
  exact Real.rpow_inv_natCast_pow (inv_nonneg.mpr c.mass_pos.le) hd

/-- Mass normalization preserves both homogeneous BF constraints. -/
noncomputable def BFMovingRawCandidate.normalize {d : ℕ} (hd : d ≠ 0)
    {K : Set E} {g h : E → ℝ}
    (c : BFMovingRawCandidate K g h d) : BFMovingCandidate K g h d := by
  let q := c.normalizingScale
  have hqpos : 0 < q := c.normalizingScale_pos hd
  have hqpow : q ^ d = (∫ t : ℝ, c.profile t ^ d)⁻¹ :=
    c.normalizingScale_pow hd
  have hmass : (∫ t : ℝ, (q * c.profile t) ^ d) = 1 := by
    simp_rw [mul_pow, integral_const_mul, hqpow]
    exact inv_mul_cancel₀ c.mass_pos.ne'
  refine
    { left := c.left
      right := c.right
      left_mem := c.left_mem
      right_mem := c.right_mem
      profile := fun t => q * c.profile t
      profile_concave := (c.profile_concave.smul hqpos.le).subset Ioo_subset_Icc_self
        (convex_Ioo 0 1)
      profile_nonneg := fun t => mul_nonneg hqpos.le (c.profile_nonneg t)
      profile_bound := profile_le_bfNormalizedProfileBound hd
        (c.profile_concave.smul hqpos.le)
        (fun t => mul_nonneg hqpos.le (c.profile_nonneg t))
        (fun t ht => by rw [c.profile_off t ht, mul_zero]) hmass
      profile_off := fun t ht => by rw [c.profile_off t ht, mul_zero]
      profile_measurable := c.profile_measurable.const_mul q
      mass_one := hmass
      g_zero := ?_
      h_nonneg := ?_ }
  · rw [show (fun t : ℝ => (q * c.profile t) ^ d *
          g (bfSegmentPoint c.left c.right t)) =
        fun t => q ^ d * (c.profile t ^ d * g (bfSegmentPoint c.left c.right t)) by
      funext t; rw [mul_pow, mul_assoc]]
    rw [integral_const_mul, c.g_zero, mul_zero]
  · rw [show (fun t : ℝ => (q * c.profile t) ^ d *
          h (bfSegmentPoint c.left c.right t)) =
        fun t => q ^ d * (c.profile t ^ d * h (bfSegmentPoint c.left c.right t)) by
      funext t; rw [mul_pow, mul_assoc]]
    rw [integral_const_mul]
    exact mul_nonneg (pow_nonneg hqpos.le d) c.h_nonneg

@[simp] theorem BFMovingRawCandidate.normalize_supportLength {d : ℕ} (hd : d ≠ 0)
    {K : Set E} {g h : E → ℝ}
    (c : BFMovingRawCandidate K g h d) :
    (c.normalize hd).supportLength = dist c.left c.right := rfl

/-- A normalized minimizing sequence has a normalized feasible limit whose physical length is the
limit of the sequence.  Besides the two BF constraints, the proof passes mass one through a third
moving-segment dominated-convergence argument. -/
theorem exists_BFMovingCandidate_limit
    {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    {g h : E → ℝ} (hg : Continuous g) (hh : Continuous h)
    {d : ℕ} (hd : d ≠ 0) (c : ℕ → BFMovingCandidate K g h d) {w : ℝ}
    (hw : Tendsto (fun k => (c k).supportLength) atTop (𝓝 w)) :
    ∃ c₀ : BFMovingCandidate K g h d, c₀.supportLength = w := by
  obtain ⟨a₀, ha₀K, φ₁, hφ₁, halim⟩ :=
    hK.tendsto_subseq (x := fun k => (c k).left) (fun k => (c k).left_mem)
  obtain ⟨b₀, hb₀K, φ₂, hφ₂, hblim⟩ :=
    hK.tendsto_subseq (x := fun k => (c (φ₁ k)).right)
      (fun k => (c (φ₁ k)).right_mem)
  obtain ⟨φ₃, hφ₃, V, hVlim⟩ :=
    exists_subseq_tendsto_of_concaveOn_Ioo
      (u := fun k => (c (φ₁ (φ₂ k))).profile)
      (fun k => (c (φ₁ (φ₂ k))).profile_concave)
      (fun k => (c (φ₁ (φ₂ k))).profile_nonneg)
      (fun k => (c (φ₁ (φ₂ k))).profile_bound)
      (fun k => (c (φ₁ (φ₂ k))).profile_off)
  let φ : ℕ → ℕ := φ₁ ∘ φ₂ ∘ φ₃
  have hφ : StrictMono φ := hφ₁.comp (hφ₂.comp hφ₃)
  have halim' : Tendsto (fun k => (c (φ k)).left) atTop (𝓝 a₀) :=
    (halim.comp hφ₂.tendsto_atTop).comp hφ₃.tendsto_atTop
  have hblim' : Tendsto (fun k => (c (φ k)).right) atTop (𝓝 b₀) :=
    hblim.comp hφ₃.tendsto_atTop
  have hdist : dist a₀ b₀ = w :=
    tendsto_nhds_unique (halim'.dist hblim') (hw.comp hφ.tendsto_atTop)
  have hconstraints := movingSegment_constraints_closed hK hKconv hd
    (fun k => (c (φ k)).profile_nonneg)
    (fun k => (c (φ k)).profile_bound)
    (fun k => (c (φ k)).profile_off)
    (fun k => (c (φ k)).profile_measurable.aestronglyMeasurable)
    hVlim halim' hblim'
    (fun k => (c (φ k)).left_mem) (fun k => (c (φ k)).right_mem)
    hg hh (fun k => (c (φ k)).g_zero) (fun k => (c (φ k)).h_nonneg)
  have hmassConv := tendsto_integral_profile_mul_movingSegment
    (E := E) (g := fun _ => 1) (d := d) hd
    (fun k => (c (φ k)).profile_nonneg)
    (fun k => (c (φ k)).profile_bound)
    (fun k => (c (φ k)).profile_off)
    (fun k => (c (φ k)).profile_measurable.aestronglyMeasurable)
    hVlim halim' hblim' (continuous_const)
    (G := 1) (fun _ _ _ => by simp)
  have hmass : (∫ t : ℝ, V t ^ d) = 1 := by
    have hconv : Tendsto (fun k => ∫ t : ℝ, (c (φ k)).profile t ^ d) atTop
        (𝓝 (∫ t : ℝ, V t ^ d)) := by simpa using hmassConv
    exact tendsto_nhds_unique hconv
      (tendsto_atTop_of_eventually_const (i₀ := 0) fun k _ => (c (φ k)).mass_one)
  have hVoff : ∀ t, t ∉ Icc (0 : ℝ) 1 → V t = 0 := by
    intro t ht
    have hz : Tendsto (fun k => (c (φ k)).profile t) atTop (𝓝 0) := by
      have heq : (fun k => (c (φ k)).profile t) = fun _ : ℕ => (0 : ℝ) := by
        funext k
        exact (c (φ k)).profile_off t ht
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hVlim t) hz
  have hVmeas : Measurable V := by
    refine measurable_of_tendsto_metrizable' atTop
      (fun k => (c (φ k)).profile_measurable) ?_
    exact tendsto_pi_nhds.mpr hVlim
  refine ⟨{
    left := a₀
    right := b₀
    left_mem := ha₀K
    right_mem := hb₀K
    profile := V
    profile_concave := concaveOn_of_tendsto (convex_Ioo (0 : ℝ) 1)
      (fun k => (c (φ k)).profile_concave) (fun t _ => hVlim t)
    profile_nonneg := fun t => ge_of_tendsto (hVlim t)
      (Eventually.of_forall fun k => (c (φ k)).profile_nonneg t)
    profile_bound := fun t => le_of_tendsto (hVlim t)
      (Eventually.of_forall fun k => (c (φ k)).profile_bound t)
    profile_off := hVoff
    profile_measurable := hVmeas
    mass_one := hmass
    g_zero := hconstraints.1
    h_nonneg := hconstraints.2
  }, hdist⟩

/-- **Literal support-minimal normalized BF needle.**  The candidate is obtained from the
canonical decreasing sequence converging to the `sInf` of all feasible physical lengths. -/
theorem exists_supportMinimizing_BFMovingCandidate
    {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    {g h : E → ℝ} (hg : Continuous g) (hh : Continuous h)
    {d : ℕ} (hd : d ≠ 0) (cbase : BFMovingCandidate K g h d) :
    ∃ cmin : BFMovingCandidate K g h d,
      cmin.supportLength = sInf (Set.range
        (fun c : BFMovingCandidate K g h d => c.supportLength)) := by
  let S : Set ℝ := Set.range
    (fun c : BFMovingCandidate K g h d => c.supportLength)
  have hS : S.Nonempty := ⟨cbase.supportLength, ⟨cbase, rfl⟩⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨c, rfl⟩
    exact dist_nonneg
  obtain ⟨r, -, hr, hrS⟩ := exists_seq_tendsto_sInf hS hSbdd
  have hex : ∀ k, ∃ c : BFMovingCandidate K g h d, c.supportLength = r k := by
    intro k
    exact hrS k
  choose c hc using hex
  have hcconv : Tendsto (fun k => (c k).supportLength) atTop (𝓝 (sInf S)) := by
    simpa only [hc] using hr
  simpa only [S] using exists_BFMovingCandidate_limit hK hKconv hg hh hd c hcconv

end Arlib

#print axioms Arlib.profile_le_bfNormalizedProfileBound
#print axioms Arlib.BFMovingRawCandidate.normalizingScale_pow
#print axioms Arlib.BFMovingRawCandidate.normalize
#print axioms Arlib.exists_BFMovingCandidate_limit
#print axioms Arlib.exists_supportMinimizing_BFMovingCandidate
