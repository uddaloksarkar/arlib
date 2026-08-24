/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFAffineRoofPencil
import Arlib.Convexity.CrossRatio
import Arlib.Convexity.NeedleSlab
import Arlib.Convexity.HlocFromLocalization

/-!
# Support minimality versus pencil subsegments

This file turns the `sInf` characterization of a support-minimizing BF candidate into its usable
order property, and constructs the candidate obtained by affinely reparametrizing a strict
subsegment.  It is the variational contradiction used to rule out vertical pencil cuts once their
selected moments have been transported to the corresponding parameter subinterval.
-/

open Set MeasureTheory

namespace Arlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Endpoint regularization of an attained candidate -/

/-- Replace the two unconstrained endpoint values of a moving profile by zero. -/
noncomputable def BFMovingCandidate.endpointZeroProfile
    {K : Set E} {g h : E → ℝ} {d : ℕ} (c : BFMovingCandidate K g h d) (t : ℝ) : ℝ :=
  if t ∈ Ioo (0 : ℝ) 1 then c.profile t else 0

/-- Endpoint regularization is equal to the old profile away from the two endpoints.  Outside
`[0,1]` this uses the candidate's zero-support field. -/
theorem BFMovingCandidate.endpointZeroProfile_eq_profile_off_pair
    {K : Set E} {g h : E → ℝ} {d : ℕ} (c : BFMovingCandidate K g h d)
    (t : ℝ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) : c.endpointZeroProfile t = c.profile t := by
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · simp [BFMovingCandidate.endpointZeroProfile, ht]
  · rw [BFMovingCandidate.endpointZeroProfile]
    simp only [if_neg ht]
    symm
    apply (c.profile_off t)
    rw [mem_Icc, not_and_or]
    rw [mem_Ioo, not_and_or] at ht
    rcases ht with ht | ht
    · exact Or.inl (fun h0 => ht (lt_of_le_of_ne h0 (Ne.symm ht0)))
    · exact Or.inr (fun h1 => ht (lt_of_le_of_ne h1 ht1))

/-- **Endpoint regularization of the compactness minimizer.**  Every moving candidate has an
equal-length, equal-moment representative whose profile is concave on the closed interval.
The only changed values are `0` and `1`, a Lebesgue-null pair. -/
noncomputable def BFMovingCandidate.endpointRegularize
    {K : Set E} {g h : E → ℝ} {d : ℕ} (c : BFMovingCandidate K g h d) :
    BFMovingCandidate K g h d where
  left := c.left
  right := c.right
  left_mem := c.left_mem
  right_mem := c.right_mem
  profile := c.endpointZeroProfile
  profile_concave := (concaveOn_Icc_extendZero c.profile_concave
    (fun t ht => c.profile_nonneg t)).subset Ioo_subset_Icc_self (convex_Ioo 0 1)
  profile_nonneg := fun t => nonneg_extendZero_of_nonneg
    (fun s hs => c.profile_nonneg s) t
  profile_bound := fun t => by
    by_cases _ht : t ∈ Ioo (0 : ℝ) 1
    · simpa [BFMovingCandidate.endpointZeroProfile, _ht] using c.profile_bound t
    · rw [BFMovingCandidate.endpointZeroProfile]
      simp only [if_neg _ht]
      unfold bfNormalizedProfileBound
      positivity
  profile_off := fun t ht => by
    rw [BFMovingCandidate.endpointZeroProfile]
    simp only [if_neg (fun h => ht (Ioo_subset_Icc_self h))]
  profile_measurable := by
    unfold BFMovingCandidate.endpointZeroProfile
    exact c.profile_measurable.ite measurableSet_Ioo measurable_const
  mass_one := by
    rw [← c.mass_one]
    apply integral_congr_off_pair
    intro t ht0 ht1
    rw [c.endpointZeroProfile_eq_profile_off_pair t ht0 ht1]
  g_zero := by
    rw [← c.g_zero]
    apply integral_congr_off_pair
    intro t ht0 ht1
    rw [c.endpointZeroProfile_eq_profile_off_pair t ht0 ht1]
  h_nonneg := by
    rw [show (∫ t : ℝ, c.endpointZeroProfile t ^ d *
        h (bfSegmentPoint c.left c.right t)) =
        ∫ t : ℝ, c.profile t ^ d * h (bfSegmentPoint c.left c.right t) by
      apply integral_congr_off_pair
      intro t ht0 ht1
      rw [c.endpointZeroProfile_eq_profile_off_pair t ht0 ht1]]
    exact c.h_nonneg

@[simp] theorem BFMovingCandidate.endpointRegularize_supportLength
    {K : Set E} {g h : E → ℝ} {d : ℕ} (c : BFMovingCandidate K g h d) :
    c.endpointRegularize.supportLength = c.supportLength := rfl

theorem BFMovingCandidate.endpointRegularize_closedConcave
    {K : Set E} {g h : E → ℝ} {d : ℕ} (c : BFMovingCandidate K g h d) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) c.endpointRegularize.profile :=
  concaveOn_Icc_extendZero c.profile_concave (fun t _ht => c.profile_nonneg t)

theorem BFMovingCandidate.endpointRegularize_eq_sInf
    {K : Set E} {g h : E → ℝ} {d : ℕ} (c : BFMovingCandidate K g h d)
    (hmin : c.supportLength = sInf (Set.range
      (fun q : BFMovingCandidate K g h d => q.supportLength))) :
    c.endpointRegularize.supportLength = sInf (Set.range
      (fun q : BFMovingCandidate K g h d => q.supportLength)) := by
  rw [c.endpointRegularize_supportLength, hmin]

/-! ## The usable consequence of `supportLength = sInf range` -/

/-- A candidate realizing the infimum has no longer support than any normalized candidate. -/
theorem BFMovingCandidate.supportLength_le_of_eq_sInf
    {K : Set E} {g h : E → ℝ} {d : ℕ}
    (cmin : BFMovingCandidate K g h d)
    (hmin : cmin.supportLength = sInf (Set.range
      (fun c : BFMovingCandidate K g h d => c.supportLength)))
    (c : BFMovingCandidate K g h d) :
    cmin.supportLength ≤ c.supportLength := by
  have hbdd : BddBelow (Set.range
      (fun c : BFMovingCandidate K g h d => c.supportLength)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact dist_nonneg
  rw [hmin]
  exact csInf_le hbdd ⟨c, rfl⟩

/-- The same minimality applies to every positive-mass raw candidate, because normalization does
not move its endpoints. -/
theorem BFMovingCandidate.supportLength_le_raw_of_eq_sInf
    {K : Set E} {g h : E → ℝ} {d : ℕ} (hd : d ≠ 0)
    (cmin : BFMovingCandidate K g h d)
    (hmin : cmin.supportLength = sInf (Set.range
      (fun c : BFMovingCandidate K g h d => c.supportLength)))
    (c : BFMovingRawCandidate K g h d) :
    cmin.supportLength ≤ dist c.left c.right := by
  simpa only [BFMovingRawCandidate.normalize_supportLength] using
    cmin.supportLength_le_of_eq_sInf hmin (c.normalize hd)

/-! ## Affine reparametrization of a physical subsegment -/

/-- Pull a profile on the parameter subinterval `[l,u]` back to `[0,1]`, and extend it by zero. -/
noncomputable def rescaledSubsegmentProfile (ψ : ℝ → ℝ) (l u s : ℝ) : ℝ :=
  if s ∈ Icc (0 : ℝ) 1 then ψ (l + (u - l) * s) else 0

@[simp] theorem rescaledSubsegmentProfile_of_mem {ψ : ℝ → ℝ} {l u s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    rescaledSubsegmentProfile ψ l u s = ψ (l + (u - l) * s) := by
  simp [rescaledSubsegmentProfile, hs]

@[simp] theorem rescaledSubsegmentProfile_of_notMem {ψ : ℝ → ℝ} {l u s : ℝ}
    (hs : s ∉ Icc (0 : ℝ) 1) : rescaledSubsegmentProfile ψ l u s = 0 := by
  simp [rescaledSubsegmentProfile, hs]

theorem measurable_rescaledSubsegmentProfile {ψ : ℝ → ℝ} (hψ : Measurable ψ) (l u : ℝ) :
    Measurable (rescaledSubsegmentProfile ψ l u) := by
  unfold rescaledSubsegmentProfile
  exact (hψ.comp (by fun_prop)).ite measurableSet_Icc measurable_const

/-- Concavity survives restriction to, and positive affine reparametrization of, a strict
interior subsegment. -/
theorem concaveOn_rescaledSubsegmentProfile {ψ : ℝ → ℝ}
    (hψ : ConcaveOn ℝ (Ioo (0 : ℝ) 1) ψ)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (rescaledSubsegmentProfile ψ l u) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmap : ∀ z ∈ Icc (0 : ℝ) 1, l + (u - l) * z ∈ Ioo (0 : ℝ) 1 := by
    intro z hz
    constructor <;> nlinarith [hz.1, hz.2]
  have hxy : a * x + b * y ∈ Icc (0 : ℝ) 1 :=
    (convex_Icc (0 : ℝ) 1) hx hy ha hb hab
  have hxy' : a • x + b • y ∈ Icc (0 : ℝ) 1 := by
    simpa only [smul_eq_mul] using hxy
  rw [rescaledSubsegmentProfile_of_mem hx, rescaledSubsegmentProfile_of_mem hy,
    rescaledSubsegmentProfile_of_mem hxy']
  have hc := hψ.2 (hmap x hx) (hmap y hy) ha hb hab
  dsimp only [smul_eq_mul] at hc ⊢
  convert hc using 1
  congr 1
  linear_combination -l * hab

/-- Closed-endpoint version, applicable to vertical cuts which retain one endpoint of the
original needle. -/
theorem concaveOn_rescaledSubsegmentProfile_closed {ψ : ℝ → ℝ}
    (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u ≤ 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (rescaledSubsegmentProfile ψ l u) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmap : ∀ z ∈ Icc (0 : ℝ) 1, l + (u - l) * z ∈ Icc (0 : ℝ) 1 := by
    intro z hz
    constructor <;> nlinarith [hz.1, hz.2]
  have hxy : a * x + b * y ∈ Icc (0 : ℝ) 1 :=
    (convex_Icc (0 : ℝ) 1) hx hy ha hb hab
  have hxy' : a • x + b • y ∈ Icc (0 : ℝ) 1 := by
    simpa only [smul_eq_mul] using hxy
  rw [rescaledSubsegmentProfile_of_mem hx, rescaledSubsegmentProfile_of_mem hy,
    rescaledSubsegmentProfile_of_mem hxy']
  have hc := hψ.2 (hmap x hx) (hmap y hy) ha hb hab
  dsimp only [smul_eq_mul] at hc ⊢
  convert hc using 1
  congr 1
  linear_combination -l * hab

/-- Segmenting twice is the same as applying the composite affine parameter once. -/
theorem bfSegmentPoint_subsegment (a b : E) (l u s : ℝ) :
    bfSegmentPoint (bfSegmentPoint a b l) (bfSegmentPoint a b u) s =
      bfSegmentPoint a b (l + (u - l) * s) := by
  unfold bfSegmentPoint
  module

/-- Whole-line change of variables for a profile restricted to `[l,u]`.  The zero extension in
`rescaledSubsegmentProfile` makes the result an exact set-integral identity. -/
theorem integral_rescaledSubsegmentProfile_pow_mul {ψ F : ℝ → ℝ} {d : ℕ} (hd : d ≠ 0)
    {l u : ℝ} (hlu : l < u) :
    (∫ s : ℝ, rescaledSubsegmentProfile ψ l u s ^ d * F (l + (u - l) * s)) =
      (u - l)⁻¹ * ∫ t in Icc l u, ψ t ^ d * F t := by
  let G : ℝ → ℝ := (Icc l u).indicator fun t => ψ t ^ d * F t
  have hc : 0 < u - l := sub_pos.mpr hlu
  have hmem : ∀ s : ℝ, l + (u - l) * s ∈ Icc l u ↔ s ∈ Icc (0 : ℝ) 1 := by
    intro s
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
  have hpoint : (fun s : ℝ => rescaledSubsegmentProfile ψ l u s ^ d *
      F (l + (u - l) * s)) = fun s => G (l + s * (u - l)) := by
    funext s
    have harg : l + s * (u - l) = l + (u - l) * s := by ring
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · have hmapped : l + s * (u - l) ∈ Icc l u := by
        rw [harg, hmem s]
        exact hs
      rw [rescaledSubsegmentProfile_of_mem hs]
      change ψ (l + (u - l) * s) ^ d * F (l + (u - l) * s) =
        (Icc l u).indicator (fun t => ψ t ^ d * F t) (l + s * (u - l))
      rw [indicator_of_mem hmapped, harg]
    · have hmapped : l + s * (u - l) ∉ Icc l u := by
        rw [harg, hmem s]
        exact hs
      simp [rescaledSubsegmentProfile, hs, G, hmapped, hd]
  rw [hpoint, integral_comp_affine_line G l hc]
  unfold G
  rw [integral_indicator measurableSet_Icc]

/-- Exact physical length of a reparametrized subsegment. -/
theorem dist_bfSegmentPoint_subsegment (a b : E) (l u : ℝ) :
    dist (bfSegmentPoint a b l) (bfSegmentPoint a b u) = |u - l| * dist a b := by
  rw [dist_eq_norm]
  have heq : bfSegmentPoint a b l - bfSegmentPoint a b u = (l - u) • (b - a) := by
    unfold bfSegmentPoint
    module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_sub_comm]
  have hnorm : ‖b - a‖ = dist a b := by
    rw [← dist_eq_norm, dist_comm]
  rw [hnorm]

/-- Build the literal raw BF candidate carried by an interior physical subsegment.  The three
moment assumptions are stated after affine pullback; the theorem proves all geometry,
concavity, measurability, support, and endpoint membership. -/
noncomputable def BFMovingCandidate.rescaledSubsegmentRaw
    {K : Set E} (hKconv : Convex ℝ K) {g h : E → ℝ} {d : ℕ}
    (c : BFMovingCandidate K g h d) {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1)
    (hmass : 0 < ∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d)
    (hgzero : (∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d *
      g (bfSegmentPoint c.left c.right (l + (u - l) * s))) = 0)
    (hhpos : 0 ≤ ∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d *
      h (bfSegmentPoint c.left c.right (l + (u - l) * s))) :
    BFMovingRawCandidate K g h d where
  left := bfSegmentPoint c.left c.right l
  right := bfSegmentPoint c.left c.right u
  left_mem := hKconv c.left_mem c.right_mem
    (sub_nonneg.mpr (hlu.trans hu.le)) hl.le (by ring)
  right_mem := hKconv c.left_mem c.right_mem (sub_nonneg.mpr hu.le)
    (hl.le.trans hlu) (by ring)
  profile := rescaledSubsegmentProfile c.profile l u
  profile_concave := concaveOn_rescaledSubsegmentProfile c.profile_concave hl hlu hu
  profile_nonneg := fun s => by
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · rw [rescaledSubsegmentProfile_of_mem hs]
      exact c.profile_nonneg _
    · rw [rescaledSubsegmentProfile_of_notMem hs]
  profile_off := fun s hs => rescaledSubsegmentProfile_of_notMem hs
  profile_measurable := measurable_rescaledSubsegmentProfile c.profile_measurable l u
  mass_pos := hmass
  g_zero := by simpa only [bfSegmentPoint_subsegment] using hgzero
  h_nonneg := by simpa only [bfSegmentPoint_subsegment] using hhpos

/-- Closed-endpoint variant of `rescaledSubsegmentRaw`.  This is the exact constructor required
by a vertical cut `[0,u]` or `[l,1]`; it makes explicit that such a cut is available as soon as
the attained profile is concave on the closed interval. -/
noncomputable def BFMovingCandidate.rescaledClosedSubsegmentRaw
    {K : Set E} (hKconv : Convex ℝ K) {g h : E → ℝ} {d : ℕ}
    (c : BFMovingCandidate K g h d)
    (hclosed : ConcaveOn ℝ (Icc (0 : ℝ) 1) c.profile) {l u : ℝ}
    (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u ≤ 1)
    (hmass : 0 < ∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d)
    (hgzero : (∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d *
      g (bfSegmentPoint c.left c.right (l + (u - l) * s))) = 0)
    (hhpos : 0 ≤ ∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d *
      h (bfSegmentPoint c.left c.right (l + (u - l) * s))) :
    BFMovingRawCandidate K g h d where
  left := bfSegmentPoint c.left c.right l
  right := bfSegmentPoint c.left c.right u
  left_mem := hKconv c.left_mem c.right_mem (sub_nonneg.mpr (hlu.trans hu))
    hl (by ring)
  right_mem := hKconv c.left_mem c.right_mem (sub_nonneg.mpr hu)
    (hl.trans hlu) (by ring)
  profile := rescaledSubsegmentProfile c.profile l u
  profile_concave := concaveOn_rescaledSubsegmentProfile_closed hclosed hl hlu hu
  profile_nonneg := fun s => by
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · rw [rescaledSubsegmentProfile_of_mem hs]
      exact c.profile_nonneg _
    · rw [rescaledSubsegmentProfile_of_notMem hs]
  profile_off := fun s hs => rescaledSubsegmentProfile_of_notMem hs
  profile_measurable := measurable_rescaledSubsegmentProfile c.profile_measurable l u
  mass_pos := hmass
  g_zero := by simpa only [bfSegmentPoint_subsegment] using hgzero
  h_nonneg := by simpa only [bfSegmentPoint_subsegment] using hhpos

/-- **Support-minimality eliminates every feasible strict interior subsegment.**  This is the
variational contradiction needed for a vertical pencil outcome; no abstract extremality premise
remains beyond the already-proved `sInf` characterization. -/
theorem BFMovingCandidate.not_feasible_strictSubsegment_of_eq_sInf
    {K : Set E} (hKconv : Convex ℝ K) {g h : E → ℝ} {d : ℕ} (hd : d ≠ 0)
    (c : BFMovingCandidate K g h d)
    (hmin : c.supportLength = sInf (Set.range
      (fun q : BFMovingCandidate K g h d => q.supportLength)))
    (hne : c.left ≠ c.right) {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1)
    (hmass : 0 < ∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d)
    (hgzero : (∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d *
      g (bfSegmentPoint c.left c.right (l + (u - l) * s))) = 0)
    (hhpos : 0 ≤ ∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d *
      h (bfSegmentPoint c.left c.right (l + (u - l) * s))) : False := by
  let q := c.rescaledSubsegmentRaw hKconv hl hlu hu hmass hgzero hhpos
  have hle := c.supportLength_le_raw_of_eq_sInf hd hmin q
  rw [BFMovingCandidate.supportLength, show q.left = bfSegmentPoint c.left c.right l from rfl,
    show q.right = bfSegmentPoint c.left c.right u from rfl,
    dist_bfSegmentPoint_subsegment, abs_of_nonneg (sub_nonneg.mpr hlu)] at hle
  have hdpos : 0 < dist c.left c.right := dist_pos.mpr hne
  have hwidth : u - l < 1 := by linarith
  exact (not_lt_of_ge hle) (by
    change (u - l) * dist c.left c.right < dist c.left c.right
    nlinarith)

/-- Closed-endpoint capstone: a support minimizer with a closed-concave profile admits no
positive-mass feasible parameter subinterval of width strictly below one. -/
theorem BFMovingCandidate.not_feasible_strictClosedSubsegment_of_eq_sInf
    {K : Set E} (hKconv : Convex ℝ K) {g h : E → ℝ} {d : ℕ} (hd : d ≠ 0)
    (c : BFMovingCandidate K g h d)
    (hmin : c.supportLength = sInf (Set.range
      (fun q : BFMovingCandidate K g h d => q.supportLength)))
    (hclosed : ConcaveOn ℝ (Icc (0 : ℝ) 1) c.profile)
    (hne : c.left ≠ c.right) {l u : ℝ}
    (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u ≤ 1) (hwidth : u - l < 1)
    (hmass : 0 < ∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d)
    (hgzero : (∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d *
      g (bfSegmentPoint c.left c.right (l + (u - l) * s))) = 0)
    (hhpos : 0 ≤ ∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d *
      h (bfSegmentPoint c.left c.right (l + (u - l) * s))) : False := by
  let q := c.rescaledClosedSubsegmentRaw hKconv hclosed hl hlu hu hmass hgzero hhpos
  have hle := c.supportLength_le_raw_of_eq_sInf hd hmin q
  rw [BFMovingCandidate.supportLength, show q.left = bfSegmentPoint c.left c.right l from rfl,
    show q.right = bfSegmentPoint c.left c.right u from rfl,
    dist_bfSegmentPoint_subsegment, abs_of_nonneg (sub_nonneg.mpr hlu)] at hle
  have hdpos : 0 < dist c.left c.right := dist_pos.mpr hne
  exact (not_lt_of_ge hle) (by
    change (u - l) * dist c.left c.right < dist c.left c.right
    nlinarith)

/-- **Vertical-cut elimination in one-dimensional moment form.**  A proper interval selected by
the pencil cannot carry the three feasible moments of a closed-concave support minimizer.  The
affine change of variables and all positive-factor arithmetic are discharged here. -/
theorem BFMovingCandidate.not_verticalIntervalMoments_of_eq_sInf
    {K : Set E} (hKconv : Convex ℝ K) {g h : E → ℝ} {d : ℕ} (hd : d ≠ 0)
    (c : BFMovingCandidate K g h d)
    (hmin : c.supportLength = sInf (Set.range
      (fun q : BFMovingCandidate K g h d => q.supportLength)))
    (hclosed : ConcaveOn ℝ (Icc (0 : ℝ) 1) c.profile)
    (hne : c.left ≠ c.right) {l u : ℝ}
    (hl : 0 ≤ l) (hlu : l < u) (hu : u ≤ 1) (hwidth : u - l < 1)
    (hmass : 0 < ∫ t in Icc l u, c.profile t ^ d)
    (hgzero : (∫ t in Icc l u,
      c.profile t ^ d * g (bfSegmentPoint c.left c.right t)) = 0)
    (hhpos : 0 ≤ ∫ t in Icc l u,
      c.profile t ^ d * h (bfSegmentPoint c.left c.right t)) : False := by
  have hc : 0 < u - l := sub_pos.mpr hlu
  have hmass' := integral_rescaledSubsegmentProfile_pow_mul
    (ψ := c.profile) (F := fun _ => 1) hd hlu
  simp only [mul_one] at hmass'
  have hmassRescaled : 0 < ∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d := by
    rw [hmass']
    exact mul_pos (inv_pos.mpr hc) hmass
  have hg' := integral_rescaledSubsegmentProfile_pow_mul
    (ψ := c.profile) (F := fun t => g (bfSegmentPoint c.left c.right t)) hd hlu
  have hgRescaled : (∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d *
      g (bfSegmentPoint c.left c.right (l + (u - l) * s))) = 0 := by
    rw [hg', hgzero, mul_zero]
  have hh' := integral_rescaledSubsegmentProfile_pow_mul
    (ψ := c.profile) (F := fun t => h (bfSegmentPoint c.left c.right t)) hd hlu
  have hhRescaled : 0 ≤ ∫ s : ℝ, rescaledSubsegmentProfile c.profile l u s ^ d *
      h (bfSegmentPoint c.left c.right (l + (u - l) * s)) := by
    rw [hh']
    exact mul_nonneg (inv_pos.mpr hc).le hhpos
  exact c.not_feasible_strictClosedSubsegment_of_eq_sInf hKconv hd hmin hclosed hne
    hl hlu.le hu hwidth hmassRescaled hgRescaled hhRescaled

end Arlib

#print axioms Arlib.BFMovingCandidate.supportLength_le_of_eq_sInf
#print axioms Arlib.BFMovingCandidate.endpointRegularize
#print axioms Arlib.BFMovingCandidate.endpointRegularize_closedConcave
#print axioms Arlib.BFMovingCandidate.endpointRegularize_eq_sInf
#print axioms Arlib.BFMovingCandidate.supportLength_le_raw_of_eq_sInf
#print axioms Arlib.concaveOn_rescaledSubsegmentProfile
#print axioms Arlib.concaveOn_rescaledSubsegmentProfile_closed
#print axioms Arlib.bfSegmentPoint_subsegment
#print axioms Arlib.integral_rescaledSubsegmentProfile_pow_mul
#print axioms Arlib.BFMovingCandidate.rescaledSubsegmentRaw
#print axioms Arlib.BFMovingCandidate.rescaledClosedSubsegmentRaw
#print axioms Arlib.BFMovingCandidate.not_feasible_strictSubsegment_of_eq_sInf
#print axioms Arlib.BFMovingCandidate.not_feasible_strictClosedSubsegment_of_eq_sInf
#print axioms Arlib.BFMovingCandidate.not_verticalIntervalMoments_of_eq_sInf
