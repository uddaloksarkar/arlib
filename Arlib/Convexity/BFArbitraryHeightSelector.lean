/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFLexicographicExtremizer

/-!
# The BF roof selector through an arbitrary interior height

Unlike the boundary-touching specialization, BF's three-case variational proof fixes an
arbitrary pencil point `(r,s)`.  The vertical outcome is still impossible: when `sin theta=0`,
the `s` coordinate disappears and the cut is a proper height interval.  This file restores that
source-faithful interface, leaving precisely the lower-roof/upper-shell alternative.
-/

open Set MeasureTheory

namespace Arlib

variable {m : ℕ}

theorem BFMovingCandidate.not_vertical_roofPencil_cut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKconv : Convex ℝ K) {g h : E → ℝ}
    (c : BFMovingCandidate K g h m)
    (hmin : c.supportLength = sInf (Set.range
      (fun q : BFMovingCandidate K g h m => q.supportLength)))
    (hcne : c.left ≠ c.right) (hm : 0 < m)
    (hclosed : ConcaveOn ℝ (Icc (0 : ℝ) 1) c.profile)
    (hGint : IntegrableOn (fun x : Fin (m + 1) → ℝ =>
      g (bfSegmentPoint c.left c.right (x 0)))
      (profileBody (coordinateSimplex m) c.profile))
    (hHint : IntegrableOn (fun x : Fin (m + 1) → ℝ =>
      h (bfSegmentPoint c.left c.right (x 0)))
      (profileBody (coordinateSimplex m) c.profile))
    {r s theta : ℝ} {side : Bool} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hsin : Real.sin theta = 0)
    (hgzero : (∫ x in profileBody (coordinateSimplex m) c.profile ∩
      halfSpace (roofCLM (m := m) (Real.cos theta)
        (Real.sin theta / Real.sqrt m)) (pencilLevel r s theta) side,
      g (bfSegmentPoint c.left c.right (x 0))) = 0)
    (hhpos : 0 < ∫ x in profileBody (coordinateSimplex m) c.profile ∩
      halfSpace (roofCLM (m := m) (Real.cos theta)
        (Real.sin theta / Real.sqrt m)) (pencilLevel r s theta) side,
      h (bfSegmentPoint c.left c.right (x 0))) : False := by
  have hcosSq : Real.cos theta ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have hcosne : Real.cos theta ≠ 0 := by nlinarith
  have hpsi0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ c.profile t :=
    fun t _ => c.profile_nonneg t
  have hlevel : pencilLevel r s theta = Real.cos theta * r := by
    simp [pencilLevel, hsin]
  have hfun : roofCLM (m := m) (Real.cos theta)
      (Real.sin theta / Real.sqrt m) = roofCLM (m := m) (Real.cos theta) 0 := by
    simp [hsin]
  have hLne : roofCLM (m := m) (Real.cos theta) 0 ≠ 0 :=
    roofCLM_first_ne_zero hcosne
  rcases lt_or_gt_of_ne hcosne with hcosneg | hcospos
  · cases side with
    | false =>
        have hgneg := setIntegral_halfSpace_neg (μ := volume)
          hLne (Real.cos theta * r) true
          (f := fun x : Fin (m + 1) → ℝ =>
            g (bfSegmentPoint c.left c.right (x 0)))
          (C := profileBody (coordinateSimplex m) c.profile)
        have hhneg := setIntegral_halfSpace_neg (μ := volume)
          hLne (Real.cos theta * r) true
          (f := fun x : Fin (m + 1) → ℝ =>
            h (bfSegmentPoint c.left c.right (x 0)))
          (C := profileBody (coordinateSimplex m) c.profile)
        rw [neg_roofCLM_first,
          show -(Real.cos theta * r) = (-Real.cos theta) * r by ring,
          profileBody_inter_verticalHalfSpace_true_of_pos (neg_pos.mpr hcosneg) hpsi0] at hgneg hhneg
        simp only [Bool.not_true] at hgneg hhneg
        rw [hfun, hlevel] at hgzero hhpos
        have hgI : (∫ x in profileHeightInterval m c.profile 0 r,
            g (bfSegmentPoint c.left c.right (x 0))) = 0 := by linarith
        have hhI : 0 < ∫ x in profileHeightInterval m c.profile 0 r,
            h (bfSegmentPoint c.left c.right (x 0)) := by linarith
        exact c.not_profileHeightInterval_of_eq_sInf hKconv hmin hcne
          (Nat.ne_of_gt hm) hclosed le_rfl hr.1 hr.2.le (by simpa using hr.2)
          (hGint.mono_set inter_subset_left) (hHint.mono_set inter_subset_left) hgI hhI
    | true =>
        rw [hfun, hlevel,
          profileBody_inter_verticalHalfSpace_true_of_neg hcosneg hpsi0] at hgzero hhpos
        exact c.not_profileHeightInterval_of_eq_sInf hKconv hmin hcne
          (Nat.ne_of_gt hm) hclosed hr.1.le hr.2 le_rfl (by linarith [hr.1])
          (hGint.mono_set inter_subset_left) (hHint.mono_set inter_subset_left) hgzero hhpos
  · cases side with
    | false =>
        have hgneg := setIntegral_halfSpace_neg (μ := volume)
          hLne (Real.cos theta * r) true
          (f := fun x : Fin (m + 1) → ℝ =>
            g (bfSegmentPoint c.left c.right (x 0)))
          (C := profileBody (coordinateSimplex m) c.profile)
        have hhneg := setIntegral_halfSpace_neg (μ := volume)
          hLne (Real.cos theta * r) true
          (f := fun x : Fin (m + 1) → ℝ =>
            h (bfSegmentPoint c.left c.right (x 0)))
          (C := profileBody (coordinateSimplex m) c.profile)
        rw [neg_roofCLM_first,
          show -(Real.cos theta * r) = (-Real.cos theta) * r by ring,
          profileBody_inter_verticalHalfSpace_true_of_neg
            (by linarith : -Real.cos theta < 0) hpsi0] at hgneg hhneg
        simp only [Bool.not_true] at hgneg hhneg
        rw [hfun, hlevel] at hgzero hhpos
        have hgI : (∫ x in profileHeightInterval m c.profile r 1,
            g (bfSegmentPoint c.left c.right (x 0))) = 0 := by linarith
        have hhI : 0 < ∫ x in profileHeightInterval m c.profile r 1,
            h (bfSegmentPoint c.left c.right (x 0)) := by linarith
        exact c.not_profileHeightInterval_of_eq_sInf hKconv hmin hcne
          (Nat.ne_of_gt hm) hclosed hr.1.le hr.2 le_rfl (by linarith [hr.1])
          (hGint.mono_set inter_subset_left) (hHint.mono_set inter_subset_left) hgI hhI
    | true =>
        rw [hfun, hlevel,
          profileBody_inter_verticalHalfSpace_true_of_pos hcospos hpsi0] at hgzero hhpos
        exact c.not_profileHeightInterval_of_eq_sInf hKconv hmin hcne
          (Nat.ne_of_gt hm) hclosed le_rfl hr.1 hr.2.le (by simpa using hr.2)
          (hGint.mono_set inter_subset_left) (hHint.mono_set inter_subset_left) hgzero hhpos

/-- **Arbitrary-height source selector.**  For every `(r,s)` with `r` interior, the BF pencil
has a constraint-preserving nonvertical member. -/
theorem BFMovingCandidate.exists_roofPencil_cut_arbitraryHeight_nonvertical
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKconv : Convex ℝ K) {g h : E → ℝ}
    (c : BFMovingCandidate K g h m)
    (hmin : c.supportLength = sInf (Set.range
      (fun q : BFMovingCandidate K g h m => q.supportLength)))
    (hcne : c.left ≠ c.right) (hm : 0 < m)
    (hclosed : ConcaveOn ℝ (Icc (0 : ℝ) 1) c.profile)
    (hGint : IntegrableOn (fun x : Fin (m + 1) → ℝ =>
      g (bfSegmentPoint c.left c.right (x 0)))
      (profileBody (coordinateSimplex m) c.profile))
    (hHint : IntegrableOn (fun x : Fin (m + 1) → ℝ =>
      h (bfSegmentPoint c.left c.right (x 0)))
      (profileBody (coordinateSimplex m) c.profile))
    (hGEint : IntegrableOn (fun X : EuclideanSpace ℝ (Fin (m + 1)) =>
      g (bfSegmentPoint c.left c.right ((WithLp.ofLp X) 0)))
      {X | WithLp.ofLp X ∈ profileBody (coordinateSimplex m) c.profile})
    (hHEint : IntegrableOn (fun X : EuclideanSpace ℝ (Fin (m + 1)) =>
      h (bfSegmentPoint c.left c.right ((WithLp.ofLp X) 0)))
      {X | WithLp.ofLp X ∈ profileBody (coordinateSimplex m) c.profile})
    (hHstrict : 0 < ∫ t : ℝ, c.profile t ^ m *
      h (bfSegmentPoint c.left c.right t))
    (r s : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∃ (theta : ℝ) (side : Bool),
      (∫ x in profileBody (coordinateSimplex m) c.profile ∩
          halfSpace (roofCLM (m := m) (Real.cos theta)
            (Real.sin theta / Real.sqrt m)) (pencilLevel r s theta) side,
        g (bfSegmentPoint c.left c.right (x 0))) = 0 ∧
      0 < ∫ x in profileBody (coordinateSimplex m) c.profile ∩
          halfSpace (roofCLM (m := m) (Real.cos theta)
            (Real.sin theta / Real.sqrt m)) (pencilLevel r s theta) side,
        h (bfSegmentPoint c.left c.right (x 0)) ∧
      (((side = true ∧ 0 < Real.sin theta) ∨
          (side = false ∧ Real.sin theta < 0)) ∨
        ((side = false ∧ 0 < Real.sin theta) ∨
          (side = true ∧ Real.sin theta < 0))) := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hpsi0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ c.profile t :=
    fun t _ => c.profile_nonneg t
  have hGtotal : (∫ x in profileBody (coordinateSimplex m) c.profile,
      g (bfSegmentPoint c.left c.right (x 0))) = 0 := by
    have heq := setIntegral_axis_profileBody_coordinateSimplex_of_support
      (F := fun t => g (bfSegmentPoint c.left c.right t)) hm0
      c.profile_measurable hpsi0 c.profile_off hGint
    rw [c.g_zero, mul_zero] at heq
    exact heq
  have hHtotal : 0 < ∫ x in profileBody (coordinateSimplex m) c.profile,
      h (bfSegmentPoint c.left c.right (x 0)) := by
    have heq := setIntegral_axis_profileBody_coordinateSimplex_of_support
      (F := fun t => h (bfSegmentPoint c.left c.right t)) hm0
      c.profile_measurable hpsi0 c.profile_off hHint
    rw [heq]
    exact mul_pos (volume_coordinateSimplex_toReal_pos (m := m)) hHstrict
  obtain ⟨theta, side, hz, hp, horient⟩ := exists_profileBody_roofPencil_cut_zero_pos
    (G := fun t => g (bfSegmentPoint c.left c.right t))
    (H := fun t => h (bfSegmentPoint c.left c.right t)) hm
    c.profile_measurable hpsi0 hGEint hHEint hGtotal hHtotal r s
  refine ⟨theta, side, hz, hp, ?_⟩
  rcases horient with hvertical | hnonvertical
  · exact False.elim (c.not_vertical_roofPencil_cut hKconv hmin hcne hm hclosed
      hGint hHint hr hvertical hz hp)
  · exact hnonvertical

end Arlib

#print axioms Arlib.BFMovingCandidate.not_vertical_roofPencil_cut
#print axioms Arlib.BFMovingCandidate.exists_roofPencil_cut_arbitraryHeight_nonvertical
