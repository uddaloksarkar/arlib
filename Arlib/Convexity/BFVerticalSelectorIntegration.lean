/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFVerticalLowerIntegration

/-!
# Eliminating the vertical outcome of the BF roof pencil

The vertical member of the rotating roof pencil is just a cut in the height coordinate.  This
file decodes both its closed and open orientations into a proper height interval and invokes
support minimality.  Consequently the selector of `BFUpperShellSelector` really returns a lower
roof; neither the vertical nor either upper-shell orientation remains.
-/

open Set MeasureTheory

namespace Arlib

variable {m : ℕ}

theorem roofCLM_first_ne_zero {a : ℝ} (ha : a ≠ 0) :
    roofCLM (m := m) a 0 ≠ 0 := by
  intro hzero
  have happ := congrArg (fun L : (Fin (m + 1) → ℝ) →L[ℝ] ℝ =>
    L (Fin.cons 1 (0 : Fin m → ℝ))) hzero
  have : a = 0 := by simpa [roofCLM_apply] using happ
  exact ha this

theorem neg_roofCLM_first (a : ℝ) :
    -(roofCLM (m := m) a 0) = roofCLM (m := m) (-a) 0 := by
  ext x
  simp [roofCLM_apply]

/-- A positive vertical closed cut is the lower height interval. -/
theorem profileBody_inter_verticalHalfSpace_true_of_pos {a r : ℝ} (ha : 0 < a)
    {psi : ℝ → ℝ} (hpsi0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ psi t) :
    profileBody (coordinateSimplex m) psi ∩
        halfSpace (roofCLM (m := m) a 0) (a * r) true =
      profileHeightInterval m psi 0 r := by
  ext x
  simp only [profileHeightInterval, mem_inter_iff]
  rw [mem_profileBody_coordinateSimplex_iff hpsi0]
  simp only [halfSpace_true, mem_setOf_eq, roofCLM_apply, mem_Icc]
  constructor
  · rintro ⟨hx, har⟩
    exact ⟨hx, hx.1.1, by nlinarith⟩
  · rintro ⟨hx, _hx0, hxr⟩
    exact ⟨hx, by nlinarith⟩

/-- A negative vertical closed cut is the upper height interval. -/
theorem profileBody_inter_verticalHalfSpace_true_of_neg {a r : ℝ} (ha : a < 0)
    {psi : ℝ → ℝ} (hpsi0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ psi t) :
    profileBody (coordinateSimplex m) psi ∩
        halfSpace (roofCLM (m := m) a 0) (a * r) true =
      profileHeightInterval m psi r 1 := by
  ext x
  simp only [profileHeightInterval, mem_inter_iff]
  rw [mem_profileBody_coordinateSimplex_iff hpsi0]
  simp only [halfSpace_true, mem_setOf_eq, roofCLM_apply, mem_Icc]
  constructor
  · rintro ⟨hx, har⟩
    exact ⟨hx, by nlinarith, hx.1.2⟩
  · rintro ⟨hx, hrx, _hx1⟩
    exact ⟨hx, by nlinarith⟩

/-- **Final orientation capstone.**  The support-minimizing BF selector has a genuine lower-roof
orientation.  Upper roofs were eliminated in `BFUpperShellSelector`; the proof here eliminates
the remaining vertical orientation, including the open side via reversal of the cut direction.
-/
theorem BFMovingCandidate.exists_roofPencil_cut_lower
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
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∃ (theta : ℝ) (side : Bool),
      (∫ x in profileBody (coordinateSimplex m) c.profile ∩
          halfSpace (roofCLM (m := m) (Real.cos theta)
            (Real.sin theta / Real.sqrt m))
            (pencilLevel r (c.profile r / Real.sqrt m) theta) side,
        g (bfSegmentPoint c.left c.right (x 0))) = 0 ∧
      0 < ∫ x in profileBody (coordinateSimplex m) c.profile ∩
          halfSpace (roofCLM (m := m) (Real.cos theta)
            (Real.sin theta / Real.sqrt m))
            (pencilLevel r (c.profile r / Real.sqrt m) theta) side,
        h (bfSegmentPoint c.left c.right (x 0)) ∧
      ((side = true ∧ 0 < Real.sin theta) ∨
        (side = false ∧ Real.sin theta < 0)) := by
  obtain ⟨theta, side, hgzero, hhpos, horient⟩ := c.exists_roofPencil_cut_not_upper
    hKconv hmin hcne hm hclosed hGint hHint hGEint hHEint hHstrict r hr
  refine ⟨theta, side, hgzero, hhpos, ?_⟩
  rcases horient with hsin | hlower
  · exfalso
    have hcosSq : Real.cos theta ^ 2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    have hcosne : Real.cos theta ≠ 0 := by nlinarith
    have hpsi0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ c.profile t :=
      fun t _ => c.profile_nonneg t
    have hlevel : pencilLevel r (c.profile r / Real.sqrt m) theta = Real.cos theta * r := by
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
            (Nat.ne_of_gt hm) hclosed hr.1.le hr.2 (le_refl 1) (by linarith [hr.1])
            (hGint.mono_set inter_subset_left) (hHint.mono_set inter_subset_left) hgI hhI
      | true =>
          rw [hfun, hlevel,
            profileBody_inter_verticalHalfSpace_true_of_pos hcospos hpsi0] at hgzero hhpos
          exact c.not_profileHeightInterval_of_eq_sInf hKconv hmin hcne
            (Nat.ne_of_gt hm) hclosed (le_refl 0) hr.1 hr.2.le (by simpa using hr.2)
            (hGint.mono_set inter_subset_left) (hHint.mono_set inter_subset_left) hgzero hhpos
  · exact hlower

end Arlib

#print axioms Arlib.roofCLM_first_ne_zero
#print axioms Arlib.profileBody_inter_verticalHalfSpace_true_of_pos
#print axioms Arlib.profileBody_inter_verticalHalfSpace_true_of_neg
#print axioms Arlib.BFMovingCandidate.exists_roofPencil_cut_lower
