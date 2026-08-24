/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.AffineProfileCut
import Arlib.Topology.HamSandwich

/-!
# Constraint-preserving adapted cuts of affine-profile bodies

This file supplies the finite selection step needed by the affine-power form of localization.
Two signed constraints on the transverse base are simultaneously bisected by the two-measure
ham-sandwich theorem.  Pulling the selected base half-space back along the affine rays gives an
ordinary ambient half-space, and the exact affine profile survives the cut.

Unlike `profileBody_inter_profileHalfSpace`, the geometric identity below permits an arbitrary
cut level.  Its price is strict positivity of the profile, which is exactly the regularized
finite-stage regime in the KLS proof.
-/

open Set MeasureTheory
open scoped Pointwise

namespace Arlib

variable {m : ℕ}

/-- Scaling by a strictly positive number commutes with an arbitrary-level half-space cut. -/
theorem smul_inter_baseHalfSpaceAt_of_pos {A : Set (Fin m → ℝ)}
    (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) {c r : ℝ} (hr : 0 < r) :
    r • (A ∩ baseHalfSpaceAt L c) =
      (r • A) ∩ {z : Fin m → ℝ | L z ≤ r * c} := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyA, hyL⟩, rfl⟩
    refine ⟨⟨y, hyA, rfl⟩, ?_⟩
    change L (r • y) ≤ r * c
    rw [map_smul]
    simpa only [smul_eq_mul] using mul_le_mul_of_nonneg_left hyL hr.le
  · rintro ⟨⟨y, hyA, hyz⟩, hzL⟩
    refine ⟨y, ⟨hyA, ?_⟩, hyz⟩
    simp only [mem_baseHalfSpaceAt]
    change L z ≤ r * c at hzL
    rw [← hyz, map_smul] at hzL
    simp only [smul_eq_mul] at hzL
    nlinarith

/-- An adapted cut at an arbitrary level preserves a strictly positive profile exactly. -/
theorem profileBody_inter_profileHalfSpace_of_pos {A : Set (Fin m → ℝ)} {g : ℝ → ℝ}
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, 0 < g t) (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) :
    profileBody A g ∩ profileHalfSpace g L c =
      profileBody (A ∩ baseHalfSpaceAt L c) g := by
  ext x
  simp only [mem_inter_iff, mem_profileBody, mem_profileHalfSpace]
  constructor
  · rintro ⟨⟨hxt, htail⟩, hcut⟩
    refine ⟨hxt, ?_⟩
    rw [smul_inter_baseHalfSpaceAt_of_pos L (hg _ hxt)]
    simpa [mul_comm] using And.intro htail hcut
  · rintro ⟨hxt, htail⟩
    rw [smul_inter_baseHalfSpaceAt_of_pos L (hg _ hxt)] at htail
    exact ⟨⟨hxt, htail.1⟩, by simpa [mul_comm] using htail.2⟩

/-- Pull a Euclidean continuous functional back to the ordinary coordinate model used by
`profileBody`. -/
def pullEuclideanLinear (L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] ℝ :=
  L.toLinearMap.comp (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap

@[simp] theorem pullEuclideanLinear_apply (L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (y : Fin m → ℝ) : pullEuclideanLinear L y = L (WithLp.toLp 2 y) := rfl

/-- Euclidean half-spaces pull back to the adapted base half-spaces used by `profileBody`. -/
theorem preimage_halfSpace_eq_baseHalfSpaceAt
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (c : ℝ) :
    (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) ⁻¹'
        halfSpace L c true = baseHalfSpaceAt (pullEuclideanLinear L) c := by
  ext y
  rfl

/-- A pair of signed transverse constraints admits a simultaneous adapted bisection.

The selected cut is already in the precise base coordinates consumed by
`profileBody_inter_profileHalfSpace_of_pos`.  Thus this is not an arbitrary ambient cut which
would destroy the affine profile. -/
theorem exists_adapted_base_bisecting_pair (h2 : 2 ≤ m)
    {A : Set (EuclideanSpace ℝ (Fin m))}
    {G H : EuclideanSpace ℝ (Fin m) → ℝ} (hA : MeasurableSet A)
    (hG : IntegrableOn G A) (hH : IntegrableOn H A)
    (hG0 : ∫ y in A, G y ≠ 0) :
    ∃ (L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (c : ℝ), L ≠ 0 ∧
      ∫ y in A ∩ halfSpace L c true, G y = (∫ y in A, G y) / 2 ∧
      ∫ y in A ∩ halfSpace L c true, H y = (∫ y in A, H y) / 2 := by
  have hfin : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := by simpa using h2
  obtain ⟨L, c, hL, hGb, hHb⟩ :=
    exists_halfSpace_bisecting_pair_of_finrank (μ := volume) hfin hA hG hH hG0
  exact ⟨L, c, hL, hGb, hHb⟩

/-- **One affine-profile localization step.**  Two signed transverse constraints are bisected,
and the corresponding cut of every strictly positive affine-profile body is an ordinary convex
ambient half-space cut with exactly the same affine-power profile over the cut base. -/
theorem exists_affineProfile_bisecting_step (h2 : 2 ≤ m)
    {A : Set (EuclideanSpace ℝ (Fin m))}
    {G H : EuclideanSpace ℝ (Fin m) → ℝ} (hAmeas : MeasurableSet A)
    (hG : IntegrableOn G A) (hH : IntegrableOn H A)
    (hG0 : ∫ y in A, G y ≠ 0) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∃ (L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (c : ℝ), L ≠ 0 ∧
      ∫ y in A ∩ halfSpace L c true, G y = (∫ y in A, G y) / 2 ∧
      ∫ y in A ∩ halfSpace L c true, H y = (∫ y in A, H y) / 2 ∧
      profileBody ((WithLp.toLp 2) ⁻¹' A) (fun t => (1 - t) * p + t * q) ∩
          profileHalfSpace (fun t => (1 - t) * p + t * q) (pullEuclideanLinear L) c =
        profileBody (((WithLp.toLp 2) ⁻¹' A) ∩
            baseHalfSpaceAt (pullEuclideanLinear L) c)
          (fun t => (1 - t) * p + t * q) ∧
      Convex ℝ (profileHalfSpace (fun t => (1 - t) * p + t * q)
        (pullEuclideanLinear L) c) := by
  obtain ⟨L, c, hL, hGb, hHb⟩ :=
    exists_adapted_base_bisecting_pair h2 hAmeas hG hH hG0
  refine ⟨L, c, hL, hGb, hHb, ?_,
    convex_profileHalfSpace_affine (pullEuclideanLinear L) c p q⟩
  apply profileBody_inter_profileHalfSpace_of_pos
  intro t ht
  rcases ht with ⟨ht0, ht1⟩
  by_cases htone : t = 1
  · subst t
    simpa using hq
  · have htlt : t < 1 := lt_of_le_of_ne ht1 htone
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr htlt) hp) (mul_nonneg ht0 hq.le)

end Arlib

#print axioms Arlib.smul_inter_baseHalfSpaceAt_of_pos
#print axioms Arlib.profileBody_inter_profileHalfSpace_of_pos
#print axioms Arlib.preimage_halfSpace_eq_baseHalfSpaceAt
#print axioms Arlib.exists_adapted_base_bisecting_pair
#print axioms Arlib.exists_affineProfile_bisecting_step
