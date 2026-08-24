/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFExtremalProfile

/-!
# The simplex slice calculation in BF's first extremal case

BF realizes a concave profile `ψ` by simplices
`{y ≥ 0 | ∑ yᵢ ≤ ψ(t)}`.  Cutting by the affine roof `∑ yᵢ ≤ ℓ(t)` replaces the profile by
`min ψ ℓ`.  This file proves that identity as an equality of sets, including the scaling step
which is often left implicit in the paper.
-/

open Set
open scoped Pointwise BigOperators

namespace Arlib

variable {m : ℕ}

/-- The standard coordinate simplex in the transverse space. -/
def coordinateSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}

/-- The roof cut used in the BF simplex construction. -/
def simplexRoof (ell : ℝ → ℝ) : Set (Fin (m + 1) → ℝ) :=
  {x | ∑ i, Fin.tail x i ≤ ell (x 0)}

@[simp] theorem mem_coordinateSimplex {y : Fin m → ℝ} :
    y ∈ coordinateSimplex m ↔ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1 := Iff.rfl

@[simp] theorem mem_simplexRoof {ell : ℝ → ℝ} {x : Fin (m + 1) → ℝ} :
    x ∈ simplexRoof ell ↔ ∑ i, Fin.tail x i ≤ ell (x 0) := Iff.rfl

/-- A nonnegative dilation of the standard simplex is exactly the coordinate simplex of that
height, including the degenerate zero-height slice. -/
theorem mem_smul_coordinateSimplex_iff {r : ℝ} (hr : 0 ≤ r) {y : Fin m → ℝ} :
    y ∈ r • coordinateSimplex m ↔ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ r := by
  rcases hr.eq_or_lt with rfl | hr
  · constructor
    · rintro ⟨z, -, rfl⟩
      simp
    · rintro ⟨hy0, hysum⟩
      have hsum0 : ∑ i, y i = 0 :=
        le_antisymm hysum (Finset.sum_nonneg fun i _ => hy0 i)
      have hyzero : y = 0 := by
        ext i
        have hyi : y i ≤ ∑ j, y j :=
          Finset.single_le_sum (fun j _ => hy0 j) (Finset.mem_univ i)
        simp only [Pi.zero_apply]
        linarith [hy0 i]
      subst y
      refine ⟨0, ?_, by simp⟩
      simp [coordinateSimplex]
  constructor
  · rintro ⟨z, hz, rfl⟩
    constructor
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hr.le (hz.1 i)
    · simp only [Pi.smul_apply, smul_eq_mul]
      calc
        ∑ i, r * z i = r * ∑ i, z i := by rw [Finset.mul_sum]
        _ ≤ r * 1 := mul_le_mul_of_nonneg_left hz.2 hr.le
        _ = r := mul_one r
  · rintro ⟨hy0, hysum⟩
    refine ⟨r⁻¹ • y, ?_, ?_⟩
    · constructor
      · intro i
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.mpr hr.le) (hy0 i)
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [← Finset.mul_sum]
        exact (inv_mul_le_one₀ hr).mpr hysum
    · ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp

/-- Membership in a positive simplex-profile body, without a hidden scaling witness. -/
theorem mem_profileBody_coordinateSimplex_iff {ψ : ℝ → ℝ}
    (hψ : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) {x : Fin (m + 1) → ℝ} :
    x ∈ profileBody (coordinateSimplex m) ψ ↔
      x 0 ∈ Icc (0 : ℝ) 1 ∧ (∀ i, 0 ≤ Fin.tail x i) ∧
        ∑ i, Fin.tail x i ≤ ψ (x 0) := by
  rw [mem_profileBody]
  constructor
  · rintro ⟨hxt, htail⟩
    exact ⟨hxt, (mem_smul_coordinateSimplex_iff (hψ _ hxt)).mp htail⟩
  · rintro ⟨hxt, htail⟩
    exact ⟨hxt, (mem_smul_coordinateSimplex_iff (hψ _ hxt)).mpr htail⟩

/-- **BF simplex/pencil profile identity.**  Intersecting the simplex-profile body of `ψ` with
the roof below `ell` gives exactly the simplex-profile body of `min ψ ell`.

Strict positivity is the regularized finite-stage regime of the source proof and avoids a
separate zero-height simplex degeneration. -/
theorem profileBody_coordinateSimplex_inter_roof {ψ ell : ℝ → ℝ}
    (hψ : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (hell : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ell t) :
    profileBody (coordinateSimplex m) ψ ∩ simplexRoof ell =
      profileBody (coordinateSimplex m) (fun t => min (ψ t) (ell t)) := by
  ext x
  rw [mem_inter_iff, mem_profileBody_coordinateSimplex_iff hψ,
    mem_simplexRoof,
    mem_profileBody_coordinateSimplex_iff
      (fun t ht => le_min (hψ t ht) (hell t ht))]
  constructor
  · rintro ⟨⟨hxt, hnonneg, hψsum⟩, hellsum⟩
    exact ⟨hxt, hnonneg, le_min hψsum hellsum⟩
  · rintro ⟨hxt, hnonneg, hminsum⟩
    exact ⟨⟨hxt, hnonneg, hminsum.trans (min_le_left _ _)⟩,
      hminsum.trans (min_le_right _ _)⟩

/-- The first BF clipping operation is literally the roof cut of the simplex-profile body. -/
theorem profileBody_coordinateSimplex_inter_constantRoof {ψ : ℝ → ℝ} {τ : ℝ}
    (hψ : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) (hτ : 0 ≤ τ) :
    profileBody (coordinateSimplex m) ψ ∩ simplexRoof (fun _ => τ) =
      profileBody (coordinateSimplex m) (clippedProfile ψ τ) := by
  change profileBody (coordinateSimplex m) ψ ∩ simplexRoof (fun _ => τ) =
    profileBody (coordinateSimplex m) (fun t => min (ψ t) τ)
  exact profileBody_coordinateSimplex_inter_roof hψ (fun _ _ => hτ)

/-- **The complete geometric part of BF case 1.**  If the concave simplex profile vanishes at
both endpoints and is positive inside, then a constant roof cut preserves its open support and
produces a profile affine on an interval strictly longer than any fixed candidate interval of
length below one.  The cut-body identity is literal, not merely an equality of slice volumes. -/
theorem exists_constantRoof_cut_longer_affine_core {ψ : ℝ → ℝ}
    (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0)
    (hψpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < ψ t)
    {a b : ℝ} (hab0 : 0 ≤ b - a) (hab : b - a < 1) :
    ∃ δ τ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ 0 < τ ∧
      b - a < (1 - δ) - δ ∧
      profileBody (coordinateSimplex m) ψ ∩ simplexRoof (fun _ => τ) =
        profileBody (coordinateSimplex m) (clippedProfile ψ τ) ∧
      ConcaveOn ℝ (Icc (0 : ℝ) 1) (clippedProfile ψ τ) ∧
      clippedProfile ψ τ 0 = 0 ∧ clippedProfile ψ τ 1 = 0 ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, 0 < clippedProfile ψ τ t) ∧
      ProfileAffineOn (clippedProfile ψ τ) δ (1 - δ) := by
  let δ : ℝ := (1 - (b - a)) / 4
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  have hδhalf : δ < 1 / 2 := by dsimp [δ]; linarith
  obtain ⟨τ, hτ, hconc, hz0, hz1, hpos, haff⟩ :=
    exists_clippedProfile_affine_core hψ hψ0 hψ1 hψpos hδ0 hδhalf
  have hψnonneg : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · rw [hψ0]
    rcases eq_or_lt_of_le ht.2 with rfl | ht1
    · rw [hψ1]
    exact (hψpos t ⟨ht0, ht1⟩).le
  refine ⟨δ, τ, hδ0, hδhalf, hτ, ?_,
    profileBody_coordinateSimplex_inter_constantRoof hψnonneg hτ.le,
    hconc, hz0, hz1, hpos, haff⟩
  dsimp [δ]
  linarith

end Arlib

#print axioms Arlib.mem_smul_coordinateSimplex_iff
#print axioms Arlib.mem_profileBody_coordinateSimplex_iff
#print axioms Arlib.profileBody_coordinateSimplex_inter_roof
#print axioms Arlib.profileBody_coordinateSimplex_inter_constantRoof
#print axioms Arlib.exists_constantRoof_cut_longer_affine_core
