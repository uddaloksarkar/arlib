/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFSupportMinimalityPencil

/-!
# Slice profile and support geometry of the BF upper-shell alternative

For an affine roof touching a concave profile at an interior height `r`, the part of the
simplex-profile body above that roof cannot have positive-volume slices on both sides of `r`.
This file proves that support-shrink statement and packages the exact slice-volume-root profile
and Fubini identity for the selected upper shell.
-/

open Set MeasureTheory
open scoped BigOperators

namespace Arlib

variable {m : ℕ}

/-- The coordinate simplex is convex. -/
theorem convex_coordinateSimplex : Convex ℝ (coordinateSimplex m) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by linarith

@[simp] theorem zero_mem_coordinateSimplex : (0 : Fin m → ℝ) ∈ coordinateSimplex m := by
  simp [coordinateSimplex]

/-- The open side above an affine roof is a convex halfspace. -/
theorem convex_simplexAboveRoof_affine (u v : ℝ) :
    Convex ℝ (simplexAboveRoof (fun t => u * t + v) : Set (Fin (m + 1) → ℝ)) := by
  have heq : simplexAboveRoof (fun t => u * t + v) =
      halfSpace (roofCLM (m := m) (-u) 1) v false := by
    ext x
    simp only [simplexAboveRoof, mem_setOf_eq, halfSpace_false, roofCLM_apply]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact convex_halfSpace _ _ _

theorem measurableSet_simplexAboveRoof_affine (u v : ℝ) :
    MeasurableSet (simplexAboveRoof (fun t => u * t + v) :
      Set (Fin (m + 1) → ℝ)) := by
  have heq : simplexAboveRoof (fun t => u * t + v) =
      halfSpace (roofCLM (m := m) (-u) 1) v false := by
    ext x
    simp only [simplexAboveRoof, mem_setOf_eq, halfSpace_false, roofCLM_apply]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact measurableSet_halfSpace _ _ _

/-- The selected part of a simplex-profile body lying strictly above an affine roof. -/
def affineUpperShell (m : ℕ) (ψ : ℝ → ℝ) (u v : ℝ) :
    Set (Fin (m + 1) → ℝ) :=
  profileBody (coordinateSimplex m) ψ ∩ simplexAboveRoof (fun t => u * t + v)

theorem measurableSet_affineUpperShell {ψ : ℝ → ℝ} (hψm : Measurable ψ)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) (u v : ℝ) :
    MeasurableSet (affineUpperShell m ψ u v) :=
  (measurableSet_profileBody_coordinateSimplex hψm hψ0).inter
    (measurableSet_simplexAboveRoof_affine u v)

theorem convex_affineUpperShell {ψ : ℝ → ℝ}
    (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) (u v : ℝ) :
    Convex ℝ (affineUpperShell m ψ u v) :=
  (convex_profileBody convex_coordinateSimplex zero_mem_coordinateSimplex hψ hψ0).inter
    (convex_simplexAboveRoof_affine u v)

/-! ## Touching geometry -/

/-- Every nonvertical roof in the normalized pencil through
`(r, ψ(r)/√m)` touches the profile at height `r`. -/
theorem pencilRoof_touch (hm : 0 < m) {ψ : ℝ → ℝ} (r θ : ℝ)
    (hsin : Real.sin θ ≠ 0) :
    (pencilLevel r (ψ r / Real.sqrt m) θ - Real.cos θ * r) /
        (Real.sin θ / Real.sqrt m) = ψ r := by
  have hsqrt : Real.sqrt (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hm))
  unfold pencilLevel
  field_simp
  ring

/-- A concave graph and an affine function touching at `r` cannot have the graph strictly above
the affine function at points on both sides of `r`. -/
theorem affine_touch_not_above_both_sides {ψ : ℝ → ℝ}
    (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ) {u v r x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxr : x < r) (hry : r < y) (htouch : u * r + v = ψ r)
    (hxa : u * x + v < ψ x) (hya : u * y + v < ψ y) : False := by
  have hyx : 0 < y - x := by linarith
  let a : ℝ := (y - r) / (y - x)
  let b : ℝ := (r - x) / (y - x)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ha' : 0 < a := by dsimp [a]; positivity
  have hb' : 0 < b := by dsimp [b]; positivity
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp
    ring
  have hr : a * x + b * y = r := by
    dsimp [a, b]
    field_simp
    ring
  have hconc := hψ.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hconc
  rw [hr, ← htouch] at hconc
  have haff : a * (u * x + v) + b * (u * y + v) = u * r + v := by
    rw [← hr]
    linear_combination v * hab
  have hstrict : a * (u * x + v) + b * (u * y + v) <
      a * ψ x + b * ψ y :=
    add_lt_add (mul_lt_mul_of_pos_left hxa ha') (mul_lt_mul_of_pos_left hya hb')
  linarith

/-- Consequently the strict-above set of a touching affine roof lies entirely on one side of
the touching height. -/
theorem affine_touch_above_set_oneSided {ψ : ℝ → ℝ}
    (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ) {u v r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (htouch : u * r + v = ψ r) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ u * t + v < ψ t} ⊆ Iio r ∨
      {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ u * t + v < ψ t} ⊆ Ioi r := by
  let S := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ u * t + v < ψ t}
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hxr : x < r ∨ r < x := by
      rcases lt_trichotomy x r with h | h | h
      · exact Or.inl h
      · subst x
        exact False.elim (lt_irrefl (ψ r) (by simpa [htouch] using hx.2))
      · exact Or.inr h
    rcases hxr with hleft | hright
    · left
      intro y hy
      rw [mem_Iio]
      by_contra hnot
      have hry : r < y := lt_of_le_of_ne (le_of_not_gt hnot) (by
        intro hyr
        subst y
        exact lt_irrefl (ψ r) (by simpa [htouch] using hy.2))
      exact affine_touch_not_above_both_sides hψ hx.1 hy.1 hleft hry htouch hx.2 hy.2
    · right
      intro y hy
      rw [mem_Ioi]
      by_contra hnot
      have hyr : y < r := lt_of_le_of_ne (le_of_not_gt hnot) (by
        intro hyr
        subst y
        exact lt_irrefl (ψ r) (by simpa [htouch] using hy.2))
      exact affine_touch_not_above_both_sides hψ hy.1 hx.1 hyr hright htouch hy.2 hx.2
  · left
    intro x hx
    exact False.elim (hS ⟨x, hx⟩)

/-! ## Positive slice support and slice profile -/

/-- A nonempty upper-shell slice forces the roof to lie strictly below the profile. -/
theorem affineUpperShell_slice_nonempty_imp {ψ : ℝ → ℝ}
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) {u v t : ℝ}
    (hne : (slice (affineUpperShell m ψ u v) t).Nonempty) :
    t ∈ Icc (0 : ℝ) 1 ∧ u * t + v < ψ t := by
  obtain ⟨y, hy⟩ := hne
  have hbody := hy.1
  have habove := hy.2
  rw [mem_profileBody_coordinateSimplex_iff hψ0] at hbody
  simp only [simplexAboveRoof, mem_setOf_eq, Fin.cons_zero, Fin.tail_cons] at habove
  exact ⟨hbody.1, habove.trans_le hbody.2.2⟩

/-- Positive slice volume in particular forces strict graph-above-roof. -/
theorem affineUpperShell_slice_volume_pos_imp {ψ : ℝ → ℝ}
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) {u v t : ℝ}
    (hpos : 0 < volume (slice (affineUpperShell m ψ u v) t)) :
    t ∈ Icc (0 : ℝ) 1 ∧ u * t + v < ψ t := by
  apply affineUpperShell_slice_nonempty_imp hψ0
  by_contra hempty
  rw [not_nonempty_iff_eq_empty.mp hempty, measure_empty] at hpos
  exact lt_irrefl 0 hpos

/-- **The upper-shell support-shrink lemma.**  If the pencil roof passes through the boundary
flat at `(r,ψ(r))`, every positive-volume slice of the selected upper shell lies to one side of
`r`.  Since `r∈(0,1)`, either possible physical parameter span is strictly below one. -/
theorem affineUpperShell_positiveSliceSupport_shrinks {ψ : ℝ → ℝ}
    (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) {u v r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (htouch : u * r + v = ψ r) :
    {t : ℝ | 0 < volume (slice (affineUpperShell m ψ u v) t)} ⊆ Ico 0 r ∨
      {t : ℝ | 0 < volume (slice (affineUpperShell m ψ u v) t)} ⊆ Ioc r 1 := by
  rcases affine_touch_above_set_oneSided hψ hr htouch with hleft | hright
  · left
    intro t ht
    have h := affineUpperShell_slice_volume_pos_imp hψ0 ht
    exact ⟨h.1.1, hleft h⟩
  · right
    intro t ht
    have h := affineUpperShell_slice_volume_pos_imp hψ0 ht
    exact ⟨hright h, h.1.2⟩

/-- Pencil-coordinate specialization of the upper-shell support-shrink lemma. -/
theorem pencilUpperShell_positiveSliceSupport_shrinks (hm : 0 < m)
    {ψ : ℝ → ℝ} (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) {r θ : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (hsin : Real.sin θ ≠ 0) :
    let den := Real.sin θ / Real.sqrt m
    let c := pencilLevel r (ψ r / Real.sqrt m) θ
    {t : ℝ | 0 < volume (slice (affineUpperShell m ψ
      (-Real.cos θ / den) (c / den)) t)} ⊆ Ico 0 r ∨
    {t : ℝ | 0 < volume (slice (affineUpperShell m ψ
      (-Real.cos θ / den) (c / den)) t)} ⊆ Ioc r 1 := by
  dsimp only
  apply affineUpperShell_positiveSliceSupport_shrinks hψ hψ0 hr
  have ht := pencilRoof_touch hm (r := r) (θ := θ) (ψ := ψ) hsin
  convert ht using 1 <;> ring

/-- The `m`-th root of the upper-shell slice volume. -/
noncomputable def upperShellSliceProfile (m : ℕ) (ψ : ℝ → ℝ) (u v t : ℝ) : ℝ :=
  (volume (slice (affineUpperShell m ψ u v) t)).toReal ^ (1 / (m : ℝ))

theorem measurable_upperShellSliceProfile {ψ : ℝ → ℝ}
    (hψm : Measurable ψ) (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) (u v : ℝ) :
    Measurable (upperShellSliceProfile m ψ u v) := by
  unfold upperShellSliceProfile
  exact (measurable_volume_slice_toReal
    (measurableSet_affineUpperShell hψm hψ0 u v)).pow measurable_const

theorem upperShellSliceProfile_nonneg (ψ : ℝ → ℝ) (u v t : ℝ) :
    0 ≤ upperShellSliceProfile m ψ u v t := by
  unfold upperShellSliceProfile
  positivity

theorem upperShellSliceProfile_pow (hm : m ≠ 0) {ψ : ℝ → ℝ} {u v t : ℝ} :
    upperShellSliceProfile m ψ u v t ^ m =
      (volume (slice (affineUpperShell m ψ u v) t)).toReal := by
  unfold upperShellSliceProfile
  rw [one_div]
  exact Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg hm

/-- Brunn concavity of the upper-shell profile on any convex interval of nonempty finite slices. -/
theorem concaveOn_upperShellSliceProfile (hm : m ≠ 0) {ψ : ℝ → ℝ}
    (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hψm : Measurable ψ) (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (u v : ℝ) {S : Set ℝ} (hS : Convex ℝ S)
    (hne : ∀ t ∈ S, (slice (affineUpperShell m ψ u v) t).Nonempty)
    (hfin : ∀ t ∈ S, volume (slice (affineUpperShell m ψ u v) t) ≠ ⊤) :
    ConcaveOn ℝ S (upperShellSliceProfile m ψ u v) := by
  exact brunn_slice_concaveOn hm (convex_affineUpperShell hψ hψ0 u v)
    (measurableSet_affineUpperShell hψm hψ0 u v) hS hne hfin

/-- **Exact Fubini/moment identity for the upper-shell alternative.** -/
theorem setIntegral_axis_affineUpperShell_eq_profileMoment
    (hm : m ≠ 0) {ψ F : ℝ → ℝ}
    (hψm : Measurable ψ) (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (u v : ℝ)
    (hint : IntegrableOn (fun x : Fin (m + 1) → ℝ => F (x 0))
      (affineUpperShell m ψ u v)) :
    (∫ x in affineUpperShell m ψ u v, F (x 0)) =
      ∫ t : ℝ, upperShellSliceProfile m ψ u v t ^ m * F t := by
  have hD := measurableSet_affineUpperShell (m := m) hψm hψ0 u v
  rw [setIntegral_eq_integral_slice hD hint]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun t => ?_
  simp only [Fin.cons_zero]
  rw [setIntegral_const, smul_eq_mul, Measure.real,
    upperShellSliceProfile_pow hm]

end Arlib

#print axioms Arlib.affine_touch_not_above_both_sides
#print axioms Arlib.pencilRoof_touch
#print axioms Arlib.affine_touch_above_set_oneSided
#print axioms Arlib.affineUpperShell_positiveSliceSupport_shrinks
#print axioms Arlib.pencilUpperShell_positiveSliceSupport_shrinks
#print axioms Arlib.concaveOn_upperShellSliceProfile
#print axioms Arlib.setIntegral_axis_affineUpperShell_eq_profileMoment
