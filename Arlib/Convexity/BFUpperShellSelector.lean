/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFUpperShellSupportInterval

/-!
# Selector integration for the BF upper-shell alternative

The rotating pencil has both an open and a closed upper-shell orientation.  Their difference is
the affine roof hyperplane, hence Haar-null.  This file packages that fact at the set-integral
level, so the strict-shell support-minimality contradiction consumes either selector output.
-/

open Set MeasureTheory
open scoped BigOperators

namespace Arlib

variable {m : ℕ}

/-- Closed counterpart of `affineUpperShell`. -/
def affineUpperShellClosed (m : ℕ) (ψ : ℝ → ℝ) (u v : ℝ) :
    Set (Fin (m + 1) → ℝ) :=
  profileBody (coordinateSimplex m) ψ ∩
    {x | u * x 0 + v ≤ ∑ i, Fin.tail x i}

theorem affineUpperShell_subset_closed (ψ : ℝ → ℝ) (u v : ℝ) :
    affineUpperShell m ψ u v ⊆ affineUpperShellClosed m ψ u v := by
  rintro x ⟨hx, hu⟩
  refine ⟨hx, ?_⟩
  change u * x 0 + v ≤ ∑ i, Fin.tail x i
  exact hu.le

/-- The roof functional is nonzero as soon as the transverse dimension is positive. -/
theorem roofCLM_neg_one_ne_zero (hm : 0 < m) (u : ℝ) :
    roofCLM (m := m) (-u) 1 ≠ 0 := by
  intro hzero
  let y : Fin m → ℝ := fun i => if i = ⟨0, hm⟩ then 1 else 0
  let x : Fin (m + 1) → ℝ := Fin.cons 0 y
  have happ : roofCLM (m := m) (-u) 1 x = 1 := by
    rw [roofCLM_apply]
    simp only [x, Fin.cons_zero, mul_zero, zero_add, one_mul,
      Fin.tail_cons, y]
    simp
  rw [hzero, zero_apply] at happ
  norm_num at happ

/-- Closed and strict upper shells differ only on the affine roof hyperplane. -/
theorem affineUpperShellClosed_diff_subset_hyperplane (ψ : ℝ → ℝ) (u v : ℝ) :
    affineUpperShellClosed m ψ u v \ affineUpperShell m ψ u v ⊆
      {x | roofCLM (m := m) (-u) 1 x = v} := by
  intro x hx
  rcases hx with ⟨⟨_hbody, hclosed⟩, hopen⟩
  change u * x 0 + v ≤ ∑ i, Fin.tail x i at hclosed
  simp only [affineUpperShell, mem_inter_iff, simplexAboveRoof, mem_setOf_eq,
    not_and_or, not_lt] at hopen
  change roofCLM (m := m) (-u) 1 x = v
  rw [roofCLM_apply]
  rcases hopen with _ | hopen
  · contradiction
  linarith

/-- Open and closed upper shells are equal almost everywhere. -/
theorem affineUpperShell_ae_eq_closed (hm : 0 < m) (ψ : ℝ → ℝ) (u v : ℝ) :
    affineUpperShell m ψ u v =ᵐ[volume] affineUpperShellClosed m ψ u v := by
  rw [ae_eq_set]
  constructor
  · rw [sdiff_eq_empty.2 (affineUpperShell_subset_closed ψ u v), measure_empty]
  · exact measure_mono_null
      (affineUpperShellClosed_diff_subset_hyperplane ψ u v)
      (measure_hyperplane_eq_zero volume (roofCLM_neg_one_ne_zero hm u) v)

/-- Consequently every selected moment is identical for the open and closed orientations. -/
theorem setIntegral_affineUpperShellClosed_eq (hm : 0 < m)
    (ψ : ℝ → ℝ) (u v : ℝ) (F : (Fin (m + 1) → ℝ) → ℝ) :
    (∫ x in affineUpperShellClosed m ψ u v, F x) =
      ∫ x in affineUpperShell m ψ u v, F x := by
  exact setIntegral_congr_set (affineUpperShell_ae_eq_closed hm ψ u v).symm

/-- The closed selector orientation inherits the exact strict-shell Fubini identity. -/
theorem setIntegral_axis_affineUpperShellClosed_eq_profileMoment
    (hm : m ≠ 0) {ψ F : ℝ → ℝ}
    (hψm : Measurable ψ) (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (u v : ℝ)
    (hint : IntegrableOn (fun x : Fin (m + 1) → ℝ => F (x 0))
      (affineUpperShell m ψ u v)) :
    (∫ x in affineUpperShellClosed m ψ u v, F (x 0)) =
      ∫ t : ℝ, upperShellSliceProfile m ψ u v t ^ m * F t := by
  rw [setIntegral_affineUpperShellClosed_eq (Nat.pos_of_ne_zero hm)]
  exact setIntegral_axis_affineUpperShell_eq_profileMoment hm hψm hψ0 u v hint

/-- A bounded coordinate-simplex profile body has finite ambient volume. -/
theorem volume_profileBody_coordinateSimplex_ne_top_of_bound {ψ : ℝ → ℝ} {B : ℝ}
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (hψB : ∀ t ∈ Icc (0 : ℝ) 1, ψ t ≤ B) :
    volume (profileBody (coordinateSimplex m) ψ) ≠ ⊤ := by
  let M := max 1 B
  let Q : Set (Fin (m + 1) → ℝ) := Set.univ.pi fun _ => Icc 0 M
  have hsub : profileBody (coordinateSimplex m) ψ ⊆ Q := by
    intro x hx i _hi
    rw [mem_profileBody_coordinateSimplex_iff hψ0] at hx
    refine Fin.cases ?_ ?_ i
    · exact ⟨hx.1.1, hx.1.2.trans (le_max_left _ _)⟩
    · intro j
      have hjle : Fin.tail x j ≤ ∑ k, Fin.tail x k :=
        Finset.single_le_sum (fun k _ => hx.2.1 k) (Finset.mem_univ j)
      exact ⟨hx.2.1 j, (hjle.trans (hx.2.2.trans (hψB _ hx.1))).trans (le_max_right _ _)⟩
  exact ne_top_of_le_ne_top
    (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_ne_top (measure_mono hsub)

/-- An upper shell cut from a bounded profile body has finite volume. -/
theorem volume_affineUpperShell_ne_top_of_bound {ψ : ℝ → ℝ} {B : ℝ}
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (hψB : ∀ t ∈ Icc (0 : ℝ) 1, ψ t ≤ B) (u v : ℝ) :
    volume (affineUpperShell m ψ u v) ≠ ⊤ := by
  exact ne_top_of_le_ne_top (volume_profileBody_coordinateSimplex_ne_top_of_bound hψ0 hψB)
    (measure_mono inter_subset_left)

/-- The closed upper-shell selector orientation yields the same shorter-candidate contradiction
as the strict orientation.  Positivity of the selected second moment supplies positive shell
volume and hence positive slice mass automatically. -/
theorem BFMovingCandidate.not_feasible_affineUpperShellClosed_of_eq_sInf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKconv : Convex ℝ K) {g h : E → ℝ}
    (c : BFMovingCandidate K g h m)
    (hmin : c.supportLength = sInf (Set.range
      (fun q : BFMovingCandidate K g h m => q.supportLength)))
    (hcne : c.left ≠ c.right) (hm : m ≠ 0)
    {ψ : ℝ → ℝ} (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hψmeas : Measurable ψ) (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    {B u v r : ℝ} (hψB : ∀ t ∈ Icc (0 : ℝ) 1, ψ t ≤ B)
    (hr : r ∈ Ioo (0 : ℝ) 1) (htouch : u * r + v = ψ r)
    (hgint : IntegrableOn (fun x : Fin (m + 1) → ℝ =>
      g (bfSegmentPoint c.left c.right (x 0))) (affineUpperShellClosed m ψ u v))
    (hhint : IntegrableOn (fun x : Fin (m + 1) → ℝ =>
      h (bfSegmentPoint c.left c.right (x 0))) (affineUpperShellClosed m ψ u v))
    (hgzero : (∫ x in affineUpperShellClosed m ψ u v,
      g (bfSegmentPoint c.left c.right (x 0))) = 0)
    (hhpos : 0 < ∫ x in affineUpperShellClosed m ψ u v,
      h (bfSegmentPoint c.left c.right (x 0))) : False := by
  have hgzero' : (∫ x in affineUpperShell m ψ u v,
      g (bfSegmentPoint c.left c.right (x 0))) = 0 := by
    rw [← setIntegral_affineUpperShellClosed_eq (Nat.pos_of_ne_zero hm)]
    exact hgzero
  have hhpos' : 0 < ∫ x in affineUpperShell m ψ u v,
      h (bfSegmentPoint c.left c.right (x 0)) := by
    rw [← setIntegral_affineUpperShellClosed_eq (Nat.pos_of_ne_zero hm)]
    exact hhpos
  have hvolpos : 0 < volume (affineUpperShell m ψ u v) := by
    rw [pos_iff_ne_zero]
    intro hz
    rw [setIntegral_measure_zero _ hz] at hhpos'
    exact lt_irrefl 0 hhpos'
  have hvolfin := volume_affineUpperShell_ne_top_of_bound (m := m) hψ0 hψB u v
  have hmass : 0 < ∫ t : ℝ,
      (volume (slice (affineUpperShell m ψ u v) t)).toReal := by
    rw [integral_volume_slice (measurableSet_affineUpperShell hψmeas hψ0 u v) hvolfin]
    exact ENNReal.toReal_pos hvolpos.ne' hvolfin
  have hSne : {t : ℝ |
      0 < volume (slice (affineUpperShell m ψ u v) t)}.Nonempty := by
    by_contra hne
    have hall : ∀ t : ℝ, volume (slice (affineUpperShell m ψ u v) t) = 0 := by
      intro t
      apply le_antisymm _ bot_le
      by_contra ht
      exact hne ⟨t, lt_of_not_ge ht⟩
    have : (∫ t : ℝ,
        (volume (slice (affineUpperShell m ψ u v) t)).toReal) = 0 := by simp [hall]
    linarith
  have hgmoment : (∫ t : ℝ,
      (volume (slice (affineUpperShell m ψ u v) t)).toReal *
      g (bfSegmentPoint c.left c.right t)) = 0 := by
    have heq := setIntegral_axis_affineUpperShell_eq_profileMoment
      (F := fun t => g (bfSegmentPoint c.left c.right t)) hm hψmeas hψ0 u v
      (hgint.mono_set (affineUpperShell_subset_closed ψ u v))
    rw [hgzero'] at heq
    simpa only [upperShellSliceProfile_pow hm] using heq.symm
  have hhmoment : 0 < ∫ t : ℝ,
      (volume (slice (affineUpperShell m ψ u v) t)).toReal *
      h (bfSegmentPoint c.left c.right t) := by
    have heq := setIntegral_axis_affineUpperShell_eq_profileMoment
      (F := fun t => h (bfSegmentPoint c.left c.right t)) hm hψmeas hψ0 u v
      (hhint.mono_set (affineUpperShell_subset_closed ψ u v))
    rw [heq] at hhpos'
    simpa only [upperShellSliceProfile_pow hm] using hhpos'
  exact c.not_feasible_affineUpperShell_of_eq_sInf hKconv hmin hcne hm hψ hψmeas hψ0
    hr htouch hSne hmass hgmoment hhmoment.le

/-! ## The flat selector on a profile body -/

/-- Raw-coordinate form of the rotating flat selector, specialized to a coordinate-simplex
profile body.  All `WithLp` transport, measurability, integrability, and integral identities are
proved internally. -/
theorem exists_profileBody_roofPencil_cut_zero_pos (hm : 0 < m)
    {ψ G H : ℝ → ℝ} (hψmeas : Measurable ψ)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (hGint : IntegrableOn (fun X : EuclideanSpace ℝ (Fin (m + 1)) =>
      G ((WithLp.ofLp X) 0))
      {X | WithLp.ofLp X ∈ profileBody (coordinateSimplex m) ψ})
    (hHint : IntegrableOn (fun X : EuclideanSpace ℝ (Fin (m + 1)) =>
      H ((WithLp.ofLp X) 0))
      {X | WithLp.ofLp X ∈ profileBody (coordinateSimplex m) ψ})
    (hGzero : (∫ x in profileBody (coordinateSimplex m) ψ, G (x 0)) = 0)
    (hHpos : 0 < ∫ x in profileBody (coordinateSimplex m) ψ, H (x 0))
    (r s : ℝ) :
    ∃ (θ : ℝ) (side : Bool),
      (∫ x in profileBody (coordinateSimplex m) ψ ∩
          halfSpace (roofCLM (m := m) (Real.cos θ)
            (Real.sin θ / Real.sqrt m)) (pencilLevel r s θ) side,
        G (x 0)) = 0 ∧
      0 < ∫ x in profileBody (coordinateSimplex m) ψ ∩
          halfSpace (roofCLM (m := m) (Real.cos θ)
            (Real.sin θ / Real.sqrt m)) (pencilLevel r s θ) side,
        H (x 0) ∧
      (Real.sin θ = 0 ∨
        ((side = true ∧ 0 < Real.sin θ) ∨ (side = false ∧ Real.sin θ < 0)) ∨
        ((side = false ∧ 0 < Real.sin θ) ∨ (side = true ∧ Real.sin θ < 0))) := by
  let P := profileBody (coordinateSimplex m) ψ
  let C : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
    {X | WithLp.ofLp X ∈ P}
  let GE : EuclideanSpace ℝ (Fin (m + 1)) → ℝ :=
    fun X => G ((WithLp.ofLp X) 0)
  let HE : EuclideanSpace ℝ (Fin (m + 1)) → ℝ :=
    fun X => H ((WithLp.ofLp X) 0)
  have hpre : (WithLp.toLp 2 : (Fin (m + 1) → ℝ) →
      EuclideanSpace ℝ (Fin (m + 1))) ⁻¹' C = P := by
    ext x
    simp [C, P]
  have hC : MeasurableSet C := by
    apply measurableSet_preimage_toLp_iff.mp
    rw [hpre]
    exact measurableSet_profileBody_coordinateSimplex hψmeas hψ0
  have hGE : IntegrableOn GE C := by simpa [GE, C, P] using hGint
  have hHE : IntegrableOn HE C := by simpa [HE, C, P] using hHint
  have hGEzero : (∫ X in C, GE X) = 0 := by
    rw [← setIntegral_preimage_toLp GE C, hpre]
    simpa only [GE, WithLp.ofLp_toLp] using hGzero
  have hHEpos : 0 < ∫ X in C, HE X := by
    rw [← setIntegral_preimage_toLp HE C, hpre]
    simpa only [HE, WithLp.ofLp_toLp] using hHpos
  obtain ⟨θ, side, hz, hp, horient⟩ := exists_coordinateRoofPencil_cut_zero_pos hm
    hC hGE hHE hGEzero hHEpos r s
  refine ⟨θ, side, ?_, ?_, horient⟩
  · simpa only [hpre, GE, WithLp.ofLp_toLp] using hz
  · simpa only [hpre, HE, WithLp.ofLp_toLp] using hp

/-- Exact geometric decoding of either upper selector orientation.  The chosen side is the
strict or closed affine upper shell, and its roof touches the prescribed profile point. -/
theorem upper_roofPencil_eq_affineUpperShell (hm : 0 < m) (ψ : ℝ → ℝ)
    {r θ : ℝ} (side : Bool)
    (hupper : (side = false ∧ 0 < Real.sin θ) ∨
      (side = true ∧ Real.sin θ < 0)) :
    ∃ u v : ℝ, u * r + v = ψ r ∧
      (profileBody (coordinateSimplex m) ψ ∩
          halfSpace (roofCLM (m := m) (Real.cos θ)
            (Real.sin θ / Real.sqrt m))
            (pencilLevel r (ψ r / Real.sqrt m) θ) side =
          affineUpperShell m ψ u v ∨
       profileBody (coordinateSimplex m) ψ ∩
          halfSpace (roofCLM (m := m) (Real.cos θ)
            (Real.sin θ / Real.sqrt m))
            (pencilLevel r (ψ r / Real.sqrt m) θ) side =
          affineUpperShellClosed m ψ u v) := by
  let den := Real.sin θ / Real.sqrt m
  let level := pencilLevel r (ψ r / Real.sqrt m) θ
  let u := -Real.cos θ / den
  let v := level / den
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hsin : Real.sin θ ≠ 0 := by
    rcases hupper with h | h
    · exact ne_of_gt h.2
    · exact ne_of_lt h.2
  have hden : den ≠ 0 := div_ne_zero hsin hsqrt.ne'
  have hell : (fun t : ℝ => (level - Real.cos θ * t) / den) =
      fun t => u * t + v := by
    funext t
    dsimp [u, v]
    field_simp
    ring
  have htouch : u * r + v = ψ r := by
    have hp := pencilRoof_touch hm (r := r) (θ := θ) (ψ := ψ) hsin
    dsimp [u, v, den, level]
    convert hp using 1 <;> ring
  refine ⟨u, v, htouch, ?_⟩
  rcases hupper with ⟨rfl, hpos⟩ | ⟨rfl, hneg⟩
  · left
    have hhalf := halfSpace_roofCLM_false_of_pos (m := m) (a := Real.cos θ)
      (b := den) (c := level) (div_pos hpos hsqrt)
    rw [hhalf, hell]
    rfl
  · right
    have hhalf := halfSpace_roofCLM_true_of_neg (m := m) (a := Real.cos θ)
      (b := den) (c := level) (div_neg_of_neg_of_pos hneg hsqrt)
    rw [hhalf]
    ext x
    simp only [affineUpperShellClosed, mem_inter_iff, mem_setOf_eq]
    rw [← congrFun hell (x 0)]

/-- **Selector capstone for the upper branch.**  Applying the rotating flat selector to a
support-minimizing candidate can return only the vertical or lower-roof orientations: either
upper orientation is decoded as a touching strict/closed upper shell and contradicted by
`not_feasible_affineUpperShellClosed_of_eq_sInf`. -/
theorem BFMovingCandidate.exists_roofPencil_cut_not_upper
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
    ∃ (θ : ℝ) (side : Bool),
      (∫ x in profileBody (coordinateSimplex m) c.profile ∩
          halfSpace (roofCLM (m := m) (Real.cos θ)
            (Real.sin θ / Real.sqrt m))
            (pencilLevel r (c.profile r / Real.sqrt m) θ) side,
        g (bfSegmentPoint c.left c.right (x 0))) = 0 ∧
      0 < ∫ x in profileBody (coordinateSimplex m) c.profile ∩
          halfSpace (roofCLM (m := m) (Real.cos θ)
            (Real.sin θ / Real.sqrt m))
            (pencilLevel r (c.profile r / Real.sqrt m) θ) side,
        h (bfSegmentPoint c.left c.right (x 0)) ∧
      (Real.sin θ = 0 ∨
        ((side = true ∧ 0 < Real.sin θ) ∨
          (side = false ∧ Real.sin θ < 0))) := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ c.profile t :=
    fun t _ => c.profile_nonneg t
  have hGtotal : (∫ x in profileBody (coordinateSimplex m) c.profile,
      g (bfSegmentPoint c.left c.right (x 0))) = 0 := by
    have heq := setIntegral_axis_profileBody_coordinateSimplex_of_support
      (F := fun t => g (bfSegmentPoint c.left c.right t)) hm0
      c.profile_measurable hψ0 c.profile_off hGint
    rw [c.g_zero, mul_zero] at heq
    exact heq
  have hHtotal : 0 < ∫ x in profileBody (coordinateSimplex m) c.profile,
      h (bfSegmentPoint c.left c.right (x 0)) := by
    have heq := setIntegral_axis_profileBody_coordinateSimplex_of_support
      (F := fun t => h (bfSegmentPoint c.left c.right t)) hm0
      c.profile_measurable hψ0 c.profile_off hHint
    rw [heq]
    exact mul_pos (volume_coordinateSimplex_toReal_pos (m := m)) hHstrict
  obtain ⟨θ, side, hz, hp, horient⟩ := exists_profileBody_roofPencil_cut_zero_pos
    (G := fun t => g (bfSegmentPoint c.left c.right t))
    (H := fun t => h (bfSegmentPoint c.left c.right t)) hm
    c.profile_measurable hψ0 hGEint hHEint hGtotal hHtotal r
      (c.profile r / Real.sqrt m)
  refine ⟨θ, side, hz, hp, ?_⟩
  rcases horient with hzero | hlower | hupper
  · exact Or.inl hzero
  · exact Or.inr hlower
  · exfalso
    obtain ⟨u, v, htouch, hset⟩ :=
      upper_roofPencil_eq_affineUpperShell hm c.profile side hupper
    have hgintClosed : IntegrableOn (fun x : Fin (m + 1) → ℝ =>
        g (bfSegmentPoint c.left c.right (x 0)))
        (affineUpperShellClosed m c.profile u v) :=
      hGint.mono_set inter_subset_left
    have hhintClosed : IntegrableOn (fun x : Fin (m + 1) → ℝ =>
        h (bfSegmentPoint c.left c.right (x 0)))
        (affineUpperShellClosed m c.profile u v) :=
      hHint.mono_set inter_subset_left
    have hzClosed : (∫ x in affineUpperShellClosed m c.profile u v,
        g (bfSegmentPoint c.left c.right (x 0))) = 0 := by
      rcases hset with hstrict | hclosedSet
      · rw [setIntegral_affineUpperShellClosed_eq hm]
        rw [← hstrict]
        exact hz
      · rw [← hclosedSet]
        exact hz
    have hpClosed : 0 < ∫ x in affineUpperShellClosed m c.profile u v,
        h (bfSegmentPoint c.left c.right (x 0)) := by
      rcases hset with hstrict | hclosedSet
      · rw [setIntegral_affineUpperShellClosed_eq hm]
        rw [← hstrict]
        exact hp
      · rw [← hclosedSet]
        exact hp
    exact c.not_feasible_affineUpperShellClosed_of_eq_sInf
      (B := bfNormalizedProfileBound m) hKconv hmin hcne hm0
      hclosed c.profile_measurable hψ0 (fun t _ => c.profile_bound t) hr htouch
      hgintClosed hhintClosed hzClosed hpClosed

end Arlib

#print axioms Arlib.roofCLM_neg_one_ne_zero
#print axioms Arlib.affineUpperShell_ae_eq_closed
#print axioms Arlib.setIntegral_affineUpperShellClosed_eq
#print axioms Arlib.setIntegral_axis_affineUpperShellClosed_eq_profileMoment
#print axioms Arlib.volume_profileBody_coordinateSimplex_ne_top_of_bound
#print axioms Arlib.BFMovingCandidate.not_feasible_affineUpperShellClosed_of_eq_sInf
#print axioms Arlib.exists_profileBody_roofPencil_cut_zero_pos
#print axioms Arlib.upper_roofPencil_eq_affineUpperShell
#print axioms Arlib.BFMovingCandidate.exists_roofPencil_cut_not_upper
