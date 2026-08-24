/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFAffineCoreAttainment
import Arlib.Convexity.SignedCut

/-!
# Fubini and orientation interfaces for BF rotating roof cuts

This file connects the geometric simplex-profile identities to the signed-integral cut API.
Axis-dependent integrals over a simplex-profile body are exactly the corresponding one-dimensional
profile moments, times the fixed volume of the coordinate simplex.  It also classifies every
height/tail-sum halfspace by the sign of its transverse coefficient.
-/

open Set MeasureTheory
open scoped BigOperators

namespace Arlib

variable {m : ℕ}

/-- Coordinate-simplex profile bodies are measurable for measurable profiles. -/
theorem measurableSet_profileBody_coordinateSimplex {ψ : ℝ → ℝ} (hψm : Measurable ψ)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) :
    MeasurableSet (profileBody (coordinateSimplex m) ψ) := by
  have heq : profileBody (coordinateSimplex m) ψ =
      {x : Fin (m + 1) → ℝ | x 0 ∈ Icc (0 : ℝ) 1 ∧
        (∀ i, 0 ≤ Fin.tail x i) ∧ ∑ i, Fin.tail x i ≤ ψ (x 0)} := by
    ext x
    exact mem_profileBody_coordinateSimplex_iff hψ0
  rw [heq]
  measurability

/-- A height outside `[0,1]` has an empty profile-body slice. -/
theorem slice_profileBody_eq_empty_of_notMem {A : Set (Fin m → ℝ)} {ψ : ℝ → ℝ} {t : ℝ}
    (ht : t ∉ Icc (0 : ℝ) 1) : slice (profileBody A ψ) t = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun y hy => ?_
  exact ht hy.1

/-- **Exact BF Fubini identity.**  The ambient axis integral is the one-dimensional
`ψ^m`-moment times the fixed transverse simplex volume.  The support assumption is necessary:
`profileBody` ignores `ψ` off `[0,1]`, whereas the whole-line moment does not. -/
theorem setIntegral_axis_profileBody_coordinateSimplex_of_support
    {ψ F : ℝ → ℝ} (hm : m ≠ 0) (hψm : Measurable ψ)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (hψoff : ∀ t, t ∉ Icc (0 : ℝ) 1 → ψ t = 0)
    (hint : IntegrableOn (fun x : Fin (m + 1) → ℝ => F (x 0))
      (profileBody (coordinateSimplex m) ψ)) :
    (∫ x in profileBody (coordinateSimplex m) ψ, F (x 0)) =
      (volume (coordinateSimplex m)).toReal * ∫ t : ℝ, ψ t ^ m * F t := by
  have hKm := measurableSet_profileBody_coordinateSimplex (m := m) hψm hψ0
  rw [setIntegral_eq_integral_slice hKm hint]
  have hslices : (fun t : ℝ =>
      ∫ y in slice (profileBody (coordinateSimplex m) ψ) t,
        F ((Fin.cons t y : Fin (m + 1) → ℝ) 0)) =
      fun t => (volume (coordinateSimplex m)).toReal * (ψ t ^ m * F t) := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simp only [Fin.cons_zero]
      rw [setIntegral_const, smul_eq_mul, Measure.real,
        volume_slice_profileBody ht (hψ0 t ht), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg (hψ0 t ht) m)]
      ring
    · rw [slice_profileBody_eq_empty_of_notMem ht, hψoff t ht]
      simp [hm]
  rw [hslices, integral_const_mul]

/-- The coordinate simplex has finite volume. -/
theorem volume_coordinateSimplex_ne_top : volume (coordinateSimplex m) ≠ ⊤ := by
  have hsub : coordinateSimplex m ⊆ Set.univ.pi fun _ : Fin m => Icc (0 : ℝ) 1 := by
    intro y hy i _
    refine ⟨hy.1 i, ?_⟩
    exact (Finset.single_le_sum (fun j _ => hy.1 j) (Finset.mem_univ i)).trans hy.2
  have hle : volume (coordinateSimplex m) ≤
      volume (Set.univ.pi fun _ : Fin m => Icc (0 : ℝ) 1) := measure_mono hsub
  have hbox : volume (Set.univ.pi fun _ : Fin m => Icc (0 : ℝ) 1) = 1 := by
    rw [volume_pi_pi]
    simp [Real.volume_Icc]
  rw [hbox] at hle
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle

/-- The coordinate simplex has strictly positive volume. -/
theorem volume_coordinateSimplex_pos : 0 < volume (coordinateSimplex m) := by
  let r : ℝ := 1 / (m + 1 : ℝ)
  let B : Set (Fin m → ℝ) := Set.univ.pi fun _ => Icc (0 : ℝ) r
  have hr : 0 < r := by dsimp [r]; positivity
  have hsub : B ⊆ coordinateSimplex m := by
    intro y hy
    refine ⟨fun i => (hy i (Set.mem_univ i)).1, ?_⟩
    calc
      ∑ i, y i ≤ ∑ _i : Fin m, r := Finset.sum_le_sum fun i _ => (hy i (Set.mem_univ i)).2
      _ = (m : ℝ) * r := by simp
      _ ≤ 1 := by
        dsimp [r]
        calc
          (m : ℝ) * (1 / (m + 1 : ℝ)) = (m : ℝ) / (m + 1 : ℝ) := by ring
          _ ≤ 1 := (div_le_one (by positivity : (0 : ℝ) < m + 1)).mpr (by norm_num)
  have hB : 0 < volume B := by
    dsimp [B]
    rw [volume_pi_pi]
    simp only [Real.volume_Icc, sub_zero]
    rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i hi
    exact (ENNReal.ofReal_pos.mpr hr).ne'
  exact hB.trans_le (measure_mono hsub)

theorem volume_coordinateSimplex_toReal_pos :
    0 < (volume (coordinateSimplex m)).toReal :=
  ENNReal.toReal_pos (volume_coordinateSimplex_pos (m := m)).ne'
    (volume_coordinateSimplex_ne_top (m := m))

/-! ## Fubini after a roof cut -/

/-- The cut profile, extended by zero outside the unit interval. -/
noncomputable def roofCutProfile (ψ ell : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ∈ Icc (0 : ℝ) 1 then min (ψ t) (ell t) else 0

theorem measurable_roofCutProfile {ψ ell : ℝ → ℝ} (hψ : Measurable ψ)
    (hell : Measurable ell) : Measurable (roofCutProfile ψ ell) := by
  unfold roofCutProfile
  exact (hψ.min hell).ite measurableSet_Icc measurable_const

@[simp] theorem roofCutProfile_of_mem {ψ ell : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : roofCutProfile ψ ell t = min (ψ t) (ell t) := by
  simp [roofCutProfile, ht]

@[simp] theorem roofCutProfile_of_notMem {ψ ell : ℝ → ℝ} {t : ℝ}
    (ht : t ∉ Icc (0 : ℝ) 1) : roofCutProfile ψ ell t = 0 := by
  simp [roofCutProfile, ht]

/-- A roof cut is the profile body of the zero-extended minimum profile. -/
theorem profileBody_coordinateSimplex_inter_roofCutProfile {ψ ell : ℝ → ℝ}
    (hψ : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (hell : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ell t) :
    profileBody (coordinateSimplex m) ψ ∩ simplexRoof ell =
      profileBody (coordinateSimplex m) (roofCutProfile ψ ell) := by
  rw [profileBody_coordinateSimplex_inter_roof hψ hell]
  ext x
  simp only [mem_profileBody]
  constructor
  · rintro ⟨ht, hx⟩
    refine ⟨ht, ?_⟩
    simpa [roofCutProfile, ht] using hx
  · rintro ⟨ht, hx⟩
    refine ⟨ht, ?_⟩
    simpa [roofCutProfile, ht] using hx

/-- Exact profile-moment identity for the lower side of an affine roof cut. -/
theorem setIntegral_axis_inter_simplexRoof
    {ψ ell F : ℝ → ℝ} (hm : m ≠ 0)
    (hψm : Measurable ψ) (hellm : Measurable ell)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (hell0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ell t)
    (hint : IntegrableOn (fun x : Fin (m + 1) → ℝ => F (x 0))
      (profileBody (coordinateSimplex m) ψ ∩ simplexRoof ell)) :
    (∫ x in profileBody (coordinateSimplex m) ψ ∩ simplexRoof ell, F (x 0)) =
      (volume (coordinateSimplex m)).toReal *
        ∫ t : ℝ, roofCutProfile ψ ell t ^ m * F t := by
  rw [profileBody_coordinateSimplex_inter_roofCutProfile hψ0 hell0] at hint ⊢
  exact setIntegral_axis_profileBody_coordinateSimplex_of_support (m := m) hm
    (measurable_roofCutProfile hψm hellm)
    (fun t ht => by rw [roofCutProfile_of_mem ht]; exact le_min (hψ0 t ht) (hell0 t ht))
    (fun t ht => roofCutProfile_of_notMem ht) hint

/-- **Constraint-preserving roof interface.**  Any selected lower roof side carrying zero and
positive ambient moments yields exactly the corresponding one-dimensional feasible profile. -/
theorem roofCutProfile_constraints_of_ambient
    {ψ ell F G : ℝ → ℝ} (hm : m ≠ 0)
    (hψm : Measurable ψ) (hellm : Measurable ell)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (hell0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ell t)
    (hFint : IntegrableOn (fun x : Fin (m + 1) → ℝ => F (x 0))
      (profileBody (coordinateSimplex m) ψ ∩ simplexRoof ell))
    (hGint : IntegrableOn (fun x : Fin (m + 1) → ℝ => G (x 0))
      (profileBody (coordinateSimplex m) ψ ∩ simplexRoof ell))
    (hFzero : (∫ x in profileBody (coordinateSimplex m) ψ ∩ simplexRoof ell, F (x 0)) = 0)
    (hGpos : 0 < ∫ x in profileBody (coordinateSimplex m) ψ ∩ simplexRoof ell, G (x 0)) :
    (∫ t : ℝ, roofCutProfile ψ ell t ^ m * F t) = 0 ∧
      0 < ∫ t : ℝ, roofCutProfile ψ ell t ^ m * G t := by
  have hF := setIntegral_axis_inter_simplexRoof (m := m) hm hψm hellm hψ0 hell0 hFint
  have hG := setIntegral_axis_inter_simplexRoof (m := m) hm hψm hellm hψ0 hell0 hGint
  have hv : 0 < (volume (coordinateSimplex m)).toReal :=
    volume_coordinateSimplex_toReal_pos (m := m)
  constructor
  · rw [hFzero] at hF
    exact (mul_eq_zero.mp hF.symm).resolve_left hv.ne'
  · rw [hG] at hGpos
    rcases mul_pos_iff.mp hGpos with h | h
    · exact h.2
    · exact (not_lt_of_ge hv.le h.1).elim

/-! ## Height/tail-sum halfspaces -/

/-- Linear functional spanning the two-dimensional BF roof pencil. -/
def roofLinearMap (a b : ℝ) : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun x := a * x 0 + b * ∑ i, Fin.tail x i
  map_add' x y := by
    have htail : Fin.tail (x + y) = Fin.tail x + Fin.tail y := by
      ext i
      simp [Fin.tail]
    rw [htail]
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    have htail : Fin.tail (c • x) = c • Fin.tail x := by
      ext i
      simp [Fin.tail]
    rw [htail]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

/-- Continuous version used by `halfSpace` and the pencil selection API. -/
noncomputable def roofCLM (a b : ℝ) : (Fin (m + 1) → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (roofLinearMap (m := m) a b)

@[simp] theorem roofCLM_apply (a b : ℝ) (x : Fin (m + 1) → ℝ) :
    roofCLM (m := m) a b x = a * x 0 + b * ∑ i, Fin.tail x i := rfl

/-- The open region above an affine roof. -/
def simplexAboveRoof (ell : ℝ → ℝ) : Set (Fin (m + 1) → ℝ) :=
  {x | ell (x 0) < ∑ i, Fin.tail x i}

/-- The open region below an affine roof. -/
def simplexBelowRoofOpen (ell : ℝ → ℝ) : Set (Fin (m + 1) → ℝ) :=
  {x | ∑ i, Fin.tail x i < ell (x 0)}

/-- Positive transverse orientation: the closed side is exactly a simplex roof. -/
theorem halfSpace_roofCLM_true_of_pos {a b c : ℝ} (hb : 0 < b) :
    halfSpace (roofCLM (m := m) a b) c true =
      simplexRoof (fun t => (c - a * t) / b) := by
  ext x
  simp only [halfSpace_true, mem_setOf_eq, roofCLM_apply, mem_simplexRoof]
  rw [le_div_iff₀ hb]
  constructor <;> intro h <;> linarith

/-- Positive transverse orientation: the other selected side is an upper shell. -/
theorem halfSpace_roofCLM_false_of_pos {a b c : ℝ} (hb : 0 < b) :
    halfSpace (roofCLM (m := m) a b) c false =
      simplexAboveRoof (fun t => (c - a * t) / b) := by
  ext x
  simp only [halfSpace_false, mem_setOf_eq, roofCLM_apply, simplexAboveRoof]
  rw [div_lt_iff₀ hb]
  constructor <;> intro h <;> linarith

/-- Negative transverse orientation reverses the closed side into an upper shell. -/
theorem halfSpace_roofCLM_true_of_neg {a b c : ℝ} (hb : b < 0) :
    halfSpace (roofCLM (m := m) a b) c true =
      {x | (c - a * x 0) / b ≤ ∑ i, Fin.tail x i} := by
  ext x
  simp only [halfSpace_true, mem_setOf_eq, roofCLM_apply]
  rw [div_le_iff_of_neg hb]
  constructor <;> intro h <;> linarith

/-- Negative transverse orientation: the open selected side is below the affine roof. -/
theorem halfSpace_roofCLM_false_of_neg {a b c : ℝ} (hb : b < 0) :
    halfSpace (roofCLM (m := m) a b) c false =
      simplexBelowRoofOpen (fun t => (c - a * t) / b) := by
  ext x
  simp only [halfSpace_false, mem_setOf_eq, roofCLM_apply, simplexBelowRoofOpen]
  rw [lt_div_iff_of_neg hb]
  constructor <;> intro h <;> linarith

theorem roofCLM_neg (a b : ℝ) :
    roofCLM (m := m) (-a) (-b) = -roofCLM (m := m) a b := by
  ext x
  simp only [roofCLM_apply, neg_apply]
  ring

/-! ## The two lower-roof orientations consumed by BF -/

/-- A selected closed side with positive transverse coefficient gives a feasible cut profile. -/
theorem roofCLM_true_constraints_of_ambient
    {ψ F G : ℝ → ℝ} {a b c : ℝ} (hm : m ≠ 0) (hb : 0 < b)
    (hψm : Measurable ψ)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (hell0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (c - a * t) / b)
    (hFint : IntegrableOn (fun x : Fin (m + 1) → ℝ => F (x 0))
      (profileBody (coordinateSimplex m) ψ))
    (hGint : IntegrableOn (fun x : Fin (m + 1) → ℝ => G (x 0))
      (profileBody (coordinateSimplex m) ψ))
    (hFzero : (∫ x in profileBody (coordinateSimplex m) ψ ∩
      halfSpace (roofCLM (m := m) a b) c true, F (x 0)) = 0)
    (hGpos : 0 < ∫ x in profileBody (coordinateSimplex m) ψ ∩
      halfSpace (roofCLM (m := m) a b) c true, G (x 0)) :
    (∫ t : ℝ, roofCutProfile ψ (fun t => (c - a * t) / b) t ^ m * F t) = 0 ∧
      0 < ∫ t : ℝ, roofCutProfile ψ (fun t => (c - a * t) / b) t ^ m * G t := by
  rw [halfSpace_roofCLM_true_of_pos hb] at hFzero hGpos
  exact roofCutProfile_constraints_of_ambient (m := m) hm hψm
    (by fun_prop) hψ0 hell0
    (hFint.mono_set inter_subset_left) (hGint.mono_set inter_subset_left) hFzero hGpos

/-- A selected open side with negative transverse coefficient is, up to its null boundary, the
closed lower roof for the reversed functional, and hence gives the same feasible cut profile. -/
theorem roofCLM_false_constraints_of_ambient
    {ψ F G : ℝ → ℝ} {a b c : ℝ} (hm : m ≠ 0) (hb : b < 0)
    (hL : roofCLM (m := m) a b ≠ 0)
    (hψm : Measurable ψ)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (hell0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ((-c) - (-a) * t) / (-b))
    (hFint : IntegrableOn (fun x : Fin (m + 1) → ℝ => F (x 0))
      (profileBody (coordinateSimplex m) ψ))
    (hGint : IntegrableOn (fun x : Fin (m + 1) → ℝ => G (x 0))
      (profileBody (coordinateSimplex m) ψ))
    (hFzero : (∫ x in profileBody (coordinateSimplex m) ψ ∩
      halfSpace (roofCLM (m := m) a b) c false, F (x 0)) = 0)
    (hGpos : 0 < ∫ x in profileBody (coordinateSimplex m) ψ ∩
      halfSpace (roofCLM (m := m) a b) c false, G (x 0)) :
    (∫ t : ℝ, roofCutProfile ψ (fun t => ((-c) - (-a) * t) / (-b)) t ^ m * F t) = 0 ∧
      0 < ∫ t : ℝ,
        roofCutProfile ψ (fun t => ((-c) - (-a) * t) / (-b)) t ^ m * G t := by
  have hFneg := setIntegral_halfSpace_neg (μ := volume) hL c true
    (C := profileBody (coordinateSimplex m) ψ) (f := fun x => F (x 0))
  have hGneg := setIntegral_halfSpace_neg (μ := volume) hL c true
    (C := profileBody (coordinateSimplex m) ψ) (f := fun x => G (x 0))
  rw [← roofCLM_neg (m := m) a b] at hFneg hGneg
  have hFzero' : (∫ x in profileBody (coordinateSimplex m) ψ ∩
      halfSpace (roofCLM (m := m) (-a) (-b)) (-c) true, F (x 0)) = 0 := by
    rw [hFneg]
    exact hFzero
  have hGpos' : 0 < ∫ x in profileBody (coordinateSimplex m) ψ ∩
      halfSpace (roofCLM (m := m) (-a) (-b)) (-c) true, G (x 0) := by
    rw [hGneg]
    exact hGpos
  exact roofCLM_true_constraints_of_ambient (m := m) hm (by linarith) hψm hψ0 hell0
    hFint hGint hFzero' hGpos'

end Arlib

#print axioms Arlib.measurableSet_profileBody_coordinateSimplex
#print axioms Arlib.setIntegral_axis_profileBody_coordinateSimplex_of_support
#print axioms Arlib.volume_coordinateSimplex_toReal_pos
#print axioms Arlib.setIntegral_axis_inter_simplexRoof
#print axioms Arlib.roofCutProfile_constraints_of_ambient
#print axioms Arlib.halfSpace_roofCLM_true_of_pos
#print axioms Arlib.halfSpace_roofCLM_false_of_pos
#print axioms Arlib.halfSpace_roofCLM_true_of_neg
#print axioms Arlib.halfSpace_roofCLM_false_of_neg
#print axioms Arlib.roofCLM_true_constraints_of_ambient
#print axioms Arlib.roofCLM_false_constraints_of_ambient
