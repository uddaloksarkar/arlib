/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFUpperShellSelector
import Arlib.Convexity.BFAffineCoreAttainment

/-!
# Final BF orientation integration

This file closes the moment/Fubini part of the vertical selector orientation.  It also records
the exact point at which the remaining lower-roof branch needs lexicographic maximality across
the entire feasible candidate class, rather than maximality of a core inside one fixed profile.
-/

open Set MeasureTheory

namespace Arlib

variable {m : ℕ}

/-- Restrict a simplex-profile body to a closed height interval. -/
def profileHeightInterval (m : ℕ) (ψ : ℝ → ℝ) (l u : ℝ) :
    Set (Fin (m + 1) → ℝ) :=
  profileBody (coordinateSimplex m) ψ ∩ {x | x 0 ∈ Icc l u}

theorem measurableSet_profileHeightInterval {ψ : ℝ → ℝ}
    (hψmeas : Measurable ψ) (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (l u : ℝ) : MeasurableSet (profileHeightInterval m ψ l u) := by
  exact (measurableSet_profileBody_coordinateSimplex hψmeas hψ0).inter
    (measurableSet_Icc.preimage (measurable_pi_apply 0))

/-- Exact Fubini identity on a closed height interval. -/
theorem setIntegral_axis_profileHeightInterval (hm : m ≠ 0)
    {ψ F : ℝ → ℝ} (hψmeas : Measurable ψ)
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    {l u : ℝ} (hl : 0 ≤ l) (hu : u ≤ 1)
    (hint : IntegrableOn (fun x : Fin (m + 1) → ℝ => F (x 0))
      (profileHeightInterval m ψ l u)) :
    (∫ x in profileHeightInterval m ψ l u, F (x 0)) =
      (volume (coordinateSimplex m)).toReal * ∫ t in Icc l u, ψ t ^ m * F t := by
  have hD := measurableSet_profileHeightInterval (m := m) hψmeas hψ0 l u
  rw [setIntegral_eq_integral_slice hD hint]
  have hpoint : (fun t : ℝ =>
      ∫ y in slice (profileHeightInterval m ψ l u) t,
        F ((Fin.cons t y : Fin (m + 1) → ℝ) 0)) =
      fun t => (Icc l u).indicator
        (fun s => (volume (coordinateSimplex m)).toReal * (ψ s ^ m * F s)) t := by
    funext t
    by_cases ht : t ∈ Icc l u
    · have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hl.trans ht.1, ht.2.trans hu⟩
      simp only [profileHeightInterval, slice, mem_inter_iff, mem_setOf_eq,
        Fin.cons_zero, indicator_of_mem ht]
      have hs : {y : Fin m → ℝ |
          Fin.cons t y ∈ profileBody (coordinateSimplex m) ψ ∧ t ∈ Icc l u} =
          slice (profileBody (coordinateSimplex m) ψ) t := by
        ext y
        simp [slice, ht]
      rw [hs, setIntegral_const, smul_eq_mul, Measure.real,
        volume_slice_profileBody ht01 (hψ0 t ht01), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg (hψ0 t ht01) m)]
      ring
    · have hs : slice (profileHeightInterval m ψ l u) t = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro y hy
        exact ht hy.2
      rw [hs, setIntegral_empty, indicator_of_notMem ht]
  rw [hpoint, integral_indicator measurableSet_Icc, integral_const_mul]

/-- **Vertical selector orientation eliminated.**  A proper height interval carrying the
selector's zero/positive moments contradicts support minimality.  Positive selected moment
automatically gives positive interval mass. -/
theorem BFMovingCandidate.not_profileHeightInterval_of_eq_sInf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKconv : Convex ℝ K) {g h : E → ℝ}
    (c : BFMovingCandidate K g h m)
    (hmin : c.supportLength = sInf (Set.range
      (fun q : BFMovingCandidate K g h m => q.supportLength)))
    (hcne : c.left ≠ c.right) (hm : m ≠ 0)
    (hclosed : ConcaveOn ℝ (Icc (0 : ℝ) 1) c.profile)
    {l u : ℝ} (hl : 0 ≤ l) (hlu : l < u) (hu : u ≤ 1) (hwidth : u - l < 1)
    (hgint : IntegrableOn (fun x : Fin (m + 1) → ℝ =>
      g (bfSegmentPoint c.left c.right (x 0)))
      (profileHeightInterval m c.profile l u))
    (hhint : IntegrableOn (fun x : Fin (m + 1) → ℝ =>
      h (bfSegmentPoint c.left c.right (x 0)))
      (profileHeightInterval m c.profile l u))
    (hgzero : (∫ x in profileHeightInterval m c.profile l u,
      g (bfSegmentPoint c.left c.right (x 0))) = 0)
    (hhpos : 0 < ∫ x in profileHeightInterval m c.profile l u,
      h (bfSegmentPoint c.left c.right (x 0))) : False := by
  have hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ c.profile t := fun t _ => c.profile_nonneg t
  have hgEq := setIntegral_axis_profileHeightInterval
    (F := fun t => g (bfSegmentPoint c.left c.right t)) hm c.profile_measurable hψ0 hl hu hgint
  have hhEq := setIntegral_axis_profileHeightInterval
    (F := fun t => h (bfSegmentPoint c.left c.right t)) hm c.profile_measurable hψ0 hl hu hhint
  have hv : 0 < (volume (coordinateSimplex m)).toReal :=
    volume_coordinateSimplex_toReal_pos (m := m)
  have hg1d : (∫ t in Icc l u, c.profile t ^ m *
      g (bfSegmentPoint c.left c.right t)) = 0 := by
    rw [hgzero] at hgEq
    exact (mul_eq_zero.mp hgEq.symm).resolve_left hv.ne'
  have hh1d : 0 < ∫ t in Icc l u, c.profile t ^ m *
      h (bfSegmentPoint c.left c.right t) := by
    rw [hhEq] at hhpos
    exact (mul_pos_iff.mp hhpos).resolve_right (by
      intro hneg
      exact (not_lt_of_ge hv.le hneg.1).elim) |>.2
  have hDsub : profileHeightInterval m c.profile l u ⊆
      profileBody (coordinateSimplex m) c.profile := inter_subset_left
  have hDfin : volume (profileHeightInterval m c.profile l u) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (volume_profileBody_coordinateSimplex_ne_top_of_bound hψ0
        (fun t _ => c.profile_bound t))
      (measure_mono hDsub)
  have hDpos : 0 < volume (profileHeightInterval m c.profile l u) := by
    rw [pos_iff_ne_zero]
    intro hDzero
    have : (∫ x in profileHeightInterval m c.profile l u,
        h (bfSegmentPoint c.left c.right (x 0))) = 0 :=
      setIntegral_measure_zero _ hDzero
    linarith
  have honeint : IntegrableOn (fun _ : Fin (m + 1) → ℝ => (1 : ℝ))
      (profileHeightInterval m c.profile l u) := integrableOn_const hDfin
  have hmassEq := setIntegral_axis_profileHeightInterval
    (F := fun _ => (1 : ℝ)) hm c.profile_measurable hψ0 hl hu honeint
  have hDrealpos : 0 < (volume (profileHeightInterval m c.profile l u)).toReal :=
    ENNReal.toReal_pos hDpos.ne' hDfin
  simp only [setIntegral_const, smul_eq_mul, Measure.real, mul_one] at hmassEq
  have hmass : 0 < ∫ t in Icc l u, c.profile t ^ m := by
    rw [hmassEq] at hDrealpos
    rcases (mul_pos_iff.mp hDrealpos) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hv.le hneg.1).elim
  exact c.not_verticalIntervalMoments_of_eq_sInf hKconv hm hmin hclosed hcne
    hl hlu hu hwidth hmass hg1d hh1d.le

end Arlib

#print axioms Arlib.setIntegral_axis_profileHeightInterval
#print axioms Arlib.BFMovingCandidate.not_profileHeightInterval_of_eq_sInf
