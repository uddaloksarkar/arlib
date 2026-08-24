/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFEndpointJumpObstruction
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The missing endpoint-tightness assumption

Endpoint continuity of each feasible profile does not survive BF compactness.  The necessary
extra property is *uniform* one-sided equicontinuity.  This file isolates that property and
shows it already fails for the exact slice profiles of the compact convex simplex bodies with
root profile `min 1 ((k+1)t)`.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace Arlib

variable {m : ℕ}

/-- Uniform one-sided equicontinuity at the left endpoint. -/
def UniformLeftEndpointTight (u : ℕ → ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ delta > 0, ∀ k t, t ∈ Icc (0 : ℝ) delta →
    |u k t - u k 0| < eps

/-- The collapsing-boundary-layer profiles.  They are continuous and concave on `[0,1]`. -/
def bfRampProfile (k : ℕ) (t : ℝ) : ℝ := min 1 (((k + 1 : ℕ) : ℝ) * t)

theorem continuous_bfRampProfile (k : ℕ) : Continuous (bfRampProfile k) := by
  unfold bfRampProfile
  fun_prop

theorem concaveOn_bfRampProfile (k : ℕ) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (bfRampProfile k) := by
  unfold bfRampProfile
  change ConcaveOn ℝ (Icc (0 : ℝ) 1)
    ((fun _ : ℝ => (1 : ℝ)) ⊓ fun t => (((k + 1 : ℕ) : ℝ) * t))
  exact (concaveOn_const 1 (convex_Icc (0 : ℝ) 1)).inf
    (by simpa [mul_comm] using
      (concaveOn_affine_real (convex_Icc (0 : ℝ) 1) 0 ((k + 1 : ℕ) : ℝ)))

theorem bfRampProfile_nonneg (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ bfRampProfile k t := by
  unfold bfRampProfile
  exact le_min (by norm_num) (mul_nonneg (by positivity) ht.1)

@[simp] theorem bfRampProfile_zero (k : ℕ) : bfRampProfile k 0 = 0 := by
  simp [bfRampProfile]

@[simp] theorem bfRampProfile_transition (k : ℕ) :
    bfRampProfile k (((k + 1 : ℕ) : ℝ)⁻¹) = 1 := by
  unfold bfRampProfile
  have hk : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [mul_inv_cancel₀ hk, min_self]

theorem tendsto_bfRamp_transition_zero :
    Tendsto (fun k : ℕ => ((((k + 1 : ℕ) : ℝ))⁻¹)) atTop (nhds 0) := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hadd : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hnat
  have hinv := tendsto_inv_atTop_zero.comp hadd
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hinv

/-- **Endpoint-continuous physical profiles are not uniformly endpoint-tight.** -/
theorem not_uniformLeftEndpointTight_bfRampProfile :
    ¬ UniformLeftEndpointTight bfRampProfile := by
  intro htight
  obtain ⟨delta, hdelta, hbound⟩ := htight (1 / 2) (by norm_num)
  have hevent : ∀ᶠ k in atTop, (((k + 1 : ℕ) : ℝ)⁻¹) < delta :=
    (tendsto_order.mp tendsto_bfRamp_transition_zero).2 delta hdelta
  obtain ⟨k, hk⟩ := hevent.exists
  have hkpos : 0 ≤ ((((k + 1 : ℕ) : ℝ))⁻¹) := by positivity
  have h := hbound k (((k + 1 : ℕ) : ℝ)⁻¹) ⟨hkpos, hk.le⟩
  rw [bfRampProfile_transition, bfRampProfile_zero] at h
  norm_num at h

/-- Each ramp is realized exactly, up to the fixed simplex-volume factor, as the sharp slice
profile of a convex profile body. -/
theorem ramp_profileBody_slice_profile (hm : m ≠ 0) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (volume (slice (profileBody (coordinateSimplex m) (bfRampProfile k)) t)).toReal ^
        (1 / (m : ℝ)) =
      bfRampProfile k t * (volume (coordinateSimplex m)).toReal ^ (1 / (m : ℝ)) := by
  exact profile_profileBody hm ht (bfRampProfile_nonneg k ht)

theorem convex_ramp_profileBody (k : ℕ) :
    Convex ℝ (profileBody (coordinateSimplex m) (bfRampProfile k)) := by
  exact convex_profileBody convex_coordinateSimplex zero_mem_coordinateSimplex
    (concaveOn_bfRampProfile k) (fun t ht => bfRampProfile_nonneg k ht)

/-- The ramp profile bodies are compact, not merely convex.  Thus the boundary-layer
counterexample occurs inside the literal compact-convex-body class used by BF. -/
theorem isCompact_ramp_profileBody (k : ℕ) :
    IsCompact (profileBody (coordinateSimplex m) (bfRampProfile k)) := by
  let box : Set (Fin (m + 1) → ℝ) := univ.pi (fun _ => Icc (0 : ℝ) 1)
  have hclosed : IsClosed (profileBody (coordinateSimplex m) (bfRampProfile k)) := by
    have htail_cont (i : Fin m) :
        Continuous (fun x : Fin (m + 1) → ℝ => Fin.tail x i) := by
      change Continuous (fun x : Fin (m + 1) → ℝ => x i.succ)
      exact continuous_apply _
    have hsum_cont :
        Continuous (fun x : Fin (m + 1) → ℝ => ∑ i, Fin.tail x i) :=
      continuous_finsetSum _ fun i _ => htail_cont i
    rw [show profileBody (coordinateSimplex m) (bfRampProfile k) =
        {x | x 0 ∈ Icc (0 : ℝ) 1 ∧ (∀ i, 0 ≤ Fin.tail x i) ∧
          ∑ i, Fin.tail x i ≤ bfRampProfile k (x 0)} by
      ext x
      exact mem_profileBody_coordinateSimplex_iff
        (fun t ht => bfRampProfile_nonneg k ht)]
    have haxis : IsClosed {x : Fin (m + 1) → ℝ | x 0 ∈ Icc (0 : ℝ) 1} :=
      isClosed_Icc.preimage (continuous_apply 0)
    have hnonneg : IsClosed {x : Fin (m + 1) → ℝ | ∀ i, 0 ≤ Fin.tail x i} := by
      have h : IsClosed (⋂ i, {x : Fin (m + 1) → ℝ | (0 : ℝ) ≤ Fin.tail x i}) :=
        isClosed_iInter fun i =>
          isClosed_le (continuous_const : Continuous (fun _ : Fin (m + 1) → ℝ => (0 : ℝ)))
            (htail_cont i)
      convert h using 1
      ext x
      simp only [mem_iInter, mem_setOf_eq]
    have hsum : IsClosed {x : Fin (m + 1) → ℝ |
        ∑ i, Fin.tail x i ≤ bfRampProfile k (x 0)} :=
      isClosed_le hsum_cont ((continuous_bfRampProfile k).comp (continuous_apply 0))
    exact haxis.inter (hnonneg.inter hsum)
  have hbox : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset hclosed ?_
  intro x hx
  rw [mem_profileBody_coordinateSimplex_iff
    (fun t ht => bfRampProfile_nonneg k ht)] at hx
  change x ∈ univ.pi (fun _ => Icc (0 : ℝ) 1)
  rw [Set.mem_pi]
  intro i _
  refine Fin.cases hx.1 (fun j => ?_) i
  have hj0 : 0 ≤ Fin.tail x j := hx.2.1 j
  have hjSum : Fin.tail x j ≤ ∑ r, Fin.tail x r :=
    Finset.single_le_sum (fun r _ => hx.2.1 r) (Finset.mem_univ j)
  have hprofile : bfRampProfile k (x 0) ≤ 1 := min_le_left _ _
  constructor
  · simpa [Fin.tail] using hj0
  · simpa [Fin.tail] using hjSum.trans (hx.2.2.trans hprofile)

/-- The physical sharp slice profiles have a fixed positive jump across points tending to the
left endpoint.  Hence compact-convex-body geometry alone cannot supply endpoint tightness. -/
theorem ramp_profileBody_endpoint_gap (hm : m ≠ 0) (k : ℕ) :
    (volume (slice (profileBody (coordinateSimplex m) (bfRampProfile k))
      (((k + 1 : ℕ) : ℝ)⁻¹))).toReal ^ (1 / (m : ℝ)) -
    (volume (slice (profileBody (coordinateSimplex m) (bfRampProfile k)) 0)).toReal ^
      (1 / (m : ℝ)) =
    (volume (coordinateSimplex m)).toReal ^ (1 / (m : ℝ)) := by
  have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have ht : ((((k + 1 : ℕ) : ℝ))⁻¹) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [inv_le_one₀ hkpos]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  rw [ramp_profileBody_slice_profile hm k ht,
    ramp_profileBody_slice_profile hm k (⟨le_rfl, by norm_num⟩ : (0 : ℝ) ∈ Icc 0 1)]
  simp [bfRampProfile, mul_inv_cancel₀ (by positivity : (↑k + 1 : ℝ) ≠ 0)]

end Arlib

#print axioms Arlib.not_uniformLeftEndpointTight_bfRampProfile
#print axioms Arlib.ramp_profileBody_slice_profile
#print axioms Arlib.convex_ramp_profileBody
#print axioms Arlib.isCompact_ramp_profileBody
#print axioms Arlib.ramp_profileBody_endpoint_gap
