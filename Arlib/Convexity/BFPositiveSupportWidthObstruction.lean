/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFEndpointJumpObstruction

/-!
# Positive-slice support does not repair the BF endpoint obstruction

It is natural to replace physical endpoint distance by the extremal width of the heights at
which the profile (equivalently, the model slice volume) is positive.  This file tests that
proposal on the endpoint-jump limit admitted by the BF compactness theorem.  Both orientations
of the constant roof through height `1/2` retain full extremal width, so this support functional
cannot yield the strict variational contradiction.
-/

open Set

namespace Arlib

/-- Extremal width of the positive part of a profile inside its normalized parameter interval. -/
noncomputable def positiveProfileSupportWidth (psi : ℝ → ℝ) : ℝ :=
  sSup {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ 0 < psi t} -
    sInf {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ 0 < psi t}

theorem bfEndpointJumpProfile_positiveSupport :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ 0 < bfEndpointJumpProfile t} = Ioo 0 1 := by
  ext t
  change ((0 ≤ t ∧ t ≤ 1) ∧ 0 <
    (if 0 < t ∧ t < 1 then (1 : ℝ) else 0)) ↔ 0 < t ∧ t < 1
  by_cases ht : 0 < t ∧ t < 1
  · simp [ht, ht.1.le, ht.2.le]
  · simp [ht]

/-- The positive-slice support width of the compactness-limit profile is still the whole
normalized segment. -/
theorem positiveProfileSupportWidth_bfEndpointJumpProfile :
    positiveProfileSupportWidth bfEndpointJumpProfile = 1 := by
  rw [positiveProfileSupportWidth, bfEndpointJumpProfile_positiveSupport,
    csSup_Ioo (by norm_num : (0 : ℝ) < 1), csInf_Ioo (by norm_num : (0 : ℝ) < 1)]
  norm_num

theorem clipped_bfEndpointJumpProfile_positiveSupport :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      0 < clippedProfile bfEndpointJumpProfile (1 / 2) t} = Ioo 0 1 := by
  ext t
  change ((0 ≤ t ∧ t ≤ 1) ∧ 0 <
    min (if 0 < t ∧ t < 1 then (1 : ℝ) else 0) (1 / 2)) ↔ 0 < t ∧ t < 1
  by_cases ht : 0 < t ∧ t < 1
  · simp [ht, ht.1.le, ht.2.le]
  · simp [ht]

/-- The lower-roof (`min psi roof`) selector orientation has no strict decrease either. -/
theorem positiveProfileSupportWidth_clipped_bfEndpointJumpProfile :
    positiveProfileSupportWidth (clippedProfile bfEndpointJumpProfile (1 / 2)) = 1 := by
  rw [positiveProfileSupportWidth, clipped_bfEndpointJumpProfile_positiveSupport,
    csSup_Ioo (by norm_num : (0 : ℝ) < 1), csInf_Ioo (by norm_num : (0 : ℝ) < 1)]
  norm_num

/-- The upper-shell orientation is positive exactly on the same full open interval. -/
theorem upperHalf_bfEndpointJumpProfile_positiveSupport :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      (1 : ℝ) / 2 < bfEndpointJumpProfile t} = Ioo 0 1 :=
  bfEndpointJumpProfile_above_half

/-- Thus both selector alternatives preserve the proposed width at the compactness limit. -/
theorem endpointJump_both_roof_orientations_full_positiveSupportWidth :
    positiveProfileSupportWidth (clippedProfile bfEndpointJumpProfile (1 / 2)) = 1 ∧
      sSup {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
          (1 : ℝ) / 2 < bfEndpointJumpProfile t} -
        sInf {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
          (1 : ℝ) / 2 < bfEndpointJumpProfile t} = 1 :=
  ⟨positiveProfileSupportWidth_clipped_bfEndpointJumpProfile,
    bfEndpointJumpProfile_above_half_full_extremal_width⟩

end Arlib

#print axioms Arlib.positiveProfileSupportWidth_bfEndpointJumpProfile
#print axioms Arlib.positiveProfileSupportWidth_clipped_bfEndpointJumpProfile
#print axioms Arlib.endpointJump_both_roof_orientations_full_positiveSupportWidth
