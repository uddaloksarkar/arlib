/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFCaseOneArithmetic

/-!
# Endpoint-jump obstruction in the BF variational class

The current compact BF candidate class permits downward endpoint jumps.  This explicit profile
shows why an arbitrary-height upper shell cannot be eliminated merely from support minimality:
a strictly positive constant roof excludes both endpoint points, but the strict-above set still
has infimum `0` and supremum `1`.
-/

open Set

namespace Arlib

noncomputable def bfEndpointJumpProfile (t : ℝ) : ℝ :=
  if t ∈ Ioo (0 : ℝ) 1 then 1 else 0

theorem concaveOn_bfEndpointJumpProfile :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) bfEndpointJumpProfile := by
  exact concaveOn_Icc_extendZero
    (concaveOn_const (1 : ℝ) (convex_Ioo (0 : ℝ) 1)) (fun _ _ => by norm_num)

theorem bfEndpointJumpProfile_endpoints :
    bfEndpointJumpProfile 0 = 0 ∧ bfEndpointJumpProfile 1 = 0 := by
  simp [bfEndpointJumpProfile]

theorem bfEndpointJumpProfile_above_half :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ (1 : ℝ) / 2 < bfEndpointJumpProfile t} =
      Ioo 0 1 := by
  ext t
  change ((0 ≤ t ∧ t ≤ 1) ∧ (1 : ℝ) / 2 <
    (if 0 < t ∧ t < 1 then 1 else 0)) ↔ (0 < t ∧ t < 1)
  by_cases ht : 0 < t ∧ t < 1
  · simp [ht, ht.1.le, ht.2.le]
    norm_num
  · simp [ht]

theorem bfEndpointJumpProfile_above_half_full_extremal_width :
    sSup {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ (1 : ℝ) / 2 < bfEndpointJumpProfile t} -
      sInf {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ (1 : ℝ) / 2 < bfEndpointJumpProfile t} = 1 := by
  rw [bfEndpointJumpProfile_above_half, csSup_Ioo (by norm_num : (0 : ℝ) < 1),
    csInf_Ioo (by norm_num : (0 : ℝ) < 1)]
  norm_num

end Arlib

#print axioms Arlib.concaveOn_bfEndpointJumpProfile
#print axioms Arlib.bfEndpointJumpProfile_above_half_full_extremal_width
