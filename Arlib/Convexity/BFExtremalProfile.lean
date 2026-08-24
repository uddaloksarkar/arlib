/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.AdaptedProfileChain

/-!
# The variational profile in the Borell--Fradelizi localization argument

This file records the exact feasible class used after the compact-chain limit and formalizes the
pointwise heart of the first endpoint case in the source's concave-to-affine argument.

When a feasible concave profile vanishes at both endpoints but is positive in the interior, cut
it by a sufficiently low horizontal affine function.  The resulting profile is still concave,
has the same open support, and is affine on any prescribed compact subinterval of `(0,1)`.
This is precisely the profile calculation behind case 1 of BF Corollary 2.2.  Selecting the cut
which also preserves the two integral constraints is a separate geometric step.
-/

open Set MeasureTheory intervalIntegral

namespace Arlib

/-- The one-dimensional feasible profiles in the equality form of BF localization. -/
def BFProfileFeasible (k : ℕ) (g h ψ : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ ∧
  (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) ∧
  IntervalIntegrable (fun t => ψ t ^ k * g t) volume 0 1 ∧
  IntervalIntegrable (fun t => ψ t ^ k * h t) volume 0 1 ∧
  (∫ t in (0 : ℝ)..1, ψ t ^ k * g t) = 0 ∧
  0 ≤ ∫ t in (0 : ℝ)..1, ψ t ^ k * h t

/-- A profile is affine on a closed interval if it agrees there with `u*t+v`. -/
def ProfileAffineOn (ψ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ u v : ℝ, ∀ t ∈ Icc a b, ψ t = u * t + v

/-- Horizontal clipping of a profile, the slice profile produced in BF's first cutting case. -/
def clippedProfile (ψ : ℝ → ℝ) (τ : ℝ) : ℝ → ℝ := fun t => min (ψ t) τ

/-- Concavity is preserved by clipping from above by a constant affine profile. -/
theorem concaveOn_clippedProfile {ψ : ℝ → ℝ} {τ : ℝ}
    (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (clippedProfile ψ τ) := by
  change ConcaveOn ℝ (Icc (0 : ℝ) 1) (ψ ⊓ fun _ => τ)
  exact hψ.inf (concaveOn_const τ (convex_Icc (0 : ℝ) 1))

/-- The first BF endpoint case, as a constructive profile improvement.

For every core `[δ,1-δ]` strictly inside `(0,1)`, the explicit height
`τ = min(ψ δ, ψ(1-δ))/2` is positive.  Clipping at this height keeps exactly the same endpoint
zeros and open support but makes the entire core affine (indeed constant). -/
theorem exists_clippedProfile_affine_core {ψ : ℝ → ℝ}
    (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0)
    (hψpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < ψ t)
    {δ : ℝ} (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ τ : ℝ, 0 < τ ∧
      ConcaveOn ℝ (Icc (0 : ℝ) 1) (clippedProfile ψ τ) ∧
      clippedProfile ψ τ 0 = 0 ∧ clippedProfile ψ τ 1 = 0 ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, 0 < clippedProfile ψ τ t) ∧
      ProfileAffineOn (clippedProfile ψ τ) δ (1 - δ) := by
  have hδ1 : δ < 1 := lt_trans hδhalf (by norm_num)
  have h1δ0 : 0 < 1 - δ := sub_pos.mpr hδ1
  have hδlt1δ : δ < 1 - δ := by linarith
  have hpδ : 0 < ψ δ := hψpos δ ⟨hδ0, hδ1⟩
  have hp1δ : 0 < ψ (1 - δ) := hψpos (1 - δ) ⟨h1δ0, by linarith⟩
  let τ : ℝ := min (ψ δ) (ψ (1 - δ)) / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτmin : τ ≤ min (ψ δ) (ψ (1 - δ)) := by
    dsimp [τ]
    have hm : 0 ≤ min (ψ δ) (ψ (1 - δ)) := (lt_min hpδ hp1δ).le
    linarith
  have hcore : ∀ t ∈ Icc δ (1 - δ), τ ≤ ψ t := by
    intro t ht
    exact hτmin.trans (hψ.min_le_of_mem_Icc
      ⟨hδ0.le, hδ1.le⟩ ⟨h1δ0.le, by linarith⟩ ht)
  refine ⟨τ, hτ, concaveOn_clippedProfile hψ, ?_, ?_, ?_, ?_⟩
  · simp [clippedProfile, hψ0, hτ.le]
  · simp [clippedProfile, hψ1, hτ.le]
  · intro t ht
    exact lt_min (hψpos t ht) hτ
  · refine ⟨0, τ, fun t ht => ?_⟩
    rw [clippedProfile, min_eq_right (hcore t ht)]
    ring

/-- The affine interval constructed in the first BF case can be made strictly longer than any
fixed candidate interval of length less than one. -/
theorem exists_clippedProfile_longer_affine_core {ψ : ℝ → ℝ}
    (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0)
    (hψpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < ψ t)
    {a b : ℝ} (hab0 : 0 ≤ b - a) (hab : b - a < 1) :
    ∃ δ τ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ 0 < τ ∧
      b - a < (1 - δ) - δ ∧
      ProfileAffineOn (clippedProfile ψ τ) δ (1 - δ) := by
  let δ : ℝ := (1 - (b - a)) / 4
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  have hδhalf : δ < 1 / 2 := by dsimp [δ]; linarith
  obtain ⟨τ, hτ, -, -, -, -, haff⟩ :=
    exists_clippedProfile_affine_core hψ hψ0 hψ1 hψpos hδ0 hδhalf
  refine ⟨δ, τ, hδ0, hδhalf, hτ, ?_, haff⟩
  dsimp [δ]
  linarith

end Arlib

#print axioms Arlib.concaveOn_clippedProfile
#print axioms Arlib.exists_clippedProfile_affine_core
#print axioms Arlib.exists_clippedProfile_longer_affine_core
