/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFMovingCandidate

/-!
# Attainment of a maximal affine core

The variational part of the Borell--Fradelizi argument also maximizes an interval on which the
selected profile is affine.  Parametrizing an interval by the fixed compact parameter set
`[0,1]` makes this property closed as both endpoints move.  Consequently every continuous
profile has a literal maximal affine core.

The endpoint-continuity assumption is intentional.  A bounded profile which is merely concave
on `(0,1)` may jump at `0` or `1`; the normalized candidate compactness theorem only provides
that weaker conclusion.  Source applications either regularize the profile or use the maximal
core inside a fixed compact subinterval of `(0,1)`.
-/

open Set
open scoped Topology

namespace Arlib

/-- `ψ` is affine along the segment from `a` to `b`, expressed on a fixed parameter interval. -/
def ParametricProfileAffineOn (ψ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1,
    ψ ((1 - s) * a + s * b) = (1 - s) * ψ a + s * ψ b

/-- Admissible affine cores of a profile in the unit interval. -/
def affineCorePairs (ψ : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2 ∧
    ParametricProfileAffineOn ψ p.1 p.2}

/-- The parametric formulation implies the coefficient formulation already used by the BF cut
files. -/
theorem profileAffineOn_of_parametric {ψ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ParametricProfileAffineOn ψ a b) : ProfileAffineOn ψ a b := by
  rcases hab.eq_or_lt with rfl | hab
  · exact ⟨0, ψ a, fun t ht => by
      have : t = a := le_antisymm ht.2 ht.1
      subst t
      ring⟩
  let u := (ψ b - ψ a) / (b - a)
  let v := ψ a - u * a
  refine ⟨u, v, fun t ht => ?_⟩
  let s := (t - a) / (b - a)
  have hba : 0 < b - a := sub_pos.mpr hab
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hba.le
    · rw [div_le_one hba]
      linarith [ht.2]
  have htparam : (1 - s) * a + s * b = t := by
    dsimp [s]
    field_simp
    ring
  have heq := h s hs
  rw [htparam] at heq
  dsimp [u, v]
  dsimp [s] at heq
  field_simp at heq ⊢
  linear_combination heq

/-- The affine-core relation is closed when the profile is continuous. -/
theorem isClosed_affineCorePairs {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    IsClosed (affineCorePairs ψ) := by
  have hparam : IsClosed {p : ℝ × ℝ | ParametricProfileAffineOn ψ p.1 p.2} := by
    have heq : {p : ℝ × ℝ | ParametricProfileAffineOn ψ p.1 p.2} =
        ⋂ s : ℝ, ⋂ (_hs : s ∈ Icc (0 : ℝ) 1),
          {p : ℝ × ℝ |
            ψ ((1 - s) * p.1 + s * p.2) = (1 - s) * ψ p.1 + s * ψ p.2} := by
      ext p
      simp only [mem_setOf_eq, mem_iInter, ParametricProfileAffineOn]
    rw [heq]
    refine isClosed_iInter fun s => isClosed_iInter fun _hs => isClosed_eq ?_ ?_
    · fun_prop
    · fun_prop
  have hbox : IsClosed (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    isClosed_Icc.prod isClosed_Icc
  have horder : IsClosed {p : ℝ × ℝ | p.1 ≤ p.2} := isClosed_le continuous_fst continuous_snd
  have heq : affineCorePairs ψ =
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {p : ℝ × ℝ | p.1 ≤ p.2} ∩
        {p : ℝ × ℝ | ParametricProfileAffineOn ψ p.1 p.2} := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨⟨hp.1, hp.2.1⟩, hp.2.2.1⟩, hp.2.2.2⟩
    · rintro ⟨⟨⟨hp0, hp1⟩, hpord⟩, hpaff⟩
      exact ⟨hp0, hp1, hpord, hpaff⟩
  rw [heq]
  exact (hbox.inter horder).inter hparam

/-- Affine cores form a nonempty compact set of endpoint pairs. -/
theorem isCompact_affineCorePairs {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    IsCompact (affineCorePairs ψ) := by
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    (isClosed_affineCorePairs hψ) (fun _ hp => ⟨hp.1, hp.2.1⟩)

theorem affineCorePairs_nonempty (ψ : ℝ → ℝ) : (affineCorePairs ψ).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · rfl
  · intro s hs
    ring_nf

/-- **A maximal affine core is attained.**  The maximality is stated directly against every
other affine core, avoiding an opaque `sSup` in downstream cut contradictions. -/
theorem exists_maximalAffineCore {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    ∃ a b : ℝ, (a, b) ∈ affineCorePairs ψ ∧
      ∀ x y : ℝ, (x, y) ∈ affineCorePairs ψ → y - x ≤ b - a := by
  obtain ⟨p, hp, hpmax⟩ :=
    (isCompact_affineCorePairs hψ).exists_isMaxOn (affineCorePairs_nonempty ψ)
      (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => p.2 - p.1) (affineCorePairs ψ))
  exact ⟨p.1, p.2, hp, fun x y hxy => hpmax hxy⟩

/-- Coefficient-form corollary matching `BFExtremalProfile.ProfileAffineOn`. -/
theorem exists_maximalProfileAffineOn {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    ∃ a b : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a ≤ b ∧
      ProfileAffineOn ψ a b ∧
      ∀ x y : ℝ, (x, y) ∈ affineCorePairs ψ → y - x ≤ b - a := by
  obtain ⟨a, b, hab, hmax⟩ := exists_maximalAffineCore hψ
  exact ⟨a, b, hab.1, hab.2.1, hab.2.2.1,
    profileAffineOn_of_parametric hab.2.2.1 hab.2.2.2, hmax⟩

/-- The final variational contradiction, separated from its geometric input: if every proper
maximal core admits a feasible strictly longer core, the maximal core is the whole interval. -/
theorem maximalAffineCore_eq_unit_of_strictImprovement {ψ : ℝ → ℝ} {a b : ℝ}
    (hab : (a, b) ∈ affineCorePairs ψ)
    (hmax : ∀ x y : ℝ, (x, y) ∈ affineCorePairs ψ → y - x ≤ b - a)
    (himprove : b - a < 1 →
      ∃ x y : ℝ, (x, y) ∈ affineCorePairs ψ ∧ b - a < y - x) :
    a = 0 ∧ b = 1 := by
  have hlen : b - a ≤ 1 := by linarith [hab.1.1, hab.2.1.2]
  have hlenEq : b - a = 1 := by
    apply le_antisymm hlen
    by_contra hnot
    obtain ⟨x, y, hxy, hstrict⟩ := himprove (lt_of_not_ge hnot)
    exact (not_lt_of_ge (hmax x y hxy)) hstrict
  constructor <;> linarith [hab.1.1, hab.1.2, hab.2.1.1, hab.2.1.2]

/-- Hence the profile is affine on `[0,1]`.  This is the exact consumer of BF's three
constraint-preserving cut cases. -/
theorem profileAffineOn_unit_of_strictImprovement {ψ : ℝ → ℝ} {a b : ℝ}
    (hab : (a, b) ∈ affineCorePairs ψ)
    (hmax : ∀ x y : ℝ, (x, y) ∈ affineCorePairs ψ → y - x ≤ b - a)
    (himprove : b - a < 1 →
      ∃ x y : ℝ, (x, y) ∈ affineCorePairs ψ ∧ b - a < y - x) :
    ProfileAffineOn ψ 0 1 := by
  obtain ⟨rfl, rfl⟩ := maximalAffineCore_eq_unit_of_strictImprovement hab hmax himprove
  exact profileAffineOn_of_parametric (by norm_num) hab.2.2.2

end Arlib

#print axioms Arlib.profileAffineOn_of_parametric
#print axioms Arlib.isClosed_affineCorePairs
#print axioms Arlib.exists_maximalAffineCore
#print axioms Arlib.exists_maximalProfileAffineOn
#print axioms Arlib.maximalAffineCore_eq_unit_of_strictImprovement
#print axioms Arlib.profileAffineOn_unit_of_strictImprovement
