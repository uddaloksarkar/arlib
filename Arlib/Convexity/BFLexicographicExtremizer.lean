/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFMovingCandidateLimitExposed

/-!
# Lexicographic BF extremizers on a fixed interior slab

This file performs the missing second compactness optimization rigorously on `[c,1-c]`: first
minimize physical support, then maximize the length of an affine profile core whose endpoints
remain in that slab.  Keeping a positive margin is exactly what makes affine-core closure true.
-/

open Set Filter
open scoped Topology

namespace Arlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lexicographic extremizer with a fixed endpoint margin.** -/
theorem exists_supportMinimizing_maximalInteriorAffineCore
    {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    {g h : E → ℝ} (hg : Continuous g) (hh : Continuous h)
    {d : ℕ} (hd : d ≠ 0) (cbase : BFMovingCandidate K g h d)
    {eta : ℝ} (heta : 0 < eta) (heta2 : eta < 1 / 2) :
    ∃ (cmin : BFMovingCandidate K g h d) (a b : ℝ),
      cmin.supportLength = sInf (Set.range
        (fun q : BFMovingCandidate K g h d => q.supportLength)) ∧
      a ∈ Icc eta (1 - eta) ∧ b ∈ Icc eta (1 - eta) ∧ a ≤ b ∧
      ParametricProfileAffineOn cmin.profile a b ∧
      ∀ (q : BFMovingCandidate K g h d) (x y : ℝ),
        q.supportLength = sInf (Set.range
          (fun q : BFMovingCandidate K g h d => q.supportLength)) →
        x ∈ Icc eta (1 - eta) → y ∈ Icc eta (1 - eta) → x ≤ y →
        ParametricProfileAffineOn q.profile x y → y - x ≤ b - a := by
  obtain ⟨cseed, hcseed⟩ := exists_supportMinimizing_BFMovingCandidate
    hK hKconv hg hh hd cbase
  let w : ℝ := sInf (Set.range
    (fun q : BFMovingCandidate K g h d => q.supportLength))
  let S : Set ℝ := {z | ∃ (q : BFMovingCandidate K g h d) (a b : ℝ),
    q.supportLength = w ∧ a ∈ Icc eta (1 - eta) ∧ b ∈ Icc eta (1 - eta) ∧
    a ≤ b ∧ ParametricProfileAffineOn q.profile a b ∧ z = b - a}
  have hhalf : (1 / 2 : ℝ) ∈ Icc eta (1 - eta) := by
    constructor <;> linarith
  have htriv : ParametricProfileAffineOn cseed.profile (1 / 2) (1 / 2) := by
    intro s hs
    ring_nf
  have hzeroS : (0 : ℝ) ∈ S := by
    refine ⟨cseed, 1 / 2, 1 / 2, ?_, hhalf, hhalf, le_rfl, htriv, by ring⟩
    exact hcseed
  have hSne : S.Nonempty := ⟨0, hzeroS⟩
  have hSbdd : BddAbove S := by
    refine ⟨1, ?_⟩
    rintro z ⟨q, a, b, _hq, ha, hb, _hab, _haff, rfl⟩
    linarith [ha.1, hb.2]
  obtain ⟨r, _hrmono, hrto, hrmem⟩ := exists_seq_tendsto_sSup hSne hSbdd
  have hex : ∀ k, ∃ (q : BFMovingCandidate K g h d) (a b : ℝ),
      q.supportLength = w ∧ a ∈ Icc eta (1 - eta) ∧ b ∈ Icc eta (1 - eta) ∧
      a ≤ b ∧ ParametricProfileAffineOn q.profile a b ∧ r k = b - a := by
    intro k
    exact hrmem k
  choose q a b hqw ha hb hab haff hr using hex
  have hqto : Tendsto (fun k => (q k).supportLength) atTop (nhds w) := by
    simpa only [hqw] using tendsto_const_nhds
  obtain ⟨q₀, phi₁, hphi₁, hq₀w, hleft, hright, hprofile⟩ :=
    exists_BFMovingCandidate_limit_exposed hK hKconv hg hh hd q hqto
  obtain ⟨a₀, ha₀mem, phi₂, hphi₂, hatend⟩ :=
    isCompact_Icc.tendsto_subseq (x := fun k => a (phi₁ k)) (fun k => ha (phi₁ k))
  obtain ⟨b₀, hb₀mem, phi₃, hphi₃, hbtend⟩ :=
    isCompact_Icc.tendsto_subseq (x := fun k => b (phi₁ (phi₂ k)))
      (fun k => hb (phi₁ (phi₂ k)))
  let Phi : ℕ → ℕ := phi₁ ∘ phi₂ ∘ phi₃
  have hPhito : Tendsto Phi atTop atTop :=
    hphi₁.tendsto_atTop.comp (hphi₂.tendsto_atTop.comp hphi₃.tendsto_atTop)
  have hatend' : Tendsto (fun k => a (Phi k)) atTop (nhds a₀) :=
    hatend.comp hphi₃.tendsto_atTop
  have hbtend' : Tendsto (fun k => b (Phi k)) atTop (nhds b₀) := hbtend
  have hprofile' : ∀ t, Tendsto (fun k => (q (Phi k)).profile t) atTop
      (nhds (q₀.profile t)) := by
    intro t
    exact ((hprofile t).comp hphi₂.tendsto_atTop).comp hphi₃.tendsto_atTop
  have haff₀ : ParametricProfileAffineOn q₀.profile a₀ b₀ :=
    parametricProfileAffineOn_limit_of_interior
      (fun k => (q (Phi k)).profile_concave)
      (fun k => (q (Phi k)).profile_nonneg)
      (show 0 ≤ bfNormalizedProfileBound d by unfold bfNormalizedProfileBound; positivity)
      (fun k => (q (Phi k)).profile_bound) heta heta2 hatend' hbtend'
      (fun k => ha (Phi k)) (fun k => hb (Phi k)) (fun k => haff (Phi k)) hprofile'
  have hlen : b₀ - a₀ = sSup S := by
    have hrtend : Tendsto (fun k => r (Phi k)) atTop (nhds (sSup S)) :=
      hrto.comp hPhito
    have habtend : Tendsto (fun k => b (Phi k) - a (Phi k)) atTop (nhds (b₀ - a₀)) :=
      hbtend'.sub hatend'
    have heq : (fun k => r (Phi k)) = fun k => b (Phi k) - a (Phi k) := by
      funext k
      exact hr (Phi k)
    rw [heq] at hrtend
    exact tendsto_nhds_unique habtend hrtend
  refine ⟨q₀, a₀, b₀, hq₀w, ha₀mem, hb₀mem, ?_, haff₀, ?_⟩
  · have : 0 ≤ sSup S := le_csSup hSbdd hzeroS
    linarith
  · intro q' x y hq' hx hy hxy hxyAff
    rw [hlen]
    exact le_csSup hSbdd ⟨q', x, y, hq', hx, hy, hxy, hxyAff, rfl⟩

end Arlib

#print axioms Arlib.exists_supportMinimizing_maximalInteriorAffineCore
