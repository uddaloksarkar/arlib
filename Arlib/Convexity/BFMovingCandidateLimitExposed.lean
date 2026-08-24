/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFAffineCoreCompactness

/-!
# An exposed compactness limit for moving BF candidates

`exists_BFMovingCandidate_limit` packages away the convergent subsequence.  Lexicographic BF
extremality additionally needs that subsequence in order to transport affine cores.  This file
provides the same compactness theorem while retaining endpoint and pointwise-profile convergence.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace Arlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_BFMovingCandidate_limit_exposed
    {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    {g h : E → ℝ} (hg : Continuous g) (hh : Continuous h)
    {d : ℕ} (hd : d ≠ 0) (c : ℕ → BFMovingCandidate K g h d) {w : ℝ}
    (hw : Tendsto (fun k => (c k).supportLength) atTop (nhds w)) :
    ∃ (c₀ : BFMovingCandidate K g h d) (phi : ℕ → ℕ),
      StrictMono phi ∧ c₀.supportLength = w ∧
      Tendsto (fun k => (c (phi k)).left) atTop (nhds c₀.left) ∧
      Tendsto (fun k => (c (phi k)).right) atTop (nhds c₀.right) ∧
      ∀ t, Tendsto (fun k => (c (phi k)).profile t) atTop (nhds (c₀.profile t)) := by
  obtain ⟨a₀, ha₀K, phi₁, hphi₁, halim⟩ :=
    hK.tendsto_subseq (x := fun k => (c k).left) (fun k => (c k).left_mem)
  obtain ⟨b₀, hb₀K, phi₂, hphi₂, hblim⟩ :=
    hK.tendsto_subseq (x := fun k => (c (phi₁ k)).right)
      (fun k => (c (phi₁ k)).right_mem)
  obtain ⟨phi₃, hphi₃, V, hVlim⟩ :=
    exists_subseq_tendsto_of_concaveOn_Ioo
      (u := fun k => (c (phi₁ (phi₂ k))).profile)
      (fun k => (c (phi₁ (phi₂ k))).profile_concave)
      (fun k => (c (phi₁ (phi₂ k))).profile_nonneg)
      (fun k => (c (phi₁ (phi₂ k))).profile_bound)
      (fun k => (c (phi₁ (phi₂ k))).profile_off)
  let phi : ℕ → ℕ := phi₁ ∘ phi₂ ∘ phi₃
  have hphi : StrictMono phi := hphi₁.comp (hphi₂.comp hphi₃)
  have halim' : Tendsto (fun k => (c (phi k)).left) atTop (nhds a₀) :=
    (halim.comp hphi₂.tendsto_atTop).comp hphi₃.tendsto_atTop
  have hblim' : Tendsto (fun k => (c (phi k)).right) atTop (nhds b₀) :=
    hblim.comp hphi₃.tendsto_atTop
  have hdist : dist a₀ b₀ = w :=
    tendsto_nhds_unique (halim'.dist hblim') (hw.comp hphi.tendsto_atTop)
  have hconstraints := movingSegment_constraints_closed hK hKconv hd
    (fun k => (c (phi k)).profile_nonneg)
    (fun k => (c (phi k)).profile_bound)
    (fun k => (c (phi k)).profile_off)
    (fun k => (c (phi k)).profile_measurable.aestronglyMeasurable)
    hVlim halim' hblim'
    (fun k => (c (phi k)).left_mem) (fun k => (c (phi k)).right_mem)
    hg hh (fun k => (c (phi k)).g_zero) (fun k => (c (phi k)).h_nonneg)
  have hmassConv := tendsto_integral_profile_mul_movingSegment
    (E := E) (g := fun _ => 1) (d := d) hd
    (fun k => (c (phi k)).profile_nonneg)
    (fun k => (c (phi k)).profile_bound)
    (fun k => (c (phi k)).profile_off)
    (fun k => (c (phi k)).profile_measurable.aestronglyMeasurable)
    hVlim halim' hblim' (continuous_const)
    (G := 1) (fun _ _ _ => by simp)
  have hmass : (∫ t : ℝ, V t ^ d) = 1 := by
    have hconv : Tendsto (fun k => ∫ t : ℝ, (c (phi k)).profile t ^ d) atTop
        (nhds (∫ t : ℝ, V t ^ d)) := by simpa using hmassConv
    exact tendsto_nhds_unique hconv
      (tendsto_atTop_of_eventually_const (i₀ := 0) fun k _ => (c (phi k)).mass_one)
  have hVoff : ∀ t, t ∉ Icc (0 : ℝ) 1 → V t = 0 := by
    intro t ht
    have hz : Tendsto (fun k => (c (phi k)).profile t) atTop (nhds 0) := by
      have heq : (fun k => (c (phi k)).profile t) = fun _ : ℕ => (0 : ℝ) := by
        funext k
        exact (c (phi k)).profile_off t ht
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hVlim t) hz
  have hVmeas : Measurable V := by
    refine measurable_of_tendsto_metrizable' atTop
      (fun k => (c (phi k)).profile_measurable) ?_
    exact tendsto_pi_nhds.mpr hVlim
  let c₀ : BFMovingCandidate K g h d := {
    left := a₀
    right := b₀
    left_mem := ha₀K
    right_mem := hb₀K
    profile := V
    profile_concave := concaveOn_of_tendsto (convex_Ioo (0 : ℝ) 1)
      (fun k => (c (phi k)).profile_concave) (fun t _ => hVlim t)
    profile_nonneg := fun t => ge_of_tendsto (hVlim t)
      (Eventually.of_forall fun k => (c (phi k)).profile_nonneg t)
    profile_bound := fun t => le_of_tendsto (hVlim t)
      (Eventually.of_forall fun k => (c (phi k)).profile_bound t)
    profile_off := hVoff
    profile_measurable := hVmeas
    mass_one := hmass
    g_zero := hconstraints.1
    h_nonneg := hconstraints.2 }
  refine ⟨c₀, phi, hphi, ?_, halim', hblim', ?_⟩
  · exact hdist
  · exact hVlim

end Arlib

#print axioms Arlib.exists_BFMovingCandidate_limit_exposed
