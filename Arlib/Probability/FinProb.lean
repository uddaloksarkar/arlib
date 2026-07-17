/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# A self-contained finite probability space

Many combinatorial probability arguments live over a *finite* outcome space,
with each outcome carrying an explicit probability (for example, obtained as a
product of coin-toss probabilities).  Rather than pulling in the full
measure-theoretic machinery, we model exactly this: a finite type of outcomes
with a nonnegative mass function summing to one.  This is a bona-fide
(discrete) probability space, and keeps every quantity in `ℝ`, which makes the
combinatorial arguments (union bound, tail bounds) clean and robust.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Prelude

namespace Arlib

open scoped BigOperators
open Finset

/-- A finite probability space: a `Fintype` of outcomes `Ω` with a nonnegative
mass function `mass` summing to `1`. -/
structure FinProb where
  Ω : Type
  [fin : Fintype Ω]
  [dec : DecidableEq Ω]
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  mass_sum : ∑ ω, mass ω = 1

attribute [instance] FinProb.fin FinProb.dec

namespace FinProb

variable (P : FinProb)

/-- Events are subsets of the outcome space, represented as `Finset`s. -/
abbrev Event := Finset P.Ω

/-- The probability of an event is the total mass of its outcomes. -/
def Pr (E : Event P) : ℝ := ∑ ω ∈ E, P.mass ω

@[simp] theorem Pr_empty : P.Pr ∅ = 0 := by simp [Pr]

@[simp] theorem Pr_univ : P.Pr (Finset.univ) = 1 := by
  simpa [Pr] using P.mass_sum

theorem Pr_nonneg (E : Event P) : 0 ≤ P.Pr E :=
  Finset.sum_nonneg fun ω _ => P.mass_nonneg ω

/-- Probability is monotone with respect to event inclusion. -/
theorem Pr_mono {E F : Event P} (h : E ⊆ F) : P.Pr E ≤ P.Pr F :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ω _ _ => P.mass_nonneg ω

theorem Pr_le_one (E : Event P) : P.Pr E ≤ 1 := by
  have h : P.Pr E ≤ P.Pr (Finset.univ) := P.Pr_mono (Finset.subset_univ E)
  simpa [Pr, P.mass_sum] using h

/-- Subadditivity for a binary union: `Pr (A ∪ B) ≤ Pr A + Pr B`. -/
theorem Pr_union_le (A B : Event P) : P.Pr (A ∪ B) ≤ P.Pr A + P.Pr B := by
  have hkey : (∑ ω ∈ A ∪ B, P.mass ω) + (∑ ω ∈ A ∩ B, P.mass ω)
      = (∑ ω ∈ A, P.mass ω) + (∑ ω ∈ B, P.mass ω) :=
    Finset.sum_union_inter
  have hnn : 0 ≤ ∑ ω ∈ A ∩ B, P.mass ω :=
    Finset.sum_nonneg fun ω _ => P.mass_nonneg ω
  unfold Pr
  linarith

/-- Finite union bound (Boole's inequality) over an index `Finset`. -/
theorem Pr_biUnion_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (E : ι → Event P) :
    P.Pr (s.biUnion E) ≤ ∑ i ∈ s, P.Pr (E i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hnotmem ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hnotmem]
      calc
        P.Pr (E i ∪ s.biUnion E) ≤ P.Pr (E i) + P.Pr (s.biUnion E) :=
              P.Pr_union_le _ _
        _ ≤ P.Pr (E i) + ∑ i ∈ s, P.Pr (E i) := by linarith [ih]

/-- Additivity of `Pr` over a **disjoint** binary union. -/
theorem Pr_union_disjoint {A B : Event P} (h : Disjoint A B) :
    P.Pr (A ∪ B) = P.Pr A + P.Pr B := by
  unfold Pr
  exact Finset.sum_union h

/-- An event and its complement (relative to `univ`) partition the total mass. -/
theorem Pr_filter_compl (p : P.Ω → Prop) [DecidablePred p] :
    P.Pr (univ.filter p) + P.Pr (univ.filter (fun ω => ¬ p ω)) = 1 := by
  have hdisj : Disjoint (univ.filter p) (univ.filter (fun ω => ¬ p ω)) := by
    rw [Finset.disjoint_left]
    intro ω h1 h2
    rw [Finset.mem_filter] at h1 h2
    exact h2.2 h1.2
  have hunion : univ.filter p ∪ univ.filter (fun ω => ¬ p ω) = univ := by
    ext ω; by_cases h : p ω <;> simp [h]
  rw [← P.Pr_union_disjoint hdisj, hunion, Pr_univ]

/-- Additivity of `Pr` over a **pairwise-disjoint** finite union. -/
theorem Pr_biUnion_disjoint {ι : Type*}
    (s : Finset ι) (E : ι → Event P)
    (h : (s : Set ι).PairwiseDisjoint E) :
    P.Pr (s.biUnion E) = ∑ i ∈ s, P.Pr (E i) := by
  unfold Pr
  rw [Finset.sum_biUnion h]

end FinProb
end Arlib
