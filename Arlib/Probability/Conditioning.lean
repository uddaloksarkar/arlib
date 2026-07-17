/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Conditioning a finite probability space on an event

Given a `FinProb` `P` and an event `B` of positive probability, `P.cond B hB`
is the finite probability space obtained by **conditioning on `B`**: outcomes
outside `B` get mass `0`, and outcomes in `B` are reweighted by `1 / Pr B` so
that the masses again sum to one.  We record the defining identities for its
mass, event probabilities (`cond_Pr`, giving `Pr(A ∩ B) / Pr B`), and
expectation (`cond_Ex`).

Everything is proved from first principles with no `sorry`.
-/
import Arlib.Probability.CondExp

namespace Arlib

open scoped BigOperators
open Finset

namespace FinProb

variable (P : FinProb)

/-- The finite probability space obtained by conditioning `P` on an event `B`
of positive probability: outcomes in `B` are reweighted by `1 / Pr B`, outcomes
outside `B` get mass `0`. -/
noncomputable def cond (B : Event P) (hB : 0 < P.Pr B) : FinProb where
  Ω := P.Ω
  mass := fun ω => if ω ∈ B then P.mass ω / P.Pr B else 0
  mass_nonneg := by
    intro ω
    by_cases h : ω ∈ B
    · simp only [h, if_true]
      exact div_nonneg (P.mass_nonneg ω) hB.le
    · simp [h]
  mass_sum := by
    have : (∑ ω, (if ω ∈ B then P.mass ω / P.Pr B else 0))
        = (∑ ω ∈ B, P.mass ω) / P.Pr B := by
      rw [Finset.sum_div]
      rw [← Finset.sum_filter]
      congr 1
      simp [Finset.filter_mem_eq_inter]
    rw [this]
    rw [show (∑ ω ∈ B, P.mass ω) = P.Pr B from rfl]
    exact div_self (ne_of_gt hB)

@[simp] theorem cond_Ω (B : Event P) (hB : 0 < P.Pr B) : (P.cond B hB).Ω = P.Ω := rfl

theorem cond_mass (B : Event P) (hB : 0 < P.Pr B) (ω : P.Ω) :
    (P.cond B hB).mass ω = if ω ∈ B then P.mass ω / P.Pr B else 0 := rfl

/-- **Conditional probability.**  `Pr_{·|B}(A) = Pr(A ∩ B) / Pr(B)`. -/
theorem cond_Pr (B : Event P) (hB : 0 < P.Pr B) (A : Event P) :
    (P.cond B hB).Pr A = P.Pr (A ∩ B) / P.Pr B := by
  rw [show (P.cond B hB).Pr A
        = ∑ ω ∈ A, (if ω ∈ B then P.mass ω / P.Pr B else 0) from rfl,
    Finset.sum_ite_mem, ← Finset.sum_div]
  rfl

/-- **Conditional expectation on an event.**
`Ex_{·|B}[X] = (∑_{ω ∈ B} mass ω · X ω) / Pr B`. -/
theorem cond_Ex (B : Event P) (hB : 0 < P.Pr B) (X : P.Ω → ℝ) :
    (P.cond B hB).Ex X = (∑ ω ∈ B, P.mass ω * X ω) / P.Pr B := by
  have h1 : (P.cond B hB).Ex X
      = ∑ ω, (if ω ∈ B then P.mass ω * X ω / P.Pr B else 0) := by
    simp only [Ex, cond_mass]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ω ∈ B
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [h1, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div]

end FinProb
end Arlib
