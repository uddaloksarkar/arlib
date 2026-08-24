/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.TV

/-!
# Elementary coupling bounds for total variation

Two random variables on the same probability space differ in total variation by at most
the probability that they disagree.  This is the direction of the coupling characterization
needed to replace unbounded rejection loops by finite timeouts.
-/

namespace Arlib

open MeasureTheory Set
open scoped ENNReal

variable {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]

/-- The laws of two coupled random variables are within the mass of their disagreement
event. -/
theorem tvLe_map_map_of_measure_ne_le {mu : Measure Omega} {f g : Omega → E}
    (hf : Measurable f) (hg : Measurable g) {eps : ℝ≥0∞}
    (hne : mu {omega | f omega ≠ g omega} ≤ eps) :
    TVLe (mu.map f) (mu.map g) eps := by
  intro S hS
  rw [Measure.map_apply hf hS, Measure.map_apply hg hS]
  have hsubFG : f ⁻¹' S ⊆ g ⁻¹' S ∪ {omega | f omega ≠ g omega} := by
    intro omega homega
    by_cases heq : f omega = g omega
    · exact Or.inl (by simpa [heq] using homega)
    · exact Or.inr heq
  have hsubGF : g ⁻¹' S ⊆ f ⁻¹' S ∪ {omega | f omega ≠ g omega} := by
    intro omega homega
    by_cases heq : f omega = g omega
    · exact Or.inl (by simpa [heq] using homega)
    · exact Or.inr heq
  constructor
  · calc
      mu (f ⁻¹' S) ≤ mu (g ⁻¹' S ∪ {omega | f omega ≠ g omega}) := measure_mono hsubFG
      _ ≤ mu (g ⁻¹' S) + mu {omega | f omega ≠ g omega} := measure_union_le _ _
      _ ≤ mu (g ⁻¹' S) + eps := by gcongr
  · calc
      mu (g ⁻¹' S) ≤ mu (f ⁻¹' S ∪ {omega | f omega ≠ g omega}) := measure_mono hsubGF
      _ ≤ mu (f ⁻¹' S) + mu {omega | f omega ≠ g omega} := measure_union_le _ _
      _ ≤ mu (f ⁻¹' S) + eps := by gcongr

#print axioms tvLe_map_map_of_measure_ne_le

end Arlib
