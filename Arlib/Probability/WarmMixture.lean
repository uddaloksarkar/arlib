import Arlib.Probability.TV
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # Warmness under submeasures and mixtures -/

namespace Arlib

open MeasureTheory Set
open ProbabilityTheory
open scoped ENNReal BigOperators

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A submeasure of an `M`-warm measure is still `M`-warm. -/
theorem IsWarm.of_le {M : ENNReal} {mu nu pi : Measure Omega}
    (hmu : mu ≤ nu) (hnu : IsWarm M nu pi) : IsWarm M mu pi := by
  intro S hS
  exact (hmu S).trans (hnu S hS)

/-- Warmness constants add when measures are added. -/
theorem IsWarm.add {M N : ENNReal} {mu nu pi : Measure Omega}
    (hmu : IsWarm M mu pi) (hnu : IsWarm N nu pi) :
    IsWarm (M + N) (mu + nu) pi := by
  intro S hS
  rw [Measure.add_apply mu nu S, add_mul]
  exact add_le_add (hmu S hS) (hnu S hS)

/-- Scaling a warm measure scales its warmness constant by the same factor. -/
theorem IsWarm.smul (c M : ENNReal) {mu pi : Measure Omega}
    (hmu : IsWarm M mu pi) : IsWarm (c * M) (c • mu) pi := by
  intro S hS
  rw [Measure.smul_apply c mu S, smul_eq_mul, mul_assoc]
  exact mul_le_mul_right (hmu S hS) c

/-- Applying the same Markov kernel to both measures preserves warmness. -/
theorem IsWarm.bind {M : ENNReal} {mu pi : Measure Omega}
    (hmu : IsWarm M mu pi)
    {Beta : Type*} [MeasurableSpace Beta]
    (kappa : Kernel Omega Beta) : IsWarm M (mu.bind kappa) (pi.bind kappa) := by
  have hmeasure : mu ≤ M • pi := by
    rw [Measure.le_iff]
    intro S hS
    rw [Measure.smul_apply M pi S, smul_eq_mul]
    exact hmu S hS
  intro T hT
  rw [Measure.bind_apply hT kappa.aemeasurable,
    Measure.bind_apply hT kappa.aemeasurable]
  calc
    (∫⁻ x, kappa x T ∂mu) ≤ ∫⁻ x, kappa x T ∂(M • pi) :=
      lintegral_mono' hmeasure le_rfl
    _ = M * ∫⁻ x, kappa x T ∂pi := by rw [lintegral_smul_measure]; rfl

/-- A finite sum of warm (possibly subprobability) measures is warm with the sum of
the individual constants. -/
theorem isWarm_sum {I : Type*} [Fintype I]
    (mu : I → Measure Omega) (M : I → ENNReal) (pi : Measure Omega)
    (h : ∀ i, IsWarm (M i) (mu i) pi) :
    IsWarm (∑ i, M i) (∑ i, mu i) pi := by
  intro S hS
  rw [Measure.finsetSum_apply Finset.univ mu S, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ ↦ h i S hS

/-- Weighted finite-mixture form. -/
theorem isWarm_sum_smul {I : Type*} [Fintype I]
    (w : I → ENNReal) (mu : I → Measure Omega) (M : I → ENNReal)
    (pi : Measure Omega) (h : ∀ i, IsWarm (M i) (mu i) pi) :
    IsWarm (∑ i, w i * M i) (∑ i, w i • mu i) pi := by
  exact isWarm_sum (fun i ↦ w i • mu i) (fun i ↦ w i * M i) pi
    (fun i ↦ (h i).smul (w i) (M i))

#print axioms IsWarm.of_le
#print axioms IsWarm.add
#print axioms IsWarm.smul
#print axioms IsWarm.bind
#print axioms isWarm_sum
#print axioms isWarm_sum_smul

end Arlib
