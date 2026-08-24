/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.DeltaIndependence
import Arlib.MarkovChains.Continuous.TrajTransfer

/-!
# Inhomogeneous Markov trajectories and quantitative past/future independence

The Gaussian cooling algorithm changes its transition kernel between samples.  Mathlib's
Ionescu--Tulcea construction already supports this; this file packages the special case in
which the kernel at time `i` reads only the last state.  A uniform TV mixing estimate for
that kernel then gives exactly the past/next `NuIndep` statement used by Cousins--Vempala's
`lem:delta-ind`.
-/

namespace Arlib.Probability

open MeasureTheory ProbabilityTheory
open Arlib.GaussianCooling
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E]

/-- The Ionescu--Tulcea history kernel associated with a time-dependent Markov kernel. -/
noncomputable def inhomogeneousHistoryKernel (P : Nat -> Kernel E E) (i : Nat) :
    Kernel ((_j : Finset.Iic i) -> E) E :=
  Kernel.comap (P i) (fun h => h ⟨i, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance (P : Nat -> Kernel E E) [∀ i, IsMarkovKernel (P i)] (i : Nat) :
    IsMarkovKernel (inhomogeneousHistoryKernel P i) := by
  unfold inhomogeneousHistoryKernel
  infer_instance

/-- The law of the infinite trajectory driven successively by `P 0, P 1, ...`. -/
noncomputable def inhomogeneousPathMeasure (P : Nat -> Kernel E E)
    [∀ i, IsMarkovKernel (P i)] (mu : Measure E) : Measure (Nat -> E) :=
  Kernel.trajMeasure (X := fun _ : Nat => E) mu (inhomogeneousHistoryKernel P)

instance (P : Nat -> Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure E) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (inhomogeneousPathMeasure P mu) := by
  unfold inhomogeneousPathMeasure
  infer_instance

/-- The exact joint law of the history through `i` and the next state. -/
theorem map_history_next_inhomogeneousPathMeasure
    (P : Nat -> Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure E) [IsProbabilityMeasure mu] (i : Nat) :
    (inhomogeneousPathMeasure P mu).map (Preorder.frestrictLe i) ⊗ₘ
        inhomogeneousHistoryKernel P i =
      (inhomogeneousPathMeasure P mu).map
        (fun omega => (Preorder.frestrictLe i omega, omega (i + 1))) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : Nat => E) (μ₀ := mu) (κ := inhomogeneousHistoryKernel P) (a := i)

/-- A pointwise mixing estimate for the time-`i` transition makes the entire past and the
next state `nu`-independent.  This is the operational Markov-law form of
Cousins--Vempala `lem:delta-ind` (b). -/
theorem nuIndep_history_next_inhomogeneousPathMeasure
    (P : Nat -> Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure E) [IsProbabilityMeasure mu]
    (tau : Measure E) [IsProbabilityMeasure tau] (i : Nat) {nu : ENNReal}
    (hnu : nu ≠ ⊤) (hmix : ∀ x, Arlib.TVLe (P i x) tau nu) :
    NuIndep (inhomogeneousPathMeasure P mu) (Preorder.frestrictLe i)
      (fun omega => omega (i + 1)) nu.toReal := by
  let rho := (inhomogeneousPathMeasure P mu).map (Preorder.frestrictLe i)
  let kappa := inhomogeneousHistoryKernel P i
  letI : IsProbabilityMeasure rho := by
    dsimp [rho]
    exact Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe i).aemeasurable
  have hmix' : ∀ h, Arlib.TVLe (kappa h) tau nu := by
    intro h
    exact hmix (h ⟨i, Finset.mem_Iic.2 le_rfl⟩)
  have hdep : NuIndep (rho ⊗ₘ kappa)
      (Prod.fst : ((Finset.Iic i -> E) × E) -> (Finset.Iic i -> E))
      (Prod.snd : ((Finset.Iic i -> E) × E) -> E) nu.toReal :=
    nuIndep_compProd_of_tvLe hnu hmix'
  have hjoint : rho ⊗ₘ kappa =
      (inhomogeneousPathMeasure P mu).map
        (fun omega => (Preorder.frestrictLe i omega, omega (i + 1))) :=
    map_history_next_inhomogeneousPathMeasure P mu i
  intro A B hA hB
  have hrect := hdep A B hA hB
  rw [hjoint] at hrect
  have hpair : Measurable
      (fun omega : Nat -> E => (Preorder.frestrictLe i omega, omega (i + 1))) := by
    fun_prop
  have hAB : MeasurableSet
      (Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B : Set ((Finset.Iic i -> E) × E)) :=
    hA.preimage measurable_fst |>.inter (hB.preimage measurable_snd)
  have hA' : MeasurableSet
      (Prod.fst ⁻¹' A : Set ((Finset.Iic i -> E) × E)) :=
    hA.preimage measurable_fst
  have hB' : MeasurableSet
      (Prod.snd ⁻¹' B : Set ((Finset.Iic i -> E) × E)) :=
    hB.preimage measurable_snd
  rw [Measure.real, Measure.map_apply hpair hAB, Measure.real,
    Measure.map_apply hpair hA', Measure.real, Measure.map_apply hpair hB'] at hrect
  change |(inhomogeneousPathMeasure P mu).real
      (Preorder.frestrictLe i ⁻¹' A ∩ (fun omega => omega (i + 1)) ⁻¹' B) -
        (inhomogeneousPathMeasure P mu).real (Preorder.frestrictLe i ⁻¹' A) *
          (inhomogeneousPathMeasure P mu).real
            ((fun omega => omega (i + 1)) ⁻¹' B)| ≤ nu.toReal at hrect
  exact hrect

/-- Measurable statistics of the past and the next state inherit the same dependence
budget.  This is the direct bridge from the trajectory theorem to the truncated `U_i,V_i`
variables in the volume-estimator proof. -/
theorem nuIndep_historyStatistic_nextStatistic_inhomogeneousPathMeasure
    (P : Nat -> Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure E) [IsProbabilityMeasure mu]
    (tau : Measure E) [IsProbabilityMeasure tau] (i : Nat) {nu : ENNReal}
    (hnu : nu ≠ ⊤) (hmix : ∀ x, Arlib.TVLe (P i x) tau nu)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (f : (Finset.Iic i -> E) -> A) (g : E -> B)
    (hf : Measurable f) (hg : Measurable g) :
    NuIndep (inhomogeneousPathMeasure P mu)
      (fun omega => f (Preorder.frestrictLe i omega))
      (fun omega => g (omega (i + 1))) nu.toReal :=
  (nuIndep_history_next_inhomogeneousPathMeasure P mu tau i hnu hmix).comp hf hg

/-- Rewriting-friendly form of the previous theorem for observables already defined on the
whole path space, once their factorization through past and next state is supplied. -/
theorem nuIndep_of_history_next_factorization_inhomogeneousPathMeasure
    (P : Nat -> Kernel E E) [∀ i, IsMarkovKernel (P i)]
    (mu : Measure E) [IsProbabilityMeasure mu]
    (tau : Measure E) [IsProbabilityMeasure tau] (i : Nat) {nu : ENNReal}
    (hnu : nu ≠ ⊤) (hmix : ∀ x, Arlib.TVLe (P i x) tau nu)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {U : (Nat -> E) -> A} {V : (Nat -> E) -> B}
    (f : (Finset.Iic i -> E) -> A) (g : E -> B)
    (hf : Measurable f) (hg : Measurable g)
    (hU : U = fun omega => f (Preorder.frestrictLe i omega))
    (hV : V = fun omega => g (omega (i + 1))) :
    NuIndep (inhomogeneousPathMeasure P mu) U V nu.toReal := by
  rw [hU, hV]
  exact nuIndep_historyStatistic_nextStatistic_inhomogeneousPathMeasure
    P mu tau i hnu hmix f g hf hg

#print axioms map_history_next_inhomogeneousPathMeasure
#print axioms nuIndep_history_next_inhomogeneousPathMeasure
#print axioms nuIndep_historyStatistic_nextStatistic_inhomogeneousPathMeasure
#print axioms nuIndep_of_history_next_factorization_inhomogeneousPathMeasure

end Arlib.Probability
