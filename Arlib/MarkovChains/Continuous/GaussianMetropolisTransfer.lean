/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.BallWalkTransfer
import Arlib.MarkovChains.Continuous.SpeedyToGaussian

/-!
# Gaussian speedy-to-ordinary transfer at `s`-conductance

This is the Gaussian analogue of `BallWalkTransfer.lean`.  Write

* `mu = (volume.withDensity (gaussianWeight sq)).restrict K`,
* `q = ellGaussianMeasure K delta sq`,
* `pi = uniformOn (volume.withDensity (gaussianWeight sq)) K`, and
* `qProb = ellGaussianProb K delta sq`.

The ordinary and speedy Metropolis-Gaussian kernels have exactly the same unnormalised
escape flow.  If the global Gaussian local-conductance deficit is at most `sm`,

    (1-sm) * mu univ <= q univ,

then the local deficit of every measurable set is at most `sm * mu univ`.  Consequently a
speedy conductance lower bound transfers, with no multiplicative loss, to the ordinary
Metropolis chain's `s`-conductance at every discard threshold at least `sm`; laziness costs
the exact factor two.

This closes the reusable *conductance-transfer* component of the direct-Metropolis route.
It does not close mixing: the repository theorem `tvLe_iterate_of_sConductance` still carries
the Lovasz--Simonovits `hLSs` decay inequality as an unproved binder.  Moreover the currently
proved CV Gaussian average bound is only `sm = 1/2`; a TV target needs a discard threshold
of order `eps/M`, so constant expected wasted-step control alone is quantitatively
insufficient for this route.  One needs either a correspondingly small Gaussian deficit or
the pathwise time-change/concentration argument.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : Nat}

/-! ## 1. Gaussian deficit localisation -/

/-- The speedy Gaussian measure is dominated by the unnormalised ordinary target. -/
theorem ellGaussianMeasure_le_gaussianRestrict
    (K : Set (EuclideanSpace Real (Fin n))) (hK : MeasurableSet K) (delta sq : Real) :
    ellGaussianMeasure K delta sq <=
      ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
        (gaussianWeight sq)).restrict K := by
  rw [Measure.le_iff]
  intro S hS
  rw [Measure.restrict_apply hS]
  exact ellGaussianMeasure_le_withDensity_inter K hK delta sq hS

/-- A global Gaussian `ell`-deficit bounds the deficit on every measurable set.

This is the exact weighted analogue of `volume_inter_le_ellMeasure_add`. -/
theorem gaussianRestrict_apply_le_ellGaussianMeasure_add
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (delta sq : Real) {S : Set (EuclideanSpace Real (Fin n))} (hS : MeasurableSet S)
    {sm : ENNReal} (hsm1 : sm <= 1)
    (hsm : (1 - sm) *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K <= ellGaussianMeasure K delta sq Set.univ)
    (hKtop : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ ⊤) :
    (((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)).restrict K) S <=
      ellGaussianMeasure K delta sq S + sm *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K := by
  let mu : Measure (EuclideanSpace Real (Fin n)) :=
    ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)).restrict K
  let q : Measure (EuclideanSpace Real (Fin n)) := ellGaussianMeasure K delta sq
  have hmu_univ : mu Set.univ =
      ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
        (gaussianWeight sq)) K := by
    simp [mu]
  have hqmu : q <= mu := by
    dsimp [q, mu]
    exact ellGaussianMeasure_le_gaussianRestrict K hK delta sq
  letI : IsFiniteMeasure mu :=
    ⟨by rw [hmu_univ]; exact lt_top_iff_ne_top.2 hKtop⟩
  letI : IsFiniteMeasure q := isFiniteMeasure_of_le mu hqmu
  have hdef : (mu - q) Set.univ <= sm * mu Set.univ := by
    rw [Measure.sub_apply MeasurableSet.univ hqmu]
    apply tsub_le_iff_right.2
    have hsplit : mu Set.univ = sm * mu Set.univ + (1 - sm) * mu Set.univ := by
      rw [← add_mul, add_tsub_cancel_of_le hsm1, one_mul]
    calc
      mu Set.univ = sm * mu Set.univ + (1 - sm) * mu Set.univ := hsplit
      _ <= sm * mu Set.univ + q Set.univ := by
        gcongr
        simpa [q, hmu_univ] using hsm
      _ = sm * mu Set.univ + q Set.univ := rfl
  have hadd : mu - q + q = mu := Measure.sub_add_cancel_of_le hqmu
  calc
    mu S = (mu - q + q) S := by rw [hadd]
    _ = (mu - q) S + q S := Measure.add_apply _ _ _
    _ <= (mu - q) Set.univ + q S := by gcongr; exact Set.subset_univ S
    _ <= sm * mu Set.univ + q S := by gcongr
    _ = ellGaussianMeasure K delta sq S + sm *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K := by
      simp [add_comm, q, hmu_univ]

/-! ## 2. Exact escape-flow identity -/

/-- The ordinary and speedy Gaussian Metropolis chains have identical unnormalised escape
flow.  Their holding terms vanish on `S x S^c`, while their moving terms are literally the
same double integral. -/
theorem flow_metropolisGaussian_compl_eq_flow_speedyMetropolisGaussian
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (delta sq : Real) {S : Set (EuclideanSpace Real (Fin n))} (hS : MeasurableSet S) :
    flow (metropolisGaussian K delta sq)
        (((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)).restrict K) S Sᶜ =
      flow (speedyMetropolisGaussian K delta sq)
        (ellGaussianMeasure K delta sq) S Sᶜ := by
  rw [flow_metropolisGaussian hK delta sq hS hS.compl,
    flow_speedyMetropolisGaussian hK delta sq hS hS.compl]
  have hemp : Sᶜ ∩ (S ∩ K) = (∅ : Set (EuclideanSpace Real (Fin n))) := by
    ext x
    constructor
    · rintro ⟨hxnot, hx, _⟩
      exact (hxnot hx).elim
    · intro hx
      exact hx.elim
  rw [hemp]
  simp

/-! ## 3. Transfer to ordinary Gaussian `s`-conductance -/

/-- The core unnormalised flow bound.  A speedy conductance lower bound times the discounted
Gaussian mass is bounded by ordinary Metropolis escape flow. -/
theorem mul_sub_le_flow_metropolisGaussian
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {delta sq : Real}
    (hG0 : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ 0)
    (hGtop : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ ⊤)
    (hL0 : ellGaussianMeasure K delta sq Set.univ ≠ 0)
    (hLtop : ellGaussianMeasure K delta sq Set.univ ≠ ⊤)
    {sm : ENNReal} (hsm1 : sm <= 1)
    (hsm : (1 - sm) *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K <= ellGaussianMeasure K delta sq Set.univ)
    {phi : ENNReal}
    (hphi : phi <= conductance (speedyMetropolisGaussian K delta sq)
      (ellGaussianProb K delta sq))
    {S : Set (EuclideanSpace Real (Fin n))} (hS : MeasurableSet S)
    (hhalf : 2 *
      (((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
        (gaussianWeight sq)).restrict K) S <=
      ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
        (gaussianWeight sq)) K) :
    phi *
      ((((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
        (gaussianWeight sq)).restrict K) S - sm *
          ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
            (gaussianWeight sq)) K) <=
      flow (metropolisGaussian K delta sq)
        (((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)).restrict K) S Sᶜ := by
  let mu : Measure (EuclideanSpace Real (Fin n)) :=
    ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)).restrict K
  let L : ENNReal := ellGaussianMeasure K delta sq Set.univ
  haveI : IsProbabilityMeasure (ellGaussianProb K delta sq) :=
    isProbabilityMeasure_ellGaussianProb hL0 hLtop
  have hflow : flow (metropolisGaussian K delta sq) mu S Sᶜ =
      L * flow (speedyMetropolisGaussian K delta sq)
        (ellGaussianProb K delta sq) S Sᶜ := by
    rw [flow_metropolisGaussian_compl_eq_flow_speedyMetropolisGaussian hK delta sq hS,
      ellGaussianProb, flow_smul_measure, ← mul_assoc,
      ENNReal.mul_inv_cancel hL0 hLtop, one_mul]
  have hmin : phi * min (ellGaussianProb K delta sq S)
        (ellGaussianProb K delta sq Sᶜ) <=
      flow (speedyMetropolisGaussian K delta sq)
        (ellGaussianProb K delta sq) S Sᶜ :=
    mul_min_le_flow_of_le_conductance
      (isReversible_speedyMetropolisGaussian_prob hK delta sq) hphi hS
  have hLmul : forall T : Set (EuclideanSpace Real (Fin n)),
      L * ellGaussianProb K delta sq T = ellGaussianMeasure K delta sq T := by
    intro T
    rw [ellGaussianProb, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel hL0 hLtop, one_mul]
  have hmass1 : mu S - sm *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K <= L * ellGaussianProb K delta sq S := by
    rw [hLmul]
    exact tsub_le_iff_right.2
      (gaussianRestrict_apply_le_ellGaussianMeasure_add hK delta sq hS hsm1 hsm hGtop)
  have hmumass : mu Set.univ =
      ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
        (gaussianWeight sq)) K := by simp [mu]
  have hsplit : mu S + mu Sᶜ = mu Set.univ := measure_add_measure_compl hS
  have hle : mu S <= mu Sᶜ := by
    have hfin : mu S ≠ ⊤ := ne_top_of_le_ne_top hGtop <| by
      rw [← hmumass]
      exact measure_mono (Set.subset_univ S)
    refine (ENNReal.add_le_add_iff_left hfin).1 ?_
    calc
      mu S + mu S = 2 * mu S := by ring
      _ <= mu Set.univ := by simpa [mu] using hhalf
      _ = mu S + mu Sᶜ := hsplit.symm
  have hmass2 : mu S - sm *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K <=
      L * ellGaussianProb K delta sq Sᶜ := by
    rw [hLmul]
    calc
      mu S - sm *
          ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
            (gaussianWeight sq)) K <=
        mu Sᶜ - sm *
          ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
            (gaussianWeight sq)) K := tsub_le_tsub_right hle _
      _ <= ellGaussianMeasure K delta sq Sᶜ := tsub_le_iff_right.2
        (gaussianRestrict_apply_le_ellGaussianMeasure_add hK delta sq hS.compl
          hsm1 hsm hGtop)
  have hmono : Monotone (fun x : ENNReal => L * x) := fun _ _ h => mul_le_mul_left' h L
  have hmm : min (L * ellGaussianProb K delta sq S)
      (L * ellGaussianProb K delta sq Sᶜ) =
      L * min (ellGaussianProb K delta sq S)
        (ellGaussianProb K delta sq Sᶜ) := hmono.map_min.symm
  calc
    phi * (mu S - sm *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K) <=
      phi * min (L * ellGaussianProb K delta sq S)
        (L * ellGaussianProb K delta sq Sᶜ) := by
          gcongr
          exact le_min hmass1 hmass2
    _ = L * (phi * min (ellGaussianProb K delta sq S)
        (ellGaussianProb K delta sq Sᶜ)) := by rw [hmm]; ring
    _ <= L * flow (speedyMetropolisGaussian K delta sq)
        (ellGaussianProb K delta sq) S Sᶜ := by gcongr
    _ = flow (metropolisGaussian K delta sq) mu S Sᶜ := hflow.symm

/-- Setwise transfer to the ordinary Gaussian Metropolis `s`-conductance. -/
theorem le_conductanceSOn_metropolisGaussian_uniformOn
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {delta sq : Real}
    (hG0 : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ 0)
    (hGtop : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ ⊤)
    (hL0 : ellGaussianMeasure K delta sq Set.univ ≠ 0)
    (hLtop : ellGaussianMeasure K delta sq Set.univ ≠ ⊤)
    {sm : ENNReal} (hsm1 : sm <= 1)
    (hsm : (1 - sm) *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K <= ellGaussianMeasure K delta sq Set.univ)
    {phi : ENNReal}
    (hphi : phi <= conductance (speedyMetropolisGaussian K delta sq)
      (ellGaussianProb K delta sq))
    {discard : ENNReal} (hsmd : sm <= discard)
    {S : Set (EuclideanSpace Real (Fin n))} (hS : MeasurableSet S)
    (hSd : discard < Arlib.uniformOn
      ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
        (gaussianWeight sq)) K S)
    (hShalf : Arlib.uniformOn
      ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
        (gaussianWeight sq)) K S <= 1 / 2) :
    phi <= conductanceSOn (metropolisGaussian K delta sq)
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K) discard S := by
  let nu : Measure (EuclideanSpace Real (Fin n)) :=
    (volume : Measure (EuclideanSpace Real (Fin n))).withDensity (gaussianWeight sq)
  let mu : Measure (EuclideanSpace Real (Fin n)) := nu.restrict K
  let G : ENNReal := nu K
  change phi <= conductanceSOn (metropolisGaussian K delta sq)
    (Arlib.uniformOn nu K) discard S
  have hpiS : Arlib.uniformOn nu K S = G⁻¹ * mu S := by
    rw [Arlib.uniformOn_def, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS]
  have hGpi : G * Arlib.uniformOn nu K S = mu S := by
    rw [hpiS, ← mul_assoc, ENNReal.mul_inv_cancel hG0 hGtop, one_mul]
  have hhalf : 2 * mu S <= G := by
    have hstep : G * Arlib.uniformOn nu K S <= G * (1 / 2) := by gcongr
    rw [hGpi] at hstep
    calc
      2 * mu S <= 2 * (G * (1 / 2)) := by gcongr
      _ = G * (2 * (1 / 2)) := by ring
      _ = G := by rw [two_mul_one_half, mul_one]
  have hd0 : Arlib.uniformOn nu K S - discard ≠ 0 := (tsub_pos_of_lt hSd).ne'
  have hdtop : Arlib.uniformOn nu K S - discard ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_le_ne_top (by norm_num) hShalf) tsub_le_self
  have hflowpi : flow (metropolisGaussian K delta sq) (Arlib.uniformOn nu K) S Sᶜ =
      G⁻¹ * flow (metropolisGaussian K delta sq) mu S Sᶜ := by
    rw [Arlib.uniformOn_def, flow_smul_measure]
  rw [conductanceSOn, ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdtop), hflowpi]
  have hexp : G * (Arlib.uniformOn nu K S - discard) =
      mu S - discard * G := by
    rw [ENNReal.mul_sub (fun _ _ => hGtop), hGpi, mul_comm G discard]
  have hkey : G * (phi * (Arlib.uniformOn nu K S - discard)) <=
      flow (metropolisGaussian K delta sq) mu S Sᶜ := by
    calc
      G * (phi * (Arlib.uniformOn nu K S - discard)) =
          phi * (G * (Arlib.uniformOn nu K S - discard)) := by ring
      _ = phi * (mu S - discard * G) := by rw [hexp]
      _ <= phi * (mu S - sm * G) := by gcongr
      _ <= flow (metropolisGaussian K delta sq) mu S Sᶜ := by
        exact mul_sub_le_flow_metropolisGaussian hK hG0 hGtop hL0 hLtop hsm1 hsm
          hphi hS hhalf
  calc
    phi * (Arlib.uniformOn nu K S - discard) =
        G⁻¹ * (G * (phi * (Arlib.uniformOn nu K S - discard))) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hG0 hGtop, one_mul]
    _ <= G⁻¹ * flow (metropolisGaussian K delta sq) mu S Sᶜ := by gcongr

/-- Infimum-form transfer. -/
theorem le_conductanceS_metropolisGaussian_uniformOn
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {delta sq : Real}
    (hG0 : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ 0)
    (hGtop : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ ⊤)
    (hL0 : ellGaussianMeasure K delta sq Set.univ ≠ 0)
    (hLtop : ellGaussianMeasure K delta sq Set.univ ≠ ⊤)
    {sm : ENNReal} (hsm1 : sm <= 1)
    (hsm : (1 - sm) *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K <= ellGaussianMeasure K delta sq Set.univ)
    {phi : ENNReal}
    (hphi : phi <= conductance (speedyMetropolisGaussian K delta sq)
      (ellGaussianProb K delta sq))
    {discard : ENNReal} (hsmd : sm <= discard) :
    phi <= conductanceS (metropolisGaussian K delta sq)
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K) discard :=
  le_conductanceS_of_forall_midSets _ _ _ _ fun _ hS hSd hShalf =>
    le_conductanceSOn_metropolisGaussian_uniformOn hK hG0 hGtop hL0 hLtop hsm1 hsm
      hphi hsmd hS hSd hShalf

/-- Lazy-chain transfer; the factor two is exact. -/
theorem le_conductanceS_lazy_metropolisGaussian_uniformOn
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {delta sq : Real}
    (hG0 : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ 0)
    (hGtop : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ ⊤)
    (hL0 : ellGaussianMeasure K delta sq Set.univ ≠ 0)
    (hLtop : ellGaussianMeasure K delta sq Set.univ ≠ ⊤)
    {sm : ENNReal} (hsm1 : sm <= 1)
    (hsm : (1 - sm) *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K <= ellGaussianMeasure K delta sq Set.univ)
    {phi : ENNReal}
    (hphi : phi <= conductance (speedyMetropolisGaussian K delta sq)
      (ellGaussianProb K delta sq))
    {discard : ENNReal} (hsmd : sm <= discard) :
    phi / 2 <= conductanceS (lazy (metropolisGaussian K delta sq))
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K) discard := by
  refine le_conductanceS_of_forall_midSets _ _ _ _ fun S hS hSd hShalf => ?_
  rw [conductanceSOn_lazy _ _ _ hS]
  gcongr
  exact le_conductanceSOn_metropolisGaussian_uniformOn hK hG0 hGtop hL0 hLtop hsm1 hsm
    hphi hsmd hS hSd hShalf

/-- The same transfer in the exact scalar form supplied by Gaussian wasted-step analysis.
If `lam` is a lower bound for the Gaussian-weighted average of `ell`, then the discarded
mass parameter is `1-lam`.

This corollary makes the quantitative limitation explicit: the currently proved CV value
`lam = 1/2` only yields thresholds at least `1/2`, whereas an accuracy-`eps` warm-start
mixing theorem needs a threshold of order `eps/M`. -/
theorem le_conductanceS_lazy_metropolisGaussian_uniformOn_of_average
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {delta sq : Real}
    (hG0 : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ 0)
    (hGtop : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ ⊤)
    (hL0 : ellGaussianMeasure K delta sq Set.univ ≠ 0)
    (hLtop : ellGaussianMeasure K delta sq Set.univ ≠ ⊤)
    {lam : ENNReal} (hlam1 : lam <= 1)
    (hlam : lam *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K <= ellGaussianMeasure K delta sq Set.univ)
    {phi : ENNReal}
    (hphi : phi <= conductance (speedyMetropolisGaussian K delta sq)
      (ellGaussianProb K delta sq))
    {discard : ENNReal} (hdiscard : 1 - lam <= discard) :
    phi / 2 <= conductanceS (lazy (metropolisGaussian K delta sq))
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K) discard := by
  apply le_conductanceS_lazy_metropolisGaussian_uniformOn hK hG0 hGtop hL0 hLtop
    (sm := 1 - lam) tsub_le_self
  · simpa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hlam1] using hlam
  · exact hphi
  · exact hdiscard

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.ellGaussianMeasure_le_gaussianRestrict
#print axioms Arlib.MarkovChains.gaussianRestrict_apply_le_ellGaussianMeasure_add
#print axioms Arlib.MarkovChains.flow_metropolisGaussian_compl_eq_flow_speedyMetropolisGaussian
#print axioms Arlib.MarkovChains.mul_sub_le_flow_metropolisGaussian
#print axioms Arlib.MarkovChains.le_conductanceSOn_metropolisGaussian_uniformOn
#print axioms Arlib.MarkovChains.le_conductanceS_metropolisGaussian_uniformOn
#print axioms Arlib.MarkovChains.le_conductanceS_lazy_metropolisGaussian_uniformOn
#print axioms Arlib.MarkovChains.le_conductanceS_lazy_metropolisGaussian_uniformOn_of_average
