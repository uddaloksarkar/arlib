/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.GaussianMetropolisTransfer
import Arlib.MarkovChains.Continuous.RadiusFourGaussian
import Arlib.MarkovChains.Continuous.WarmLSMixing

/-!
# Warm-start LS mixing for the ordinary Gaussian Metropolis walk

This file composes the Gaussian speedy-to-ordinary `s`-conductance transfer with the
Euclidean warm-start Lovasz--Simonovits theorem.  The only analytic inputs left explicit are

* a speedy conductance lower bound, and
* a Gaussian local-conductance deficit small enough for the LS discard scale
  `eps / (2 * M)`.

The second input is genuinely stronger than the currently available average local-conductance
bound.  The latter gives only deficit `1 / 2`, while `eps / (2 * M)` can be arbitrarily small.
Thus an expected-proper-step estimate cannot by itself close deterministic-time mixing.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : Nat}

/-- The normalized Gaussian restriction is absolutely continuous with respect to Euclidean
volume.  This has no positivity or finiteness guards; in the degenerate cases both the
normalization and the absolute-continuity statement still make sense. -/
theorem uniformOn_gaussianWeight_absolutelyContinuous
    (K : Set (EuclideanSpace Real (Fin n))) (sq : Real) :
    Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity (gaussianWeight sq)) K
      ≪ volume :=
  (Arlib.uniformOn_absolutelyContinuous _ _).trans
    (withDensity_absolutelyContinuous _ _)

/-- Concrete warm-start deterministic-time mixing for the lazy ordinary Gaussian Metropolis
walk, conditional on a deficit estimate at the accuracy-dependent LS scale.

The speedy conductance hypothesis is written with `2 * phi`: laziness costs exactly a factor
two in `GaussianMetropolisTransfer`. -/
theorem mixesWithin_lazy_metropolisGaussian_of_small_deficit_warm [NeZero n]
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {delta sq : Real}
    (hG0 : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ 0)
    (hGtop : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ ⊤)
    (hL0 : ellGaussianMeasure K delta sq Set.univ ≠ 0)
    (hLtop : ellGaussianMeasure K delta sq Set.univ ≠ ⊤)
    {mu : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure mu]
    {M phi eps : Real} (hM : 1 ≤ M) (hphi0 : 0 < phi) (hphihalf : phi ≤ 1 / 2)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K))
    {sm : ENNReal} (hsm1 : sm ≤ 1)
    (hsm : (1 - sm) *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K ≤ ellGaussianMeasure K delta sq Set.univ)
    (hspeedy : ENNReal.ofReal (2 * phi) ≤
      conductance (speedyMetropolisGaussian K delta sq) (ellGaussianProb K delta sq))
    (hsms : sm ≤ ENNReal.ofReal (eps / (2 * M)))
    {m : Nat} (hm : lsThresholdS M phi eps ≤ (m : Real)) :
    MixesWithin (lazy (metropolisGaussian K delta sq))
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K) mu m (ENNReal.ofReal eps) := by
  letI : IsProbabilityMeasure
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K) :=
    Arlib.isProbabilityMeasure_uniformOn _ hG0 hGtop
  have hcondRaw := le_conductanceS_lazy_metropolisGaussian_uniformOn hK hG0 hGtop
    hL0 hLtop hsm1 hsm hspeedy hsms
  have hdouble : ENNReal.ofReal (2 * phi) = 2 * ENNReal.ofReal phi := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
    norm_num
  have htwo : (2 : ENNReal) * ENNReal.ofReal phi / 2 = ENNReal.ofReal phi := by
    rw [mul_comm, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  have hcond : ENNReal.ofReal phi ≤
      conductanceS (lazy (metropolisGaussian K delta sq))
        (Arlib.uniformOn
          ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
            (gaussianWeight sq)) K)
        (ENNReal.ofReal (eps / (2 * M))) := by
    rwa [hdouble, htwo] at hcondRaw
  exact tvLe_iterate_lazy_of_sConductance_warm_euclidean
    (isReversible_metropolisGaussian hK delta sq)
    (uniformOn_gaussianWeight_absolutelyContinuous K sq)
    hM hphi0 hphihalf heps0 heps1 hwarm hcond hm

/-- The same adapter exposed directly as a `TVLe` theorem for distributional callers. -/
theorem tvLe_iterate_lazy_metropolisGaussian_of_small_deficit_warm [NeZero n]
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {delta sq : Real}
    (hG0 : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ 0)
    (hGtop : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight sq)) K ≠ ⊤)
    (hL0 : ellGaussianMeasure K delta sq Set.univ ≠ 0)
    (hLtop : ellGaussianMeasure K delta sq Set.univ ≠ ⊤)
    {mu : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure mu]
    {M phi eps : Real} (hM : 1 ≤ M) (hphi0 : 0 < phi) (hphihalf : phi ≤ 1 / 2)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K))
    {sm : ENNReal} (hsm1 : sm ≤ 1)
    (hsm : (1 - sm) *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K ≤ ellGaussianMeasure K delta sq Set.univ)
    (hspeedy : ENNReal.ofReal (2 * phi) ≤
      conductance (speedyMetropolisGaussian K delta sq) (ellGaussianProb K delta sq))
    (hsms : sm ≤ ENNReal.ofReal (eps / (2 * M)))
    {m : Nat} (hm : lsThresholdS M phi eps ≤ (m : Real)) :
    Arlib.TVLe (iterate (lazy (metropolisGaussian K delta sq)) mu m)
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight sq)) K) (ENNReal.ofReal eps) :=
  mixesWithin_lazy_metropolisGaussian_of_small_deficit_warm hK hG0 hGtop hL0 hLtop
    hM hphi0 hphihalf heps0 heps1 hwarm hsm1 hsm hspeedy hsms hm

/-- Radius-four CV specialization.  All speedy-conductance, normalization, boundedness and
reversibility facts are discharged.  The sole non-scalar analytic premise left is the small
Gaussian local-conductance deficit `hsm`; the repository currently proves it only with
`sm = 1 / 2`, which is not enough for a general warm accuracy target. -/
theorem mixesWithin_lazy_metropolisGaussian_radius_four_of_small_deficit [NeZero n]
    (hn : 21 ≤ n) {sigma delta R : Real} (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hdeltasigma : delta ≤ sigma / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRsigma : R ≤ 4 * sigma * Real.sqrt n)
    {mu : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure mu]
    {M eps : Real} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hphiHalf : delta * Real.log 2 / (1280 * sigma * Real.sqrt n) ≤ 1 / 2)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight (sigma ^ 2))) K))
    {sm : ENNReal} (hsm1 : sm ≤ 1)
    (hsm : (1 - sm) *
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight (sigma ^ 2))) K ≤
        ellGaussianMeasure K delta (sigma ^ 2) Set.univ)
    (hsms : sm ≤ ENNReal.ofReal (eps / (2 * M)))
    {m : Nat}
    (hm : lsThresholdS M
      (delta * Real.log 2 / (1280 * sigma * Real.sqrt n)) eps ≤ (m : Real)) :
    MixesWithin (lazy (metropolisGaussian K delta (sigma ^ 2)))
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (gaussianWeight (sigma ^ 2))) K) mu m (ENNReal.ofReal eps) := by
  have hKball : K ⊆ Metric.closedBall (0 : EuclideanSpace Real (Fin n)) R := by
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKball
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKball) measure_closedBall_lt_top)
  have hsquare : 0 < sigma ^ 2 := by positivity
  have hG0 : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight (sigma ^ 2))) K ≠ 0 :=
    withDensity_gaussianWeight_ne_zero _ hK0
  have hGtop : ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
      (gaussianWeight (sigma ^ 2))) K ≠ ⊤ :=
    withDensity_gaussianWeight_ne_top hsquare hK hKtop
  have hL0 : ellGaussianMeasure K delta (sigma ^ 2) Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero hK hKc hKb hK0 hdelta _
  have hLtop : ellGaussianMeasure K delta (sigma ^ 2) Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top hGtop (by
      simpa [Measure.restrict_apply] using
        (ellGaussianMeasure_le_gaussianRestrict K hK delta (sigma ^ 2) Set.univ))
  have hspeedy0 := conductance_speedyMetropolisGaussian_ge_uncond_radius_four hn hsigma
    hdelta hdeltasigma hK hKc hK0 hR hKR hRsigma
  have hscalar :
      2 * (delta * Real.log 2 / (1280 * sigma * Real.sqrt n)) =
        delta * Real.log 2 / (640 * sigma * Real.sqrt n) := by ring
  have hspeedy : ENNReal.ofReal
        (2 * (delta * Real.log 2 / (1280 * sigma * Real.sqrt n))) ≤
      conductance (speedyMetropolisGaussian K delta (sigma ^ 2))
        (ellGaussianProb K delta (sigma ^ 2)) := by
    rwa [hscalar]
  have hphi0 : 0 < delta * Real.log 2 / (1280 * sigma * Real.sqrt n) := by
    positivity
  exact mixesWithin_lazy_metropolisGaussian_of_small_deficit_warm hK hG0 hGtop hL0 hLtop
    hM hphi0 hphiHalf heps0 heps1 hwarm hsm1 hsm hspeedy hsms hm

#print axioms Arlib.MarkovChains.uniformOn_gaussianWeight_absolutelyContinuous
#print axioms Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_of_small_deficit_warm
#print axioms Arlib.MarkovChains.tvLe_iterate_lazy_metropolisGaussian_of_small_deficit_warm
#print axioms Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_radius_four_of_small_deficit

end Arlib.MarkovChains
