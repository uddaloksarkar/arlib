/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.AdjustableRadiusGaussian
import Arlib.Convexity.GaussianCooling.PhaseSamplerTV

/-!
# Adjustable-radius Gaussian phase sampler

This file carries the adjustable-radius conductance theorem through lazy mixing and the
speedy-to-Gaussian rejection map.  With

`a = max 8 (2*q)` and `δ = σ/(a*√n)`,

the explicit deadline is proportional to `a²*n²`; hence it is quadratic in `q` once
`q ≥ 4`.  The final phase-law error is exactly

`64*epsMix + (q*exp (-(q²-1)/2))^n`.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : Nat}

/-- Lazy mixing from the adjustable-radius conductance lower bound. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_uncond_adjustable
    (hn : 21 <= n) {q : Real} (hq : 1 < q) {σ δ R : Real}
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hδq : δ <= σ / (max 8 (2 * q) * Real.sqrt n))
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hK0 : volume K ≠ 0) (hR : 0 <= R) (hKR : ∀ x ∈ K, ‖x‖ <= R)
    (hRσ : R <= q * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure mu0]
    {M eps : Real} (hM : 1 <= M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0 (ellGaussianProb K δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps <= 1)
    {t : Nat} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
      (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2) + 1 <= (t : Real)) :
    MixesWithin (lazy (speedyMetropolisGaussian K δ (σ ^ 2)))
      (ellGaussianProb K δ (σ ^ 2)) mu0 t (ENNReal.ofReal eps) := by
  have hδ8 := step_le_eight_of_le_adjustable (n := n) hσ hδq
  have hs : (0 : Real) < σ ^ 2 := by positivity
  have hKcb : K ⊆ closedBall (0 : EuclideanSpace Real (Fin n)) R := by
    intro x hx
    simpa [mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  haveI : IsProbabilityMeasure (ellGaussianProb K δ (σ ^ 2)) :=
    isProbabilityMeasure_ellGaussianProb
      (ellGaussianMeasure_univ_ne_zero hK hKc hKb hK0 hδ (σ ^ 2))
      (ne_top_of_le_ne_top hKtop (ellGaussianMeasure_univ_le hs K δ))
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ :=
    exists_smallSet_of_absolutelyContinuous (n := n) (by omega)
      (ellGaussianProb K δ (σ ^ 2))
      (ellGaussianProb_absolutelyContinuous K δ (σ ^ 2))
  exact mixesWithin_lazy_of_conductance_sqrt (by omega) hσ hδ hδ8
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    ⟨S0, hS0m, hS0pos, hS0half⟩ hM hwarm heps0 heps1
    (Arlib.conductance_speedyMetropolisGaussian_ge_uncond_adjustable hn hq hσ hδ hδq
      hK hKc hK0 hR hKR hRσ) ht

/-- Algebraic deadline form for adjustable-radius mixing. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit_adjustable
    (hn : 21 <= n) {q : Real} (hq : 1 < q) {σ δ R : Real}
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hδq : δ <= σ / (max 8 (2 * q) * Real.sqrt n))
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hK0 : volume K ≠ 0) (hR : 0 <= R) (hKR : ∀ x ∈ K, ‖x‖ <= R)
    (hRσ : R <= q * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure mu0]
    {M eps : Real} (hM : 1 <= M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0 (ellGaussianProb K δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps <= 1)
    {t : Nat} (ht : 4 * 640 ^ 2 * σ ^ 2 * (n : Real) *
      (Real.log M + 2 * Real.log (1 / eps)) / (δ * Real.log 2) ^ 2 + 1 <= (t : Real)) :
    MixesWithin (lazy (speedyMetropolisGaussian K δ (σ ^ 2)))
      (ellGaussianProb K δ (σ ^ 2)) mu0 t (ENNReal.ofReal eps) := by
  refine mixesWithin_lazy_speedyMetropolisGaussian_uncond_adjustable hn hq hσ hδ hδq
    hK hKc hK0 hR hKR hRσ hM hwarm heps0 heps1 ?_
  have hsq : Real.sqrt (n : Real) ^ 2 = (n : Real) := Real.sq_sqrt (Nat.cast_nonneg n)
  have heq : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
        (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2) =
      4 * 640 ^ 2 * σ ^ 2 * (n : Real) * (Real.log M + 2 * Real.log (1 / eps)) /
        (δ * Real.log 2) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, hsq, div_div_eq_mul_div]
    field_simp
  rw [heq]
  exact ht

/-- At the maximal adjustable step, the deadline displays its quadratic `q` dependence. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_adjustable_truncated
    (hn : 21 <= n) {q : Real} (hq : 1 < q) {σ : Real} (hσ : 0 < σ)
    (hrad : 1 <= q * σ * Real.sqrt n)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K)
    {mu0 : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure mu0]
    {M eps : Real} (hM : 1 <= M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (ellGaussianProb
        (K ∩ closedBall (0 : EuclideanSpace Real (Fin n)) (q * σ * Real.sqrt n))
        (σ / (max 8 (2 * q) * Real.sqrt n)) (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps <= 1)
    {t : Nat} (ht : 4 * 640 ^ 2 * (max 8 (2 * q)) ^ 2 * (n : Real) ^ 2 *
      (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1 <= (t : Real)) :
    MixesWithin
      (lazy (speedyMetropolisGaussian
        (K ∩ closedBall (0 : EuclideanSpace Real (Fin n)) (q * σ * Real.sqrt n))
        (σ / (max 8 (2 * q) * Real.sqrt n)) (σ ^ 2)))
      (ellGaussianProb
        (K ∩ closedBall (0 : EuclideanSpace Real (Fin n)) (q * σ * Real.sqrt n))
        (σ / (max 8 (2 * q) * Real.sqrt n)) (σ ^ 2))
      mu0 t (ENNReal.ofReal eps) := by
  let a : Real := max 8 (2 * q)
  let r : Real := q * σ * Real.sqrt n
  let K' := K ∩ closedBall (0 : EuclideanSpace Real (Fin n)) r
  let δ : Real := σ / (a * Real.sqrt n)
  have ha : 0 < a := by dsimp [a]; positivity
  have hn0 : (0 : Real) < n := by positivity
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hK'm : MeasurableSet K' := measurableSet_inter_closedBall hK r
  have hK'c : Convex Real K' := convex_inter_closedBall hKc r
  have hK'0 : volume K' ≠ 0 := volume_inter_closedBall_ne_zero hball hrad
  have hKR : ∀ x ∈ K', ‖x‖ <= r := fun _ hx => norm_le_of_mem_inter_closedBall hx
  have hmix := mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit_adjustable
    hn hq hσ hδ (show δ <= σ / (max 8 (2 * q) * Real.sqrt n) by rfl)
    hK'm hK'c hK'0 (by dsimp [r]; positivity) hKR
    (show r <= q * σ * Real.sqrt n by rfl) hM hwarm heps0 heps1 (t := t)
  have hsq : Real.sqrt (n : Real) ^ 2 = (n : Real) := Real.sq_sqrt hn0.le
  have heq : 4 * 640 ^ 2 * σ ^ 2 * (n : Real) *
        (Real.log M + 2 * Real.log (1 / eps)) / (δ * Real.log 2) ^ 2 + 1 =
      4 * 640 ^ 2 * a ^ 2 * (n : Real) ^ 2 *
        (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1 := by
    dsimp [δ]
    rw [mul_pow, div_pow, mul_pow, hsq]
    field_simp [ne_of_gt hσ, ne_of_gt ha, ne_of_gt hn0]
  have hdeadline : 4 * 640 ^ 2 * σ ^ 2 * (n : Real) *
      (Real.log M + 2 * Real.log (1 / eps)) / (δ * Real.log 2) ^ 2 + 1 <= (t : Real) := by
    rw [heq]
    simpa only [a] using ht
  have hresult := hmix hdeadline
  simpa only [a, r, K', δ] using hresult

end Arlib.MarkovChains

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n m : Nat}

/-- Adjustable-radius speedy rejection followed by comparison with the full phase law. -/
theorem tvLe_speedyRejection_coolLaw_truncated_relative_adjustable_of_mixing
    (hn : 21 <= n) {q : Real} (hq : 1 < q)
    {σsq : Nat -> Real} (hσsqpos : ∀ j, 0 < σsq j)
    {σ : Real} (hσ : 0 < σ) (hrad : 1 <= q * σ * Real.sqrt n)
    (hstepRejection : σ / (max 8 (2 * q) * Real.sqrt n) <= 1 / (2 * (n : Real)))
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m) (hphase : σsq i = σ ^ 2)
    {mu0 : Measure (EuclSpace n)} [IsProbabilityMeasure mu0]
    {M epsMix : Real} (hM : 1 <= M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (K ∩ closedBall (0 : EuclSpace n) (q * σ * Real.sqrt n))
        (σ / (max 8 (2 * q) * Real.sqrt n)) (σ ^ 2)))
    (heps0 : 0 < epsMix) (heps32 : epsMix <= 1 / 32)
    {t : Nat} (ht : 4 * 640 ^ 2 * (max 8 (2 * q)) ^ 2 * (n : Real) ^ 2 *
      (Real.log M + 2 * Real.log (1 / epsMix)) / Real.log 2 ^ 2 + 1 <= (t : Real)) :
    Arlib.TVLe
      (Arlib.condOn
        ((Measure.map (fun x : EuclSpace n => (1 - 1 / (2 * (n : Real)))⁻¹ • x)
            (Arlib.condOn
              (Arlib.MarkovChains.iterate
                (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyMetropolisGaussian
                  (K ∩ closedBall (0 : EuclSpace n) (q * σ * Real.sqrt n))
                  (σ / (max 8 (2 * q) * Real.sqrt n)) (σsq i))) mu0 t)
              ((1 - 1 / (2 * (n : Real))) •
                (K ∩ closedBall (0 : EuclSpace n) (q * σ * Real.sqrt n))))).withDensity
          fun v => ENNReal.ofReal
            (Arlib.MarkovChains.speedyAcceptReal
              (1 - 1 / (2 * (n : Real))) (σsq i) v))
        Set.univ)
      (coolLaw m σsq K i)
      (64 * ENNReal.ofReal epsMix +
        ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)) := by
  have hn1 : 1 <= n := by omega
  let K' : Set (EuclSpace n) :=
    K ∩ closedBall (0 : EuclSpace n) (q * σ * Real.sqrt n)
  let δ : Real := σ / (max 8 (2 * q) * Real.sqrt n)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hK'm : MeasurableSet K' := Arlib.MarkovChains.measurableSet_inter_closedBall hKm _
  have hK'c : Convex Real K' := Arlib.MarkovChains.convex_inter_closedBall hKc _
  have hK'ball : ball (0 : EuclSpace n) 1 ⊆ K' :=
    Arlib.MarkovChains.unitBall_subset_inter_closedBall hball hrad
  have hK'fin : volume K' ≠ ⊤ := Arlib.MarkovChains.volume_inter_closedBall_ne_top K _
  have hmix := Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_adjustable_truncated
    hn hq hσ hrad hKm hKc hball hM hwarm heps0 (heps32.trans (by norm_num)) ht
  rw [Arlib.MarkovChains.mixesWithin_iff, ← hphase] at hmix
  have hsampler := tvLe_speedyRejection_coolLaw hn1 hσsqpos hK'm hK'c hK'ball hK'fin
    hδ hstepRejection hi hmix (ENNReal.ofReal_le_ofReal heps32)
  have htail := Arlib.MarkovChains.tvLe_coolLaw_inter_closedBall_relative_adjustable
    hn1 hq hσsqpos hσ hKm hKc hball hfin hi hphase hrad
  exact hsampler.trans htail

/-- Elementary radius-selection condition for `A` sampler calls and tail budget `b`. -/
def AdjustableRadiusTailFits (n : Nat) (A b q : Real) : Prop :=
  1 < q ∧ A * (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n <= b

/-- The selectable-radius condition is exactly the accumulated tail-budget certificate. -/
theorem adjustableRadiusTail_accumulated_le {n : Nat} {A b q : Real}
    (hfit : AdjustableRadiusTailFits n A b q) :
    A * (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n <= b := hfit.2

/-- Equivalent per-coordinate form: a fitting radius spends at most `b/A` per call. -/
theorem adjustableRadiusTail_perCoordinate_le {n : Nat} {A b q : Real} (hA : 0 < A)
    (hfit : AdjustableRadiusTailFits n A b q) :
    (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n <= b / A := by
  rw [le_div_iff₀ hA]
  simpa [mul_comm] using hfit.2

end Arlib.GaussianCooling

#print axioms Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_adjustable_truncated
#print axioms Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_truncated_relative_adjustable_of_mixing
#print axioms Arlib.GaussianCooling.adjustableRadiusTail_accumulated_le
#print axioms Arlib.GaussianCooling.adjustableRadiusTail_perCoordinate_le
