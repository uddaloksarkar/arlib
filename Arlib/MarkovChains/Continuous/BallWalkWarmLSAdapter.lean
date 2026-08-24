/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.BallWalkTransfer
import Arlib.MarkovChains.Continuous.WarmLSMixing

/-!
# Warm LS mixing for the ordinary lazy ball walk

`BallWalkTransfer` proves the polynomial `s`-conductance lower bound, but its older
TV consumer retained an abstract Lovasz--Simonovits decay premise.  `WarmLSMixing`
now proves precisely the warm, Euclidean decay theorem.  This file composes the two:
the only scalar obligations left are choosing the smoothness discard and a real lower
bound `ph` below the displayed geometric conductance constant.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

variable {n : Nat}

/-- Polynomial `s`-conductance mixing for the lazy ball walk, with the LS decay theorem
fully discharged.  In applications one chooses `delta` so that
`1-(1-delta)^n <= eps/(2M)` and takes `ph` below the explicit right-hand side. -/
theorem tvLe_iterate_lazy_ballWalk_warm_of_geometry [NeZero n]
    (hn : 2 ≤ n) {K : Set (EuclideanSpace Real (Fin n))}
    (hK : MeasurableSet K) (hconv : Convex Real K)
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K)
    {R delta : Real} (hR : 0 < R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    {mu : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure mu]
    {M ph eps : Real} (hM : 1 ≤ M) (hph0 : 0 < ph) (hphhalf : ph ≤ 1 / 2)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hwarm : IsWarm (ENNReal.ofReal M) mu (Arlib.uniformOn volume K))
    (hsmooth : 1 - ENNReal.ofReal ((1 - delta) ^ n) ≤
      ENNReal.ofReal (eps / (2 * M)))
    (hph : ENNReal.ofReal ph ≤
      min (1 / 16)
        (ENNReal.ofReal (1 / (8 * R)) *
          ENNReal.ofReal (delta / (2 * (n : Real))) / 64) / 2)
    {m : Nat} (hm : lsThresholdS M ph eps ≤ (m : Real)) :
    TVLe (iterate (lazy (ballWalk K delta)) mu m)
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
  have hK0 : volume K ≠ 0 := by
    have hle : volume (ball (0 : EuclideanSpace Real (Fin n)) 1) ≤ volume K :=
      measure_mono hball
    exact ((Metric.measure_ball_pos volume 0 one_pos).trans_le hle).ne'
  have hKtop : volume K ≠ ⊤ := by
    have hsub : K ⊆ closedBall (0 : EuclideanSpace Real (Fin n)) R := by
      intro x hx
      rw [mem_closedBall, dist_zero_right]
      exact hKR x hx
    exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hsub)
  letI : IsProbabilityMeasure (Arlib.uniformOn volume K) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0 hKtop
  have hcgeom := le_conductanceS_lazy_ballWalk_of_ball_subset hn hK hconv hball hR hKR
    hdelta hdelta1 hsmooth
  have hc : ENNReal.ofReal ph ≤
      conductanceS (lazy (ballWalk K delta)) (Arlib.uniformOn volume K)
        (ENNReal.ofReal (eps / (2 * M))) := hph.trans hcgeom
  exact tvLe_iterate_lazy_of_sConductance_warm_euclidean
    (isReversible_ballWalk hK delta)
    (Arlib.uniformOn_absolutelyContinuous volume K)
    hM hph0 hphhalf heps0 heps1 hwarm hc hm

#print axioms tvLe_iterate_lazy_ballWalk_warm_of_geometry

end Arlib.MarkovChains
