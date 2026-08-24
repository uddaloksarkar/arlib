/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.MarkovChains.Continuous.Cheeger
import Arlib.MarkovChains.Continuous.HitAndRunMixing

/-!
# The discounted coarea inequality for `s`-conductance

This file proves the analytic part of the Lovasz--Simonovits `s`-conductance argument that
is already supported by the repository's coarea API.  If `c <= conductanceS P pi s`, then
every measurable set `S` with `s < pi S <= 1/2` satisfies

`c * (pi S - s) <= flow P pi S Sᶜ`.

Integrating this estimate over the superlevel sets of a nonnegative function gives the
discounted `L1` isoperimetric inequality

`2*c*integral_0^infinity (pi {g>t}-s) dt
  <= integral |g x-g y| d(pi x P)`.

This is the coarea half of the Lovasz--Simonovits curve proof.  It does **not** claim the
`hLSs` TV-decay theorem from `HitAndRunMixing`: that proof additionally needs an exact-mass
Hardy--Littlewood/bathtub rearrangement theorem on an atomless probability space.  In
particular one must select, from a level set of a density, a measurable slice of prescribed
measure so that the LS curve is defined at every `x in [0,1]`.  Neither `NullSingletonClass`
nor the current Mathlib measure API supplies this general divisibility theorem.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Clearing the discounted denominator in a lower bound on `s`-conductance.

Unlike the ordinary analogue `conductance_mul_measure_le_flow`, the useful mass is the
excess `pi S - s`.  The strict lower mass bound is exactly what makes this denominator
nonzero. -/
theorem conductanceS_mul_tsub_measure_le_flow (P : Kernel Omega Omega) (pi : Measure Omega)
    [IsProbabilityMeasure pi] {s c : ENNReal} {S : Set Omega}
    (hc : c <= conductanceS P pi s) (hS : MeasurableSet S)
    (hs : s < pi S) (hhalf : pi S <= 1 / 2) :
    c * (pi S - s) <= flow P pi S Sᶜ := by
  have hset : S ∈ MidSets pi s := ⟨hS, hs, hhalf⟩
  have hquot : c <= conductanceSOn P pi s S :=
    hc.trans (iInf₂_le S hset)
  have hne : pi S - s ≠ 0 := (tsub_pos_iff_lt.2 hs).ne'
  have htop : pi S - s ≠ ⊤ := by
    exact ne_top_of_le_ne_top (measure_ne_top pi S) tsub_le_self
  rw [conductanceSOn] at hquot
  calc
    c * (pi S - s) <= (flow P pi S Sᶜ / (pi S - s)) * (pi S - s) := by
      gcongr
    _ = flow P pi S Sᶜ := ENNReal.div_mul_cancel hne htop

/-- The discounted `L1` coarea inequality supplied by a lower bound on `s`-conductance.

For every positive level `t`, the superlevel set of `g` is contained in its positive
support, hence has mass at most `1/2`.  Levels of mass at most `s` contribute zero to the
discounted layer cake.  At all remaining levels
`conductanceS_mul_tsub_measure_le_flow` applies, and reversibility supplies the identical
reverse-flow estimate. -/
theorem two_mul_conductanceS_mul_lintegral_tsub_le_lintegral_abs_sub
    {P : Kernel Omega Omega} [IsMarkovKernel P] {pi : Measure Omega}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {s c : ENNReal}
    (hc : c <= conductanceS P pi s) {g : Omega → Real}
    (hg : Measurable g) (hg0 : ∀ x, 0 <= g x)
    (hsupp : pi {x | 0 < g x} <= 1 / 2) :
    2 * c * ∫⁻ t in Set.Ioi (0 : Real), (pi {x | t < g x} - s)
      <= ∫⁻ p, ENNReal.ofReal |g p.1 - g p.2| ∂(pi ⊗ₘ P) := by
  rw [← lintegral_Ioi_flow_add_flow P pi hg hg0]
  refine le_trans (lintegral_const_mul_le _ _) (lintegral_mono_ae ?_)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  let S : Set Omega := {x | t < g x}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hg
  have hsub : S ⊆ {x | 0 < g x} := by
    intro x hx
    change t < g x at hx
    change 0 < g x
    change 0 < t at ht
    exact lt_trans ht hx
  have hhalf : pi S <= 1 / 2 := (measure_mono hsub).trans hsupp
  by_cases hsmall : pi S <= s
  · have hz : pi S - s = 0 := tsub_eq_zero_of_le hsmall
    change 2 * c * (pi S - s) <= flow P pi S Sᶜ + flow P pi Sᶜ S
    simp [hz]
  · have hs : s < pi S := lt_of_not_ge hsmall
    have hflow := conductanceS_mul_tsub_measure_le_flow P pi hc hS hs hhalf
    rw [hrev Sᶜ S hS.compl hS]
    calc
      2 * c * (pi S - s) = c * (pi S - s) + c * (pi S - s) := by ring
      _ <= flow P pi S Sᶜ + flow P pi S Sᶜ := add_le_add hflow hflow

#print axioms Arlib.MarkovChains.conductanceS_mul_tsub_measure_le_flow
#print axioms Arlib.MarkovChains.two_mul_conductanceS_mul_lintegral_tsub_le_lintegral_abs_sub

end Arlib.MarkovChains
