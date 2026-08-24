/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.MarkovChains.Continuous.EuclideanBathtub
import Arlib.MarkovChains.Continuous.WarmLSOneStep

/-!
# Lazy set-profile majorization

The key LS decomposition is pointwise.  If `g = T 1_S` is a lazy set profile, then
`g >= 1/2` on `S` and `g <= 1/2` off `S`.  Define

* `u = 2g-1` on `S`, and `0` off `S`;
* `v = 1` on `S`, and `2g` off `S`.

Both weights lie in `[0,1]` and `g=(u+v)/2`.  Their masses are the two LS-shifted
endpoints.  This file first proves the weighted bathtub inequality, then the abstract
midpoint majorization.  The final section verifies the pointwise decomposition itself.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A superlevel bathtub set beats every `[0,1]`-valued weight of the same mass. -/
theorem integral_mul_le_setIntegral_of_between_superlevels
    {mu : Measure Omega} [IsFiniteMeasure mu] {f w : Omega → Real}
    (hf : Integrable f mu) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∀ x, w x ≤ 1) {q : Real} {S : Set Omega} (hS : MeasurableSet S)
    (hstrict : {x | q < f x} ⊆ S) (hweak : S ⊆ {x | q ≤ f x})
    (hmass : ∫ x, w x ∂mu = (mu S).toReal) :
    ∫ x, f x * w x ∂mu ≤ ∫ x in S, f x ∂mu := by
  have hwint : Integrable w mu :=
    Integrable.of_bound hw.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact hw1 x)
  let i : Omega → Real := S.indicator fun _ => 1
  have hi : Measurable i := measurable_const.indicator hS
  have hiint : Integrable i mu := (integrable_const (1 : Real)).indicator hS
  have hcenter : ∫ x, q * w x ∂mu = ∫ x, q * i x ∂mu := by
    rw [integral_const_mul, integral_const_mul, hmass]
    simp [i, integral_indicator_const (1 : Real) hS, measureReal_def]
  have hpoint : ∀ x, (f x - q) * w x ≤ (f x - q) * i x := by
    intro x
    by_cases hx : x ∈ S
    · have hnonneg : 0 ≤ f x - q := sub_nonneg.mpr (hweak hx)
      simp only [i, Set.indicator_of_mem hx, mul_one]
      exact mul_le_of_le_one_right hnonneg (hw1 x)
    · have hnlt : ¬ q < f x := fun h => hx (hstrict h)
      have hnonpos : f x - q ≤ 0 := sub_nonpos.mpr (not_lt.mp hnlt)
      simp only [i, Set.indicator_of_notMem hx, mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hnonpos (hw0 x)
  have hleft : Integrable (fun x => (f x - q) * w x) mu :=
    (hf.sub (integrable_const q)).mul_bdd (c := 1) hw.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact hw1 x)
  have hright : Integrable (fun x => (f x - q) * i x) mu :=
    (hf.sub (integrable_const q)).mul_bdd (c := 1) hi.aestronglyMeasurable
      (Eventually.of_forall fun x => by by_cases hx : x ∈ S <;> simp [i, hx])
  have hmono : ∫ x, (f x - q) * w x ∂mu ≤ ∫ x, (f x - q) * i x ∂mu :=
    integral_mono hleft hright hpoint
  have hfw : Integrable (fun x => f x * w x) mu :=
    hf.mul_bdd (c := 1) hw.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact hw1 x)
  have hfi : Integrable (fun x => f x * i x) mu :=
    hf.mul_bdd (c := 1) hi.aestronglyMeasurable
      (Eventually.of_forall fun x => by by_cases hx : x ∈ S <;> simp [i, hx])
  have hexpandL : ∫ x, (f x - q) * w x ∂mu =
      (∫ x, f x * w x ∂mu) - ∫ x, q * w x ∂mu := by
    have hfun : (fun x => (f x - q) * w x) = fun x => f x * w x - q * w x := by
      funext x; ring
    rw [hfun, integral_sub hfw (hwint.const_mul q)]
  have hexpandR : ∫ x, (f x - q) * i x ∂mu =
      (∫ x, f x * i x ∂mu) - ∫ x, q * i x ∂mu := by
    have hfun : (fun x => (f x - q) * i x) = fun x => f x * i x - q * i x := by
      funext x; ring
    rw [hfun, integral_sub hfi (hiint.const_mul q)]
  rw [hexpandL, hexpandR, hcenter] at hmono
  have hmono' : ∫ x, f x * w x ∂mu ≤ ∫ x, f x * i x ∂mu := by linarith
  calc
    ∫ x, f x * w x ∂mu ≤ ∫ x, f x * i x ∂mu := hmono'
    _ = ∫ x in S, f x ∂mu := by
      rw [← integral_indicator hS]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ S <;> simp [i, hx]

/-- The two weights in the lazy-profile decomposition. -/
noncomputable def lazyProfileLower (S : Set Omega) (g : Omega → Real) : Omega → Real :=
  S.indicator fun x => 2 * g x - 1

noncomputable def lazyProfileUpper (S : Set Omega) (g : Omega → Real) : Omega → Real :=
  S.indicator (fun _ => 1) + Sᶜ.indicator (fun x => 2 * g x)

/-- Pointwise lazy profile decomposition `g=(u+v)/2`. -/
theorem lazyProfile_decomposition {S : Set Omega} {g : Omega → Real}
    (x : Omega) :
    g x = (lazyProfileLower S g x + lazyProfileUpper S g x) / 2 := by
  classical
  by_cases hx : x ∈ S <;> simp [lazyProfileLower, lazyProfileUpper, hx]

/-- Both lazy-profile weights belong to `[0,1]`. -/
theorem lazyProfile_weights_mem_Icc {S : Set Omega} {g : Omega → Real}
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hSin : ∀ x ∈ S, 1 / 2 ≤ g x) (hSout : ∀ x ∉ S, g x ≤ 1 / 2) (x : Omega) :
    lazyProfileLower S g x ∈ Set.Icc 0 1 ∧ lazyProfileUpper S g x ∈ Set.Icc 0 1 := by
  classical
  by_cases hx : x ∈ S
  · have hl : 2 * g x - 1 ∈ Set.Icc (0 : Real) 1 := by
      constructor <;> linarith [hSin x hx, hg1 x]
    have hu : (1 : Real) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
    simpa [lazyProfileLower, lazyProfileUpper, hx] using And.intro hl hu
  · have hl : (0 : Real) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    have hu : 2 * g x ∈ Set.Icc (0 : Real) 1 := by
      constructor <;> linarith [hg0 x, hSout x hx]
    simpa [lazyProfileLower, lazyProfileUpper, hx] using And.intro hl hu

theorem measurable_lazyProfileLower {S : Set Omega} {g : Omega → Real}
    (hS : MeasurableSet S) (hg : Measurable g) : Measurable (lazyProfileLower S g) := by
  exact ((hg.const_mul 2).sub_const 1).indicator hS

theorem measurable_lazyProfileUpper {S : Set Omega} {g : Omega → Real}
    (hS : MeasurableSet S) (hg : Measurable g) : Measurable (lazyProfileUpper S g) := by
  exact (measurable_const.indicator hS).add ((hg.const_mul 2).indicator hS.compl)

/-- Abstract midpoint majorization.  This is the sharp rearrangement step in the lazy
Lovász--Simonovits recursion: a profile which is the average of two `[0,1]` weights is
bounded by the average of the integrals over their equal-mass bathtub selectors. -/
theorem integral_mul_le_average_setIntegrals_of_profile_decomposition
    {mu : Measure Omega} [IsFiniteMeasure mu] {f g u v : Omega → Real}
    (hf : Integrable f mu) (hu : Measurable u) (hv : Measurable v)
    (hu0 : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1)
    (hv0 : ∀ x, 0 ≤ v x) (hv1 : ∀ x, v x ≤ 1)
    (hdecomp : ∀ x, g x = (u x + v x) / 2)
    {qU qV : Real} {U V : Set Omega} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUstrict : {x | qU < f x} ⊆ U) (hUweak : U ⊆ {x | qU ≤ f x})
    (hVstrict : {x | qV < f x} ⊆ V) (hVweak : V ⊆ {x | qV ≤ f x})
    (hUmass : ∫ x, u x ∂mu = (mu U).toReal)
    (hVmass : ∫ x, v x ∂mu = (mu V).toReal) :
    ∫ x, f x * g x ∂mu ≤
      ((∫ x in U, f x ∂mu) + ∫ x in V, f x ∂mu) / 2 := by
  have hfu : Integrable (fun x => f x * u x) mu :=
    hf.mul_bdd (c := 1) hu.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hu0 x)]; exact hu1 x)
  have hfv : Integrable (fun x => f x * v x) mu :=
    hf.mul_bdd (c := 1) hv.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hv0 x)]; exact hv1 x)
  have huBathtub : ∫ x, f x * u x ∂mu ≤ ∫ x in U, f x ∂mu :=
    integral_mul_le_setIntegral_of_between_superlevels hf hu hu0 hu1 hU hUstrict hUweak hUmass
  have hvBathtub : ∫ x, f x * v x ∂mu ≤ ∫ x in V, f x ∂mu :=
    integral_mul_le_setIntegral_of_between_superlevels hf hv hv0 hv1 hV hVstrict hVweak hVmass
  have hid : ∫ x, f x * g x ∂mu =
      ((∫ x, f x * u x ∂mu) + ∫ x, f x * v x ∂mu) / 2 := by
    calc
      ∫ x, f x * g x ∂mu = ∫ x, (f x * u x + f x * v x) / 2 ∂mu := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        change f x * g x = (f x * u x + f x * v x) / 2
        rw [hdecomp x]
        ring
      _ = ((∫ x, f x * u x ∂mu) + ∫ x, f x * v x ∂mu) / 2 := by
        rw [integral_div, integral_add hfu hfv]
  rw [hid]
  exact div_le_div_of_nonneg_right (add_le_add huBathtub hvBathtub) (by norm_num)

theorem integral_mul_le_average_setIntegrals_of_weight_bounds
    {mu : Measure Omega} [IsFiniteMeasure mu] {f g u v : Omega → Real}
    (hf : Integrable f mu) (hu : Measurable u) (hv : Measurable v)
    (hu0 : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1)
    (hv0 : ∀ x, 0 ≤ v x) (hv1 : ∀ x, v x ≤ 1)
    (hdecomp : ∀ x, g x = (u x + v x) / 2) {U V : Set Omega}
    (huBound : ∫ x, f x * u x ∂mu ≤ ∫ x in U, f x ∂mu)
    (hvBound : ∫ x, f x * v x ∂mu ≤ ∫ x in V, f x ∂mu) :
    ∫ x, f x * g x ∂mu ≤
      ((∫ x in U, f x ∂mu) + ∫ x in V, f x ∂mu) / 2 := by
  have hfu : Integrable (fun x => f x * u x) mu :=
    hf.mul_bdd (c := 1) hu.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hu0 x)]; exact hu1 x)
  have hfv : Integrable (fun x => f x * v x) mu :=
    hf.mul_bdd (c := 1) hv.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hv0 x)]; exact hv1 x)
  calc
    ∫ x, f x * g x ∂mu =
        ((∫ x, f x * u x ∂mu) + ∫ x, f x * v x ∂mu) / 2 := by
      calc
        _ = ∫ x, (f x * u x + f x * v x) / 2 ∂mu := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          change f x * g x = (f x * u x + f x * v x) / 2
          rw [hdecomp x]
          ring
        _ = _ := by rw [integral_div, integral_add hfu hfv]
    _ ≤ _ := div_le_div_of_nonneg_right (add_le_add huBound hvBound) (by norm_num)

/-- Lazy-profile midpoint majorization, with the two exact-mass bathtub selectors explicit.
The separate mass identities are precisely where the boundary flow enters the LS curve. -/
theorem integral_mul_lazyProfile_le_average_setIntegrals
    {mu : Measure Omega} [IsFiniteMeasure mu] {f g : Omega → Real}
    (hf : Integrable f mu) (hg : Measurable g) {S : Set Omega} (hS : MeasurableSet S)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hSin : ∀ x ∈ S, 1 / 2 ≤ g x) (hSout : ∀ x ∉ S, g x ≤ 1 / 2)
    {qU qV : Real} {U V : Set Omega} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUstrict : {x | qU < f x} ⊆ U) (hUweak : U ⊆ {x | qU ≤ f x})
    (hVstrict : {x | qV < f x} ⊆ V) (hVweak : V ⊆ {x | qV ≤ f x})
    (hUmass : ∫ x, lazyProfileLower S g x ∂mu = (mu U).toReal)
    (hVmass : ∫ x, lazyProfileUpper S g x ∂mu = (mu V).toReal) :
    ∫ x, f x * g x ∂mu ≤
      ((∫ x in U, f x ∂mu) + ∫ x in V, f x ∂mu) / 2 := by
  have hb := fun x => lazyProfile_weights_mem_Icc hg0 hg1 hSin hSout x
  exact integral_mul_le_average_setIntegrals_of_profile_decomposition hf
    (measurable_lazyProfileLower hS hg) (measurable_lazyProfileUpper hS hg)
    (fun x => (hb x).1.1) (fun x => (hb x).1.2)
    (fun x => (hb x).2.1) (fun x => (hb x).2.2)
    lazyProfile_decomposition hU hV hUstrict hUweak hVstrict hVweak
    hUmass hVmass

/-- The Markov operator on an indicator is the real-valued transition probability. -/
theorem markovOp_indicator_eq_kernel_toReal (P : Kernel Omega Omega) [IsMarkovKernel P]
    {S : Set Omega} (hS : MeasurableSet S) (x : Omega) :
    markovOp P (S.indicator fun _ => (1 : Real)) x = (P x S).toReal := by
  rw [markovOp_apply]
  simpa [measureReal_def] using integral_indicator_const (μ := P x) (1 : Real) hS

/-- The masses of the two profile weights are exactly the LS-shifted endpoint masses.
This identity uses stationarity for the mean of the profile and reversibility to identify
the incoming and outgoing boundary flows. -/
theorem integral_lazyProfileLowerUpper_markovOp_indicator {P : Kernel Omega Omega}
    [IsMarkovKernel P] {pi : Measure Omega} [IsProbabilityMeasure pi]
    (hrev : IsReversible P pi) {S : Set Omega} (hS : MeasurableSet S) :
    let g := markovOp P (S.indicator fun _ => (1 : Real))
    (∫ x, lazyProfileLower S g x ∂pi =
        (pi S).toReal - 2 * (flow P pi S Sᶜ).toReal) ∧
      ∫ x, lazyProfileUpper S g x ∂pi =
        (pi S).toReal + 2 * (flow P pi S Sᶜ).toReal := by
  let i : Omega → Real := S.indicator fun _ => 1
  let g := markovOp P i
  have hi : Measurable i := measurable_const.indicator hS
  have hiLp : MemLp i 2 pi := memLp_two_indicator hS
  have hg : Measurable g := measurable_markovOp P hi
  have hgLp : MemLp g 2 pi := memLp_markovOp hrev.invariant hi hiLp
  have hgint : Integrable g pi := hgLp.integrable (by norm_num)
  have hmean : ∫ x, g x ∂pi = (pi S).toReal := by
    rw [integral_markovOp hrev hi (hiLp.integrable (by norm_num))]
    simpa [i, measureReal_def] using integral_indicator_const (μ := pi) (1 : Real) hS
  have hSc : ∫ x in Sᶜ, g x ∂pi = (flow P pi S Sᶜ).toReal := by
    have hflow : ∫ x, Sᶜ.indicator (fun x => (P x S).toReal) x ∂pi =
        (flow P pi Sᶜ S).toReal := integral_indicator_kernel_toReal P pi hS.compl hS
    rw [hrev Sᶜ S hS.compl hS] at hflow
    rw [← integral_indicator hS.compl]
    calc
      ∫ x, Sᶜ.indicator g x ∂pi =
          ∫ x, Sᶜ.indicator (fun x => (P x S).toReal) x ∂pi := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ Sᶜ
        · simp only [Set.indicator_of_mem hx]
          exact markovOp_indicator_eq_kernel_toReal P hS x
        · simp [hx]
      _ = (flow P pi S Sᶜ).toReal := hflow
  have hSg : ∫ x in S, g x ∂pi =
      (pi S).toReal - (flow P pi S Sᶜ).toReal := by
    have hsplit := integral_add_compl hS hgint
    linarith
  constructor
  · rw [lazyProfileLower, integral_indicator hS]
    rw [integral_sub ((hgint.const_mul 2).integrableOn) (integrable_const (1 : Real)),
      integral_const_mul, setIntegral_const, smul_eq_mul, mul_one, hSg]
    simp only [measureReal_def]
    ring_nf
  · have hone : Integrable (S.indicator fun _ => (1 : Real)) pi :=
      (integrable_const (1 : Real)).indicator hS
    have htwoSc : Integrable (Sᶜ.indicator fun x => 2 * g x) pi :=
      (hgint.const_mul 2).indicator hS.compl
    change ∫ x, S.indicator (fun _ => (1 : Real)) x +
      Sᶜ.indicator (fun x => 2 * g x) x ∂pi = _
    rw [integral_add hone htwoSc, integral_indicator hS,
      integral_indicator hS.compl, integral_const_mul,
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def, hSc]

/-- The indicator profile of a lazy kernel is half the original transition probability plus
half the indicator of the current state. -/
theorem markovOp_lazy_indicator_eq (P : Kernel Omega Omega) [IsMarkovKernel P]
    {S : Set Omega} (hS : MeasurableSet S) (x : Omega) :
    markovOp (lazy P) (S.indicator fun _ => (1 : Real)) x =
      (P x S).toReal / 2 + (S.indicator fun _ => (1 : Real)) x / 2 := by
  rw [markovOp_indicator_eq_kernel_toReal (lazy P) hS x, lazy_apply_set P x hS]
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx, Pi.one_apply]
    rw [ENNReal.toReal_add (by finiteness) (by norm_num), ENNReal.toReal_mul]
    norm_num
    ring
  · simp only [Set.indicator_of_notMem hx, mul_zero, add_zero, ENNReal.toReal_mul]
    norm_num
    ring

/-- All pointwise hypotheses used by the midpoint decomposition hold automatically for a
lazy Markov kernel. -/
theorem lazy_markovOp_indicator_profile_bounds (P : Kernel Omega Omega) [IsMarkovKernel P]
    {S : Set Omega} (hS : MeasurableSet S) :
    let g := markovOp (lazy P) (S.indicator fun _ => (1 : Real))
    (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ 1) ∧
      (∀ x ∈ S, 1 / 2 ≤ g x) ∧ (∀ x ∉ S, g x ≤ 1 / 2) := by
  let g := markovOp (lazy P) (S.indicator fun _ => (1 : Real))
  have hp0 : ∀ x, 0 ≤ (P x S).toReal := fun _ => ENNReal.toReal_nonneg
  have hp1 : ∀ x, (P x S).toReal ≤ 1 := fun x =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [markovOp_lazy_indicator_eq P hS x]
    by_cases hx : x ∈ S <;> simp [hx] <;> positivity
  · rw [markovOp_lazy_indicator_eq P hS x]
    by_cases hx : x ∈ S <;> simp [hx] <;> linarith [hp0 x, hp1 x]
  · rw [markovOp_lazy_indicator_eq P hS x]
    simp only [Set.indicator_of_mem hx, Pi.one_apply]
    exact le_add_of_nonneg_left (div_nonneg (hp0 x) (by norm_num))
  · rw [markovOp_lazy_indicator_eq P hS x]
    simp only [Set.indicator_of_notMem hx, zero_div, add_zero]
    linarith [hp1 x]

/-- Euclidean weighted bathtub principle, including both clipped endpoint masses. -/
theorem exists_weighted_bathtub_maximizer_euclidean {n : Nat} [NeZero n]
    (mu : Measure (EuclideanSpace Real (Fin n))) [IsFiniteMeasure mu]
    (hmu : mu ≪ volume) {f w : EuclideanSpace Real (Fin n) → Real}
    (hfm : Measurable f) (hfi : Integrable f mu)
    (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {a : ENNReal} (hmass : ∫ x, w x ∂mu = a.toReal) (ha : a ≤ mu Set.univ) :
    ∃ U : Set (EuclideanSpace Real (Fin n)), MeasurableSet U ∧ mu U = a ∧
      ∫ x, f x * w x ∂mu ≤ ∫ x in U, f x ∂mu := by
  have hwint : Integrable w mu :=
    Integrable.of_bound hwm.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact hw1 x)
  rcases eq_or_lt_of_le (show 0 ≤ a from zero_le) with rfl | ha0
  · have hwzero : w =ᵐ[mu] 0 :=
      (integral_eq_zero_iff_of_nonneg hw0 hwint).mp (by simpa using hmass)
    refine ⟨∅, MeasurableSet.empty, measure_empty, ?_⟩
    rw [setIntegral_empty]
    have hprod : (fun x => f x * w x) =ᵐ[mu] 0 := by
      filter_upwards [hwzero] with x hx
      have hx' : w x = 0 := by simpa only [Pi.zero_apply] using hx
      simpa only [Pi.zero_apply, hx', mul_zero]
    rw [integral_congr_ae hprod]
    simp only [Pi.zero_apply, integral_zero]
    exact le_rfl
  rcases eq_or_lt_of_le ha with rfl | haU
  · have hsubint : Integrable (fun x => 1 - w x) mu :=
      (integrable_const (1 : Real)).sub hwint
    have hsubmean : ∫ x, (1 - w x) ∂mu = 0 := by
      rw [integral_sub (integrable_const (1 : Real)) hwint, integral_const,
        measureReal_def, hmass]
      ring
    have hwae : w =ᵐ[mu] 1 := by
      have hz : (fun x => 1 - w x) =ᵐ[mu] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => sub_nonneg.mpr (hw1 x)) hsubint).mp hsubmean
      filter_upwards [hz] with x hx
      have hx' : 1 - w x = 0 := by simpa only [Pi.zero_apply] using hx
      simpa only [Pi.one_apply] using (sub_eq_zero.mp hx').symm
    refine ⟨Set.univ, MeasurableSet.univ, rfl, ?_⟩
    rw [setIntegral_univ]
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards [hwae] with x hx
    have hx' : w x = 1 := by simpa only [Pi.one_apply] using hx
    simpa only [hx', mul_one]
  · obtain ⟨q, U, hU, hUa, hstrict, hweak, -⟩ :=
      exists_bathtub_maximizer_euclidean_interior mu hmu hfm hfi ha0 haU
    refine ⟨U, hU, hUa, ?_⟩
    apply integral_mul_le_setIntegral_of_between_superlevels hfi hwm hw0 hw1 hU
      hstrict hweak
    rw [hmass, hUa]

/-- The exact abstract one-step LS curve recursion once the two shifted-mass bathtub
selectors have been chosen.  Endpoint selectors may be `∅` or `univ`; no strict-interior
assumption is made here. -/
theorem lazy_markovProfile_exactMass_curve_recursion
    {P : Kernel Omega Omega} [IsMarkovKernel P] {pi : Measure Omega}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {f : Omega → Real} (hf : Integrable f pi) {S : Set Omega} (hS : MeasurableSet S)
    (hprofile0 : ∀ x, 0 ≤ markovOp P (S.indicator fun _ => (1 : Real)) x)
    (hprofile1 : ∀ x, markovOp P (S.indicator fun _ => (1 : Real)) x ≤ 1)
    (hSin : ∀ x ∈ S, 1 / 2 ≤ markovOp P (S.indicator fun _ => (1 : Real)) x)
    (hSout : ∀ x ∉ S, markovOp P (S.indicator fun _ => (1 : Real)) x ≤ 1 / 2)
    {qU qV : Real} {U V : Set Omega} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUstrict : {x | qU < f x} ⊆ U) (hUweak : U ⊆ {x | qU ≤ f x})
    (hVstrict : {x | qV < f x} ⊆ V) (hVweak : V ⊆ {x | qV ≤ f x})
    (hUmass : (pi U).toReal = (pi S).toReal - 2 * (flow P pi S Sᶜ).toReal)
    (hVmass : (pi V).toReal = (pi S).toReal + 2 * (flow P pi S Sᶜ).toReal) :
    ∫ x, f x * markovOp P (S.indicator fun _ => (1 : Real)) x ∂pi ≤
      ((∫ x in U, f x ∂pi) + ∫ x in V, f x ∂pi) / 2 := by
  have hm := integral_lazyProfileLowerUpper_markovOp_indicator hrev hS
  apply integral_mul_lazyProfile_le_average_setIntegrals hf
    (measurable_markovOp P (measurable_const.indicator hS)) hS
    hprofile0 hprofile1 hSin hSout hU hV hUstrict hUweak hVstrict hVweak
  · exact hm.1.trans hUmass.symm
  · exact hm.2.trans hVmass.symm

/-- Specialized exact-mass curve recursion for a lazy reversible kernel.  All profile
hypotheses are discharged here; only the two bathtub selectors and their shifted masses
remain explicit. -/
theorem lazy_exactMass_curve_recursion
    {P : Kernel Omega Omega} [IsMarkovKernel P] {pi : Measure Omega}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {f : Omega → Real} (hf : Integrable f pi) {S : Set Omega} (hS : MeasurableSet S)
    {qU qV : Real} {U V : Set Omega} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUstrict : {x | qU < f x} ⊆ U) (hUweak : U ⊆ {x | qU ≤ f x})
    (hVstrict : {x | qV < f x} ⊆ V) (hVweak : V ⊆ {x | qV ≤ f x})
    (hUmass : (pi U).toReal = (pi S).toReal - 2 * (flow (lazy P) pi S Sᶜ).toReal)
    (hVmass : (pi V).toReal = (pi S).toReal + 2 * (flow (lazy P) pi S Sᶜ).toReal) :
    ∫ x, f x * markovOp (lazy P) (S.indicator fun _ => (1 : Real)) x ∂pi ≤
      ((∫ x in U, f x ∂pi) + ∫ x in V, f x ∂pi) / 2 := by
  have hb := lazy_markovOp_indicator_profile_bounds P hS
  exact lazy_markovProfile_exactMass_curve_recursion (isReversible_lazy hrev) hf hS
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hU hV hUstrict hUweak hVstrict hVweak
    hUmass hVmass

/-- Fully selected Euclidean lazy one-step LS recursion.  The two endpoint arguments are
clipped by `ENNReal.ofReal`; when either is `0` or `1`, the weighted bathtub theorem chooses
`∅` or `univ` automatically. -/
theorem exists_lazy_exactMass_curve_recursion_euclidean {n : Nat} [NeZero n]
    {P : Kernel (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n))}
    [IsMarkovKernel P] {pi : Measure (EuclideanSpace Real (Fin n))}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpi : pi ≪ volume)
    {f : EuclideanSpace Real (Fin n) → Real} (hfm : Measurable f) (hf : Integrable f pi)
    {S : Set (EuclideanSpace Real (Fin n))} (hS : MeasurableSet S) :
    ∃ U V : Set (EuclideanSpace Real (Fin n)), MeasurableSet U ∧ MeasurableSet V ∧
      pi U = ENNReal.ofReal ((pi S).toReal - 2 * (flow (lazy P) pi S Sᶜ).toReal) ∧
      pi V = ENNReal.ofReal ((pi S).toReal + 2 * (flow (lazy P) pi S Sᶜ).toReal) ∧
      ∫ x, f x * markovOp (lazy P) (S.indicator fun _ => (1 : Real)) x ∂pi ≤
        ((∫ x in U, f x ∂pi) + ∫ x in V, f x ∂pi) / 2 := by
  let g := markovOp (lazy P) (S.indicator fun _ => (1 : Real))
  let u := lazyProfileLower S g
  let v := lazyProfileUpper S g
  have hb := lazy_markovOp_indicator_profile_bounds P hS
  have huw := fun x => lazyProfile_weights_mem_Icc hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 x
  have hum : Measurable u := measurable_lazyProfileLower hS
    (measurable_markovOp (lazy P) (measurable_const.indicator hS))
  have hvm : Measurable v := measurable_lazyProfileUpper hS
    (measurable_markovOp (lazy P) (measurable_const.indicator hS))
  have hui : Integrable u pi := Integrable.of_bound hum.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (huw x).1.1]
      exact (huw x).1.2)
  have hvi : Integrable v pi := Integrable.of_bound hvm.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (huw x).2.1]
      exact (huw x).2.2)
  have hu0 : 0 ≤ ∫ x, u x ∂pi := integral_nonneg (fun x => (huw x).1.1)
  have hv0 : 0 ≤ ∫ x, v x ∂pi := integral_nonneg (fun x => (huw x).2.1)
  have hu1 : ∫ x, u x ∂pi ≤ 1 := by
    calc
      ∫ x, u x ∂pi ≤ ∫ _x, (1 : Real) ∂pi := integral_mono hui (integrable_const 1)
        (fun x => (huw x).1.2)
      _ = 1 := by simp
  have hv1 : ∫ x, v x ∂pi ≤ 1 := by
    calc
      ∫ x, v x ∂pi ≤ ∫ _x, (1 : Real) ∂pi := integral_mono hvi (integrable_const 1)
        (fun x => (huw x).2.2)
      _ = 1 := by simp
  obtain ⟨U, hU, hUa, huBound⟩ := exists_weighted_bathtub_maximizer_euclidean pi hpi
    hfm hf hum (fun x => (huw x).1.1) (fun x => (huw x).1.2)
    (a := ENNReal.ofReal (∫ x, u x ∂pi)) (by simp [ENNReal.toReal_ofReal hu0])
    (by rw [measure_univ]; exact ENNReal.ofReal_le_one.mpr hu1)
  obtain ⟨V, hV, hVa, hvBound⟩ := exists_weighted_bathtub_maximizer_euclidean pi hpi
    hfm hf hvm (fun x => (huw x).2.1) (fun x => (huw x).2.2)
    (a := ENNReal.ofReal (∫ x, v x ∂pi)) (by simp [ENNReal.toReal_ofReal hv0])
    (by rw [measure_univ]; exact ENNReal.ofReal_le_one.mpr hv1)
  have hm := integral_lazyProfileLowerUpper_markovOp_indicator (isReversible_lazy hrev) hS
  refine ⟨U, V, hU, hV, ?_, ?_, ?_⟩
  · rw [hUa]
    exact congrArg ENNReal.ofReal hm.1
  · rw [hVa]
    exact congrArg ENNReal.ofReal hm.2
  · exact integral_mul_le_average_setIntegrals_of_weight_bounds hf hum hvm
      (fun x => (huw x).1.1) (fun x => (huw x).1.2)
      (fun x => (huw x).2.1) (fun x => (huw x).2.2)
      lazyProfile_decomposition huBound hvBound

/-- Warm-start one-step Lovász--Simonovits recursion for a lazy reversible Euclidean chain.
The set `S` is the exact-mass maximizer at time `t+1`; `U,V` are exact-mass maximizers at
the two flow-shifted (and endpoint-clipped) arguments at time `t`. -/
theorem exists_warm_lazy_ls_exactMass_oneStep {n : Nat} [NeZero n]
    {P : Kernel (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n))}
    [IsMarkovKernel P] {pi mu : Measure (EuclideanSpace Real (Fin n))}
    [IsProbabilityMeasure pi] [IsProbabilityMeasure mu]
    (hrev : IsReversible P pi) (hpi : pi ≪ volume) {M : Real} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu pi) (t : Nat)
    {s a c : ENNReal} (hsa : s < a) (hahalf : a ≤ 1 / 2)
    (hc : c ≤ conductanceS (lazy P) pi s) :
    ∃ (h : EuclideanSpace Real (Fin n) → Real)
      (S U V : Set (EuclideanSpace Real (Fin n))),
      Measurable h ∧ (∀ x, 0 ≤ h x) ∧ MemLp h 2 pi ∧
      mu = pi.withDensity (fun x => ENNReal.ofReal (h x)) ∧
      MeasurableSet S ∧ MeasurableSet U ∧ MeasurableSet V ∧ pi S = a ∧
      (∀ T : Set (EuclideanSpace Real (Fin n)), MeasurableSet T → pi T = a →
        ∫ x in T, (markovIter (lazy P) h (t + 1) x - 1) ∂pi ≤
          ∫ x in S, (markovIter (lazy P) h (t + 1) x - 1) ∂pi) ∧
      c * (a - s) ≤ flow (lazy P) pi S Sᶜ ∧
      pi U = ENNReal.ofReal
        ((pi S).toReal - 2 * (flow (lazy P) pi S Sᶜ).toReal) ∧
      pi V = ENNReal.ofReal
        ((pi S).toReal + 2 * (flow (lazy P) pi S Sᶜ).toReal) ∧
      ∫ x in S, (markovIter (lazy P) h (t + 1) x - 1) ∂pi ≤
        ((∫ x in U, (markovIter (lazy P) h t x - 1) ∂pi) +
          ∫ x in V, (markovIter (lazy P) h t x - 1) ∂pi) / 2 := by
  obtain ⟨h, S, hhm, hh0, hhLp, hrepr, hS, hSa, htop, hflow, hpair⟩ :=
    exists_warm_ls_topSet_oneStep (P := lazy P) (isReversible_lazy hrev) hpi hM hwarm t
      hsa hahalf hc
  have hft : Measurable (fun x => markovIter (lazy P) h t x - 1) :=
    (measurable_markovIter (lazy P) hhm t).sub_const 1
  have hfLp : MemLp (markovIter (lazy P) h t) 2 pi :=
    memLp_markovIter (isReversible_lazy hrev).invariant hhm hhLp t
  have hfint : Integrable (fun x => markovIter (lazy P) h t x - 1) pi :=
    (hfLp.integrable (by norm_num)).sub (integrable_const (1 : Real))
  obtain ⟨U, V, hU, hV, hUa, hVa, hmid⟩ :=
    exists_lazy_exactMass_curve_recursion_euclidean hrev hpi hft hfint hS
  refine ⟨h, S, U, V, hhm, hh0, hhLp, hrepr, hS, hU, hV, hSa, htop,
    hflow, hUa, hVa, ?_⟩
  rw [hpair]
  exact hmid

#print axioms Arlib.MarkovChains.integral_mul_le_setIntegral_of_between_superlevels
#print axioms Arlib.MarkovChains.lazyProfile_decomposition
#print axioms Arlib.MarkovChains.lazyProfile_weights_mem_Icc
#print axioms Arlib.MarkovChains.integral_mul_le_average_setIntegrals_of_profile_decomposition
#print axioms Arlib.MarkovChains.integral_mul_le_average_setIntegrals_of_weight_bounds
#print axioms Arlib.MarkovChains.integral_mul_lazyProfile_le_average_setIntegrals
#print axioms Arlib.MarkovChains.markovOp_indicator_eq_kernel_toReal
#print axioms Arlib.MarkovChains.integral_lazyProfileLowerUpper_markovOp_indicator
#print axioms Arlib.MarkovChains.markovOp_lazy_indicator_eq
#print axioms Arlib.MarkovChains.lazy_markovOp_indicator_profile_bounds
#print axioms Arlib.MarkovChains.exists_weighted_bathtub_maximizer_euclidean
#print axioms Arlib.MarkovChains.lazy_markovProfile_exactMass_curve_recursion
#print axioms Arlib.MarkovChains.lazy_exactMass_curve_recursion
#print axioms Arlib.MarkovChains.exists_lazy_exactMass_curve_recursion_euclidean
#print axioms Arlib.MarkovChains.exists_warm_lazy_ls_exactMass_oneStep

end Arlib.MarkovChains
