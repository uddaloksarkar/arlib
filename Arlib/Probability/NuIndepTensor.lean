import Arlib.Probability.DependenceCovariance
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tensorization of quantitative event independence

Independent coordinate pairs tensorize the event-dependence coefficient additively.
This is the block form needed when the cooling estimator runs one complete scalar path
per sample coordinate.
-/

namespace Arlib.GaussianCooling

open MeasureTheory ProbabilityTheory Set

variable {Omega1 Omega2 A1 A2 B1 B2 : Type*}
  [MeasurableSpace Omega1] [MeasurableSpace Omega2]
  [MeasurableSpace A1] [MeasurableSpace A2]
  [MeasurableSpace B1] [MeasurableSpace B2]

/-- Dependence of two independent coordinate pairs is at most the sum of their
dependence coefficients. -/
theorem NuIndep.prod
    {mu1 : Measure Omega1} {mu2 : Measure Omega2}
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    {X1 : Omega1 → A1} {Y1 : Omega1 → B1}
    {X2 : Omega2 → A2} {Y2 : Omega2 → B2}
    {nu1 nu2 : Real}
    (h1 : NuIndep mu1 X1 Y1 nu1) (h2 : NuIndep mu2 X2 Y2 nu2)
    (hX1 : Measurable X1) (hY1 : Measurable Y1)
    (hX2 : Measurable X2) (hY2 : Measurable Y2) :
    NuIndep (mu1.prod mu2)
      (fun z ↦ (X1 z.1, X2 z.2)) (fun z ↦ (Y1 z.1, Y2 z.2))
      (nu1 + nu2) := by
  intro A B hA hB
  let Xpair : Omega1 × Omega2 → A1 × A2 := fun z ↦ (X1 z.1, X2 z.2)
  let Ypair : Omega1 × Omega2 → B1 × B2 := fun z ↦ (Y1 z.1, Y2 z.2)
  let oneA : A1 × A2 → Real := A.indicator (fun _ ↦ 1)
  let oneB : B1 × B2 → Real := B.indicator (fun _ ↦ 1)
  have honeA : Measurable oneA := measurable_const.indicator hA
  have honeB : Measurable oneB := measurable_const.indicator hB
  have honeA0 : ∀ z, 0 ≤ oneA z := by intro z; by_cases hz : z ∈ A <;> simp [oneA, hz]
  have honeA1 : ∀ z, oneA z ≤ 1 := by intro z; by_cases hz : z ∈ A <;> simp [oneA, hz]
  have honeB0 : ∀ z, 0 ≤ oneB z := by intro z; by_cases hz : z ∈ B <;> simp [oneB, hz]
  have honeB1 : ∀ z, oneB z ≤ 1 := by intro z; by_cases hz : z ∈ B <;> simp [oneB, hz]
  let fA : A1 → Real := fun a1 ↦ ∫ omega2, oneA (a1, X2 omega2) ∂mu2
  let fB : B1 → Real := fun b1 ↦ ∫ omega2, oneB (b1, Y2 omega2) ∂mu2
  have hfA : Measurable fA := by
    have hs := (honeA.comp (measurable_fst.prodMk (hX2.comp measurable_snd))).stronglyMeasurable
    exact (hs.integral_prod_right' (ν := mu2)).measurable
  have hfB : Measurable fB := by
    have hs := (honeB.comp (measurable_fst.prodMk (hY2.comp measurable_snd))).stronglyMeasurable
    exact (hs.integral_prod_right' (ν := mu2)).measurable
  have hfA0 : ∀ a, 0 ≤ fA a := fun a ↦ integral_nonneg fun omega ↦ honeA0 (a, X2 omega)
  have hfB0 : ∀ b, 0 ≤ fB b := fun b ↦ integral_nonneg fun omega ↦ honeB0 (b, Y2 omega)
  have hfA1 : ∀ a, fA a ≤ 1 := by
    intro a
    calc
      fA a ≤ ∫ _omega2, (1 : Real) ∂mu2 := by
        apply integral_mono
        · exact Arlib.integrable_of_forall_mem_Icc
            (honeA.comp (measurable_const.prodMk hX2))
            (fun omega ↦ honeA0 (a, X2 omega)) (fun omega ↦ honeA1 (a, X2 omega))
        · exact integrable_const 1
        · exact fun omega ↦ honeA1 (a, X2 omega)
      _ = 1 := by simp
  have hfB1 : ∀ b, fB b ≤ 1 := by
    intro b
    calc
      fB b ≤ ∫ _omega2, (1 : Real) ∂mu2 := by
        apply integral_mono
        · exact Arlib.integrable_of_forall_mem_Icc
            (honeB.comp (measurable_const.prodMk hY2))
            (fun omega ↦ honeB0 (b, Y2 omega)) (fun omega ↦ honeB1 (b, Y2 omega))
        · exact integrable_const 1
        · exact fun omega ↦ honeB1 (b, Y2 omega)
      _ = 1 := by simp
  have houter :
      |(∫ omega1, fA (X1 omega1) * fB (Y1 omega1) ∂mu1) -
          (∫ omega1, fA (X1 omega1) ∂mu1) *
            ∫ omega1, fB (Y1 omega1) ∂mu1| ≤ nu1 :=
    abs_integral_mul_sub_mul_integral_le_of_unit h1 hX1 hY1 hfA hfB
      hfA0 hfA1 hfB0 hfB1
  let jointInner : Omega1 → Real := fun omega1 ↦
    ∫ omega2, oneA (X1 omega1, X2 omega2) * oneB (Y1 omega1, Y2 omega2) ∂mu2
  have hinner : ∀ omega1,
      |jointInner omega1 - fA (X1 omega1) * fB (Y1 omega1)| ≤ nu2 := by
    intro omega1
    exact abs_integral_mul_sub_mul_integral_le_of_unit h2 hX2 hY2
      (honeA.comp (measurable_const.prodMk measurable_id))
      (honeB.comp (measurable_const.prodMk measurable_id))
      (fun a2 ↦ honeA0 (X1 omega1, a2)) (fun a2 ↦ honeA1 (X1 omega1, a2))
      (fun b2 ↦ honeB0 (Y1 omega1, b2)) (fun b2 ↦ honeB1 (Y1 omega1, b2))
  have hnu2 : 0 ≤ nu2 := by
    simpa using h2 (univ : Set A2) (univ : Set B2) MeasurableSet.univ MeasurableSet.univ
  have hjointMeas : Measurable jointInner := by
    have hs := ((honeA.comp ((hX1.comp measurable_fst).prodMk (hX2.comp measurable_snd))).mul
      (honeB.comp ((hY1.comp measurable_fst).prodMk (hY2.comp measurable_snd))))
      |>.stronglyMeasurable
    exact (hs.integral_prod_right' (ν := mu2)).measurable
  have hfgMeas : Measurable (fun omega1 ↦ fA (X1 omega1) * fB (Y1 omega1)) :=
    (hfA.comp hX1).mul (hfB.comp hY1)
  have hinnerInt :
      |(∫ omega1, jointInner omega1 ∂mu1) -
          ∫ omega1, fA (X1 omega1) * fB (Y1 omega1) ∂mu1| ≤ nu2 := by
    rw [← integral_sub]
    · calc
        |∫ omega1, jointInner omega1 - fA (X1 omega1) * fB (Y1 omega1) ∂mu1| ≤
            ∫ omega1, |jointInner omega1 - fA (X1 omega1) * fB (Y1 omega1)| ∂mu1 :=
          abs_integral_le_integral_abs
        _ ≤ ∫ _omega1, nu2 ∂mu1 := by
          apply integral_mono
          · exact Integrable.mono' (integrable_const nu2)
              (hjointMeas.sub hfgMeas).abs.aestronglyMeasurable
              (Filter.Eventually.of_forall fun omega ↦ by
                simpa [Real.norm_eq_abs] using hinner omega)
          · exact integrable_const nu2
          · exact hinner
        _ = nu2 := by simp
    · exact Arlib.integrable_of_forall_mem_Icc hjointMeas (fun omega ↦ integral_nonneg fun _ ↦
          mul_nonneg (honeA0 _) (honeB0 _)) (fun omega ↦ by
            calc jointInner omega ≤ ∫ _x, (1 : Real) ∂mu2 := by
                  apply integral_mono
                  · exact Arlib.integrable_of_forall_mem_Icc
                      ((honeA.comp (measurable_const.prodMk hX2)).mul
                        (honeB.comp (measurable_const.prodMk hY2)))
                      (fun x ↦ mul_nonneg (honeA0 _) (honeB0 _))
                      (fun x ↦ mul_le_one₀ (honeA1 _) (honeB0 _) (honeB1 _))
                  · exact integrable_const 1
                  · exact fun x ↦ mul_le_one₀ (honeA1 _) (honeB0 _) (honeB1 _)
                _ = 1 := by simp)
    · exact Arlib.integrable_of_forall_mem_Icc hfgMeas
        (fun omega ↦ mul_nonneg (hfA0 _) (hfB0 _))
        (fun omega ↦ mul_le_one₀ (hfA1 _) (hfB0 _) (hfB1 _))
  -- Rewrite the event probabilities as the three Fubini integrals above.
  have hXY : Measurable Xpair :=
    (hX1.comp measurable_fst).prodMk (hX2.comp measurable_snd)
  have hYZ : Measurable Ypair :=
    (hY1.comp measurable_fst).prodMk (hY2.comp measurable_snd)
  have hjoint : (mu1.prod mu2).real
      ((fun z ↦ (X1 z.1, X2 z.2)) ⁻¹' A ∩ (fun z ↦ (Y1 z.1, Y2 z.2)) ⁻¹' B) =
      ∫ omega1, jointInner omega1 ∂mu1 := by
    have hsetOrig : MeasurableSet
        ((fun z : Omega1 × Omega2 ↦ (X1 z.1, X2 z.2)) ⁻¹' A ∩
          (fun z : Omega1 × Omega2 ↦ (Y1 z.1, Y2 z.2)) ⁻¹' B) := by
      simpa [Xpair, Ypair] using (hA.preimage hXY).inter (hB.preimage hYZ)
    rw [← integral_indicator_one hsetOrig]
    rw [integral_prod]
    · apply integral_congr_ae
      filter_upwards with omega1
      apply integral_congr_ae
      filter_upwards with omega2
      by_cases ha : (X1 omega1, X2 omega2) ∈ A <;>
        by_cases hb : (Y1 omega1, Y2 omega2) ∈ B <;>
        simp [oneA, oneB, ha, hb]
    · have hset : MeasurableSet (Xpair ⁻¹' A ∩ Ypair ⁻¹' B) :=
        (hA.preimage hXY).inter (hB.preimage hYZ)
      exact Arlib.integrable_of_forall_mem_Icc (measurable_const.indicator hset)
        (fun z ↦ by by_cases hz : z ∈ Xpair ⁻¹' A ∩ Ypair ⁻¹' B <;>
          simp [Set.indicator, Xpair, Ypair, hz])
        (fun z ↦ by by_cases hz : z ∈ Xpair ⁻¹' A ∩ Ypair ⁻¹' B <;>
          simp [Set.indicator, Xpair, Ypair, hz])
  have hmargA : (mu1.prod mu2).real ((fun z ↦ (X1 z.1, X2 z.2)) ⁻¹' A) =
      ∫ omega1, fA (X1 omega1) ∂mu1 := by
    have hsetOrig : MeasurableSet
        ((fun z : Omega1 × Omega2 ↦ (X1 z.1, X2 z.2)) ⁻¹' A) := by
      simpa [Xpair] using hA.preimage hXY
    rw [← integral_indicator_one hsetOrig, integral_prod]
    · rfl
    · exact Arlib.integrable_of_forall_mem_Icc
        (measurable_const.indicator (hA.preimage hXY))
        (fun z ↦ by by_cases hz : z ∈ Xpair ⁻¹' A <;> simp [Set.indicator, Xpair, hz])
        (fun z ↦ by by_cases hz : z ∈ Xpair ⁻¹' A <;> simp [Set.indicator, Xpair, hz])
  have hmargB : (mu1.prod mu2).real ((fun z ↦ (Y1 z.1, Y2 z.2)) ⁻¹' B) =
      ∫ omega1, fB (Y1 omega1) ∂mu1 := by
    have hsetOrig : MeasurableSet
        ((fun z : Omega1 × Omega2 ↦ (Y1 z.1, Y2 z.2)) ⁻¹' B) := by
      simpa [Ypair] using hB.preimage hYZ
    rw [← integral_indicator_one hsetOrig, integral_prod]
    · rfl
    · exact Arlib.integrable_of_forall_mem_Icc
        (measurable_const.indicator (hB.preimage hYZ))
        (fun z ↦ by by_cases hz : z ∈ Ypair ⁻¹' B <;> simp [Set.indicator, Ypair, hz])
        (fun z ↦ by by_cases hz : z ∈ Ypair ⁻¹' B <;> simp [Set.indicator, Ypair, hz])
  rw [hjoint, hmargA, hmargB]
  calc
    |(∫ omega1, jointInner omega1 ∂mu1) -
        (∫ omega1, fA (X1 omega1) ∂mu1) * ∫ omega1, fB (Y1 omega1) ∂mu1| ≤
        |(∫ omega1, jointInner omega1 ∂mu1) -
          ∫ omega1, fA (X1 omega1) * fB (Y1 omega1) ∂mu1| +
        |(∫ omega1, fA (X1 omega1) * fB (Y1 omega1) ∂mu1) -
          (∫ omega1, fA (X1 omega1) ∂mu1) * ∫ omega1, fB (Y1 omega1) ∂mu1| := by
            exact abs_sub_le _ _ _
    _ ≤ nu2 + nu1 := add_le_add hinnerInt houter
    _ = nu1 + nu2 := add_comm _ _

/-- Pull quantitative independence back along a measure-preserving map of the sample
space. -/
theorem NuIndep.comp_measurePreserving
    {Omega Omega' A B : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure Omega} {mu' : Measure Omega'} {T : Omega → Omega'}
    {X : Omega' → A} {Y : Omega' → B} {nu : Real}
    (h : NuIndep mu' X Y nu) (hT : MeasurePreserving T mu mu')
    (hX : Measurable X) (hY : Measurable Y) :
    NuIndep mu (X ∘ T) (Y ∘ T) nu := by
  intro U V hU hV
  have h0 := h U V hU hV
  rw [← hT.map_eq] at h0
  rw [Measure.real, Measure.map_apply hT.measurable
      ((hU.preimage hX).inter (hV.preimage hY)),
    Measure.real, Measure.map_apply hT.measurable (hU.preimage hX),
    Measure.real, Measure.map_apply hT.measurable (hV.preimage hY)] at h0
  change |mu.real (T ⁻¹' (X ⁻¹' U) ∩ T ⁻¹' (Y ⁻¹' V)) -
    mu.real (T ⁻¹' (X ⁻¹' U)) * mu.real (T ⁻¹' (Y ⁻¹' V))| ≤ nu
  simpa [Measure.real] using h0

universe uOmega uA uB

/-- The induction-friendly heterogeneous finite-product tensorization theorem. -/
theorem nuIndep_pi_aux :
    ∀ (k : Nat) {Omega : Fin k → Type uOmega} {A : Fin k → Type uA}
      {B : Fin k → Type uB}
      [_mOmega : ∀ i, MeasurableSpace (Omega i)]
      [_mA : ∀ i, MeasurableSpace (A i)] [_mB : ∀ i, MeasurableSpace (B i)]
      (mu : ∀ i, Measure (Omega i)) (X : ∀ i, Omega i → A i)
      (Y : ∀ i, Omega i → B i) (nu : Fin k → Real),
      (∀ i, IsProbabilityMeasure (mu i)) →
      (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) →
      (∀ i, NuIndep (mu i) (X i) (Y i) (nu i)) →
      NuIndep (Measure.pi mu)
        (fun omega i ↦ X i (omega i)) (fun omega i ↦ Y i (omega i)) (∑ i, nu i) := by
  intro k
  induction k with
  | zero =>
      intro Omega A B _ _ _ mu X Y nu hmu hX hY h
      haveI : ∀ i, IsProbabilityMeasure (mu i) := hmu
      rw [Fin.sum_univ_zero, nuIndep_zero_iff_indepFun]
      let emptyA : ∀ i : Fin 0, A i := fun i ↦ Fin.elim0 i
      have hconstX : (fun (omega : ∀ i : Fin 0, Omega i) i ↦ X i (omega i)) =
          (fun _omega ↦ emptyA) := by
        funext omega
        exact Subsingleton.elim _ _
      rw [hconstX]
      exact indepFun_const_left emptyA _
  | succ k ih =>
      intro Omega A B _ _ _ mu X Y nu hmu hX hY h
      haveI : ∀ i, IsProbabilityMeasure (mu i) := hmu
      let zero : Fin (k + 1) := 0
      let tailMu : ∀ j : Fin k, Measure (Omega (zero.succAbove j)) :=
        fun j ↦ mu (zero.succAbove j)
      let tailX : ∀ j : Fin k, Omega (zero.succAbove j) → A (zero.succAbove j) :=
        fun j ↦ X (zero.succAbove j)
      let tailY : ∀ j : Fin k, Omega (zero.succAbove j) → B (zero.succAbove j) :=
        fun j ↦ Y (zero.succAbove j)
      let tailNu : Fin k → Real := fun j ↦ nu (zero.succAbove j)
      have htail : NuIndep (Measure.pi tailMu)
          (fun omega j ↦ tailX j (omega j))
          (fun omega j ↦ tailY j (omega j)) (∑ j, tailNu j) := by
        apply ih tailMu tailX tailY tailNu
        · exact fun j ↦ hmu _
        · exact fun j ↦ hX _
        · exact fun j ↦ hY _
        · exact fun j ↦ h _
      let Xprod : Omega zero × (∀ j : Fin k, Omega (zero.succAbove j)) →
          A zero × (∀ j : Fin k, A (zero.succAbove j)) :=
        fun z ↦ (X zero z.1, fun j ↦ tailX j (z.2 j))
      let Yprod : Omega zero × (∀ j : Fin k, Omega (zero.succAbove j)) →
          B zero × (∀ j : Fin k, B (zero.succAbove j)) :=
        fun z ↦ (Y zero z.1, fun j ↦ tailY j (z.2 j))
      have hXtail : Measurable
          (fun (omega : ∀ j : Fin k, Omega (zero.succAbove j)) j ↦ tailX j (omega j)) :=
        measurable_pi_lambda _ fun j ↦ (hX _).comp (measurable_pi_apply j)
      have hYtail : Measurable
          (fun (omega : ∀ j : Fin k, Omega (zero.succAbove j)) j ↦ tailY j (omega j)) :=
        measurable_pi_lambda _ fun j ↦ (hY _).comp (measurable_pi_apply j)
      have hXprod : Measurable Xprod :=
        (hX zero).comp measurable_fst |>.prodMk (hXtail.comp measurable_snd)
      have hYprod : Measurable Yprod :=
        (hY zero).comp measurable_fst |>.prodMk (hYtail.comp measurable_snd)
      have hprod : NuIndep ((mu zero).prod (Measure.pi tailMu)) Xprod Yprod
          (nu zero + ∑ j, tailNu j) := by
        exact (h zero).prod htail (hX zero) (hY zero) hXtail hYtail
      let eOmega := MeasurableEquiv.piFinSuccAbove Omega zero
      have hmp : MeasurePreserving eOmega (Measure.pi mu)
          ((mu zero).prod (Measure.pi tailMu)) := by
        simpa [eOmega, tailMu, zero] using
          (MeasureTheory.measurePreserving_piFinSuccAbove mu (0 : Fin (k + 1)))
      have hpulled : NuIndep (Measure.pi mu) (Xprod ∘ eOmega) (Yprod ∘ eOmega)
          (nu zero + ∑ j, tailNu j) :=
        hprod.comp_measurePreserving hmp hXprod hYprod
      let eA := MeasurableEquiv.piFinSuccAbove A zero
      let eB := MeasurableEquiv.piFinSuccAbove B zero
      have hback := hpulled.comp eA.symm.measurable eB.symm.measurable
      have hxEq : (fun omega ↦ eA.symm ((Xprod ∘ eOmega) omega)) =
          (fun omega i ↦ X i (omega i)) := by
        funext omega
        have hnat : Xprod (eOmega omega) = eA (fun i ↦ X i (omega i)) := by
          apply Prod.ext
          · change X 0 (omega 0) = X 0 (omega 0)
            rfl
          · funext j
            change X j.succ (omega j.succ) = X j.succ (omega j.succ)
            rfl
        change eA.symm (Xprod (eOmega omega)) = _
        rw [hnat]
        exact eA.symm_apply_apply _
      have hyEq : (fun omega ↦ eB.symm ((Yprod ∘ eOmega) omega)) =
          (fun omega i ↦ Y i (omega i)) := by
        funext omega
        have hnat : Yprod (eOmega omega) = eB (fun i ↦ Y i (omega i)) := by
          apply Prod.ext
          · change Y 0 (omega 0) = Y 0 (omega 0)
            rfl
          · funext j
            change Y j.succ (omega j.succ) = Y j.succ (omega j.succ)
            rfl
        change eB.symm (Yprod (eOmega omega)) = _
        rw [hnat]
        exact eB.symm_apply_apply _
      rw [Fin.sum_univ_succAbove nu zero]
      rw [hxEq, hyEq] at hback
      simpa [tailNu] using hback

/-- Finite products of independent coordinate pairs have block dependence bounded by
the sum of the coordinate coefficients. -/
theorem NuIndep.pi {k : Nat} {Omega : Fin k → Type uOmega} {A : Fin k → Type uA}
    {B : Fin k → Type uB}
    [∀ i, MeasurableSpace (Omega i)] [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSpace (B i)]
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {X : ∀ i, Omega i → A i} {Y : ∀ i, Omega i → B i}
    {nu : Fin k → Real} (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (h : ∀ i, NuIndep (mu i) (X i) (Y i) (nu i)) :
    NuIndep (Measure.pi mu) (fun omega i ↦ X i (omega i))
      (fun omega i ↦ Y i (omega i)) (∑ i, nu i) :=
  nuIndep_pi_aux k mu X Y nu (fun _ ↦ inferInstance) hX hY h

/-- Measurable block statistics inherit the tensorized dependence coefficient. -/
theorem NuIndep.pi_comp {k : Nat} {Omega : Fin k → Type uOmega}
    {A : Fin k → Type uA} {B : Fin k → Type uB}
    [∀ i, MeasurableSpace (Omega i)] [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSpace (B i)]
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {X : ∀ i, Omega i → A i} {Y : ∀ i, Omega i → B i}
    {nu : Fin k → Real} (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (h : ∀ i, NuIndep (mu i) (X i) (Y i) (nu i))
    {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    {f : (∀ i, A i) → C} {g : (∀ i, B i) → D}
    (hf : Measurable f) (hg : Measurable g) :
    NuIndep (Measure.pi mu) (fun omega ↦ f (fun i ↦ X i (omega i)))
      (fun omega ↦ g (fun i ↦ Y i (omega i))) (∑ i, nu i) :=
  (NuIndep.pi hX hY h).comp hf hg

/-- Homogeneous-coordinate form: `k` independent copies of a `nu`-independent pair are
block-independent with coefficient `k * nu`. -/
theorem NuIndep.pi_const {k : Nat} {Omega : Type uOmega} {A : Type uA} {B : Type uB}
    [MeasurableSpace Omega] [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → A} {Y : Omega → B} {nu : Real}
    (hX : Measurable X) (hY : Measurable Y) (h : NuIndep mu X Y nu) :
    NuIndep (Measure.pi (fun _ : Fin k ↦ mu))
      (fun omega i ↦ X (omega i)) (fun omega i ↦ Y (omega i)) ((k : Real) * nu) := by
  have hp := NuIndep.pi (k := k) (mu := fun _ ↦ mu) (X := fun _ ↦ X)
    (Y := fun _ ↦ Y) (nu := fun _ ↦ nu) (fun _ ↦ hX) (fun _ ↦ hY) (fun _ ↦ h)
  simpa using hp

/-- Homogeneous tensorization followed by arbitrary measurable block statistics. -/
theorem NuIndep.pi_const_comp {k : Nat} {Omega : Type uOmega} {A : Type uA}
    {B : Type uB} [MeasurableSpace Omega] [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → A} {Y : Omega → B} {nu : Real}
    (hX : Measurable X) (hY : Measurable Y) (h : NuIndep mu X Y nu)
    {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    {f : (Fin k → A) → C} {g : (Fin k → B) → D}
    (hf : Measurable f) (hg : Measurable g) :
    NuIndep (Measure.pi (fun _ : Fin k ↦ mu))
      (fun omega ↦ f (fun i ↦ X (omega i)))
      (fun omega ↦ g (fun i ↦ Y (omega i))) ((k : Real) * nu) :=
  (NuIndep.pi_const hX hY h).comp hf hg

#print axioms NuIndep.prod
#print axioms NuIndep.pi
#print axioms NuIndep.pi_comp
#print axioms NuIndep.pi_const
#print axioms NuIndep.pi_const_comp

end Arlib.GaussianCooling
