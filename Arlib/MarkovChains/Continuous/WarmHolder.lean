/-
# Hölder refinement of the warm-start bound

`Arlib.MarkovChains.lintegral_le_of_isWarm` pays the warmness factor `M` in full and throws
away the mass of `μ`.  That is exact when `μ` is a probability measure, but in a rejection
loop the round-`j` law is *unnormalised*, with mass `sⱼ` decaying geometrically, and summing
the plain bound over `L` rounds costs a factor `L` that the truth does not.

The mass cannot simply be multiplied in: `μ ≤ M·π` with `μ(univ) = s` does **not** give
`∫f dμ ≤ s·M·∫f dπ` — take `μ = M·(π|_T)` with `π(T) = s/M` and `f = 1_T`, where the left
side is `s` and the right is `s²`.  What *is* available is Hölder, and at a conjugate pair
`(p, q)` the mass enters as `μ(univ)^{1/q}`:

    ∫f dμ  ≤  (M · ∫ f^p dπ)^{1/p} · μ(univ)^{1/q}.

The proof needs no Radon–Nikodym derivative and no absolute continuity: it is Hölder against
`μ` with the second factor the constant `1`, followed by the plain warm bound applied to
`f^p`.  Warmness is used exactly once, on `f^p` rather than on `f`.

Taking `p → 1` trades a stronger integrability demand on `f` for a weaker one on the mass;
that trade is the point, and `LocalConductanceMoment.lean` is what makes the `L^p(π)` norm
finite at `p = 1 + 1/(2n)`.
-/
import Arlib.MarkovChains.Continuous.WastedSteps
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Om : Type*} [MeasurableSpace Om]

/-- **The Hölder warm bound.**  At a conjugate pair `(p, q)`,

    `∫f dμ ≤ (M · ∫ f^p dπ)^{1/p} · μ(univ)^{1/q}`.

At `p = 1` this degenerates to `lintegral_le_of_isWarm`; the content is at `p > 1`, where the
mass `μ(univ)` appears with the small exponent `1/q`. -/
theorem lintegral_le_of_isWarm_holder {M : ℝ≥0∞} {μ pi : Measure Om} (h : IsWarm M μ pi)
    {f : Om → ℝ≥0∞} (hf : AEMeasurable f μ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∫⁻ x, f x ∂μ ≤ (M * ∫⁻ x, f x ^ p ∂pi) ^ (1 / p) * (μ Set.univ) ^ (1 / q) := by
  have hp0 : 0 < p := hpq.pos
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one] at hhold
  refine hhold.trans (mul_le_mul_right' ?_ _)
  exact ENNReal.rpow_le_rpow (lintegral_le_of_isWarm h fun x => f x ^ p)
    (by positivity)

/-- **The survival sum at a fractional power.**  If `sⱼ ≤ η + rʲ` then

    `∑_{j<L} sⱼ^β  ≤  L·η^β + (1 − r^β)⁻¹`

for `0 < β ≤ 1`.  This is where the factor `L` is actually removed: at `β = 1/q` with
`q ≈ 2n` the first term is `L·η^{1/(2n)}`, negligible once `η` is exponentially small, and the
second is `O(q)` rather than `O(L)`. -/
theorem sum_rpow_le_of_le_add_pow {s : ℕ → ℝ≥0∞} {L : ℕ} {eta r : ℝ≥0∞} {beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta ≤ 1)
    (hs : ∀ j, j < L → s j ≤ eta + r ^ j) :
    ∑ j ∈ Finset.range L, (s j) ^ beta ≤ (L : ℝ≥0∞) * eta ^ beta + (1 - r ^ beta)⁻¹ := by
  have hstep : ∀ j ∈ Finset.range L, (s j) ^ beta ≤ eta ^ beta + (r ^ beta) ^ j := by
    intro j hj
    have hle : (s j) ^ beta ≤ (eta + r ^ j) ^ beta :=
      ENNReal.rpow_le_rpow (hs j (Finset.mem_range.1 hj)) hb0.le
    refine hle.trans ?_
    have hsub : (eta + r ^ j) ^ beta ≤ eta ^ beta + (r ^ j) ^ beta :=
      ENNReal.rpow_add_le_add_rpow eta (r ^ j) hb0.le hb1
    refine hsub.trans_eq ?_
    congr 1
    rw [← ENNReal.rpow_natCast r j, ← ENNReal.rpow_natCast (r ^ beta) j,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm]
  calc ∑ j ∈ Finset.range L, (s j) ^ beta
      ≤ ∑ j ∈ Finset.range L, (eta ^ beta + (r ^ beta) ^ j) := Finset.sum_le_sum hstep
    _ = (L : ℝ≥0∞) * eta ^ beta + ∑ j ∈ Finset.range L, (r ^ beta) ^ j := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (L : ℝ≥0∞) * eta ^ beta + (1 - r ^ beta)⁻¹ := by
        refine add_le_add le_rfl ?_
        refine le_trans (ENNReal.sum_le_tsum (Finset.range L)) ?_
        exact le_of_eq (ENNReal.tsum_geometric (r ^ beta))

/-- **The lever, abstractly.**  Summing the Hölder warm bound over a rejection loop whose
survival mass decays geometrically:

    `∑_{j<L} ∫ fⱼ dμⱼ  ≤  (M·A)^{1/p} · (L·η^{1/q} + (1 − r^{1/q})⁻¹)`

where `A` bounds every `∫ fⱼ^p dπ`.  Compare `lintegral_le_of_isWarm` summed naively, which
gives `L · M · sup_j ∫ fⱼ dπ`: the factor `L` has been replaced by `L·η^{1/q} + (1 −
r^{1/q})⁻¹`, and the second term is `O(q)` for `r` bounded away from `1`.  The trade is that
`A` is an `L^p(π)` bound rather than an `L^1(π)` bound.

Both `η` and `r` are binders, as they are throughout the retry chain; nothing here assumes
what they are. -/
theorem sum_lintegral_le_of_isWarm_holder
    {M : ℝ≥0∞} {pi : Measure Om} {mu : ℕ → Measure Om} {L : ℕ}
    (hwarm : ∀ j, j < L → IsWarm M (mu j) pi)
    {f : ℕ → Om → ℝ≥0∞} (hf : ∀ j, AEMeasurable (f j) (mu j))
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {A : ℝ≥0∞} (hA : ∀ j, j < L → ∫⁻ x, f j x ^ p ∂pi ≤ A)
    {eta r : ℝ≥0∞} (hs : ∀ j, j < L → mu j Set.univ ≤ eta + r ^ j) :
    ∑ j ∈ Finset.range L, ∫⁻ x, f j x ∂(mu j)
      ≤ (M * A) ^ (1 / p) *
          ((L : ℝ≥0∞) * eta ^ (1 / q) + (1 - r ^ (1 / q))⁻¹) := by
  have hp0 : 0 < p := hpq.pos
  have hqc : q.HolderConjugate p := Real.HolderConjugate.symm hpq
  have hq1 : 1 < q := (Real.holderConjugate_iff.1 hqc).1
  have hq0 : 0 < q := lt_trans one_pos hq1
  have hb0 : 0 < 1 / q := by positivity
  have hb1 : 1 / q ≤ 1 := by
    rw [div_le_one hq0]; linarith
  have hstep : ∀ j ∈ Finset.range L,
      (∫⁻ x, f j x ∂(mu j)) ≤ (M * A) ^ (1 / p) * (mu j Set.univ) ^ (1 / q) := by
    intro j hj
    refine (lintegral_le_of_isWarm_holder (hwarm j (Finset.mem_range.1 hj)) (hf j) hpq).trans ?_
    refine mul_le_mul_right' (ENNReal.rpow_le_rpow ?_ (div_nonneg zero_le_one hp0.le)) _
    exact mul_le_mul_left' (hA j (Finset.mem_range.1 hj)) M
  calc ∑ j ∈ Finset.range L, ∫⁻ x, f j x ∂(mu j)
      ≤ ∑ j ∈ Finset.range L, (M * A) ^ (1 / p) * (mu j Set.univ) ^ (1 / q) :=
        Finset.sum_le_sum hstep
    _ = (M * A) ^ (1 / p) * ∑ j ∈ Finset.range L, (mu j Set.univ) ^ (1 / q) := by
        rw [Finset.mul_sum]
    _ ≤ (M * A) ^ (1 / p) *
          ((L : ℝ≥0∞) * eta ^ (1 / q) + (1 - r ^ (1 / q))⁻¹) :=
        mul_le_mul_left' (sum_rpow_le_of_le_add_pow hb0 hb1 hs) _

/-! ## Jensen and Minkowski, in the form the `L^p(π)` bound needs

To apply `sum_lintegral_le_of_isWarm_holder` one needs an `L^p(π)` bound on each `fⱼ`, and
in a walk `fⱼ` is a sum of kernel iterates of the one-step cost.  These two lemmas reduce
that to the one-step cost's own `L^p(π)` norm. -/

/-- **Jensen for a probability measure**, `(∫w)^p ≤ ∫w^p`.  This is again Hölder against the
constant `1`; `IsWarm.refl` supplies the trivial warmness. -/
theorem rpow_lintegral_le_lintegral_rpow {ν : Measure Om} [IsProbabilityMeasure ν]
    {w : Om → ℝ≥0∞} (hw : AEMeasurable w ν) {p q : ℝ} (hpq : p.HolderConjugate q) :
    (∫⁻ y, w y ∂ν) ^ p ≤ ∫⁻ y, w y ^ p ∂ν := by
  have hp0 : 0 < p := hpq.pos
  have h := lintegral_le_of_isWarm_holder (IsWarm.refl ν) hw hpq
  simp only [one_mul, measure_univ, ENNReal.one_rpow, mul_one] at h
  calc (∫⁻ y, w y ∂ν) ^ p ≤ ((∫⁻ y, w y ^ p ∂ν) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h hp0.le
    _ = ∫⁻ y, w y ^ p ∂ν := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]

/-- **Minkowski for a finite sum.**  `‖∑_{i<t} gᵢ‖_p ≤ ∑_{i<t} ‖gᵢ‖_p`, by induction on
`ENNReal.lintegral_Lp_add_le`. -/
theorem lintegral_rpow_sum_le {ν : Measure Om} {g : ℕ → Om → ℝ≥0∞}
    (hg : ∀ i, AEMeasurable (g i) ν) {p : ℝ} (hp1 : 1 ≤ p) (t : ℕ) :
    (∫⁻ x, (∑ i ∈ Finset.range t, g i x) ^ p ∂ν) ^ (1 / p)
      ≤ ∑ i ∈ Finset.range t, (∫⁻ x, g i x ^ p ∂ν) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  induction t with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      rw [ENNReal.zero_rpow_of_pos hp0, lintegral_zero,
        ENNReal.zero_rpow_of_pos (by positivity)]
  | succ t ih =>
      have hsum : AEMeasurable (∑ i ∈ Finset.range t, g i) ν :=
        Finset.aemeasurable_sum _ fun i _ => hg i
      have hstep := ENNReal.lintegral_Lp_add_le (μ := ν) hsum (hg t) hp1
      have hpt : (∫⁻ x, (∑ i ∈ Finset.range t, g i) x ^ p ∂ν)
          = ∫⁻ x, (∑ i ∈ Finset.range t, g i x) ^ p ∂ν := by
        refine lintegral_congr fun x => ?_
        simp
      calc (∫⁻ x, (∑ i ∈ Finset.range (t + 1), g i x) ^ p ∂ν) ^ (1 / p)
          = (∫⁻ x, ((∑ i ∈ Finset.range t, g i) + g t) x ^ p ∂ν) ^ (1 / p) := by
            congr 1
            refine lintegral_congr fun x => ?_
            congr 1
            simp [Finset.sum_range_succ]
        _ ≤ (∫⁻ x, (∑ i ∈ Finset.range t, g i) x ^ p ∂ν) ^ (1 / p)
              + (∫⁻ x, g t x ^ p ∂ν) ^ (1 / p) := hstep
        _ = (∫⁻ x, (∑ i ∈ Finset.range t, g i x) ^ p ∂ν) ^ (1 / p)
              + (∫⁻ x, g t x ^ p ∂ν) ^ (1 / p) := by rw [hpt]
        _ ≤ (∑ i ∈ Finset.range t, (∫⁻ x, g i x ^ p ∂ν) ^ (1 / p))
              + (∫⁻ x, g t x ^ p ∂ν) ^ (1 / p) := add_le_add ih le_rfl
        _ = ∑ i ∈ Finset.range (t + 1), (∫⁻ x, g i x ^ p ∂ν) ^ (1 / p) :=
            (Finset.sum_range_succ _ _).symm

/-! ## Averaging the `δ_x`-started chain

The `L^p(π)` norm of a `t`-step round mean is controlled by the one-step cost's, but the
round mean is a function *of the starting point*, so the bridge is: averaging the chain
started at `δ_x` over `x ∼ μ` is the chain started at `μ`. -/

/-- `∫ (∫ f d(iterate P δ_x i)) dμ = ∫ f d(iterate P μ i)`. -/
theorem lintegral_lintegral_iterate_dirac {P : Kernel Om Om} [IsMarkovKernel P]
    (i : ℕ) (μ : Measure Om) [IsProbabilityMeasure μ] :
    ∀ {f : Om → ℝ≥0∞}, Measurable f →
      ∫⁻ x, (∫⁻ y, f y ∂(iterate P (Measure.dirac x) i)) ∂μ
        = ∫⁻ y, f y ∂(iterate P μ i) := by
  induction i with
  | zero =>
      intro f hf
      simp only [iterate_zero]
      exact lintegral_congr fun x => lintegral_dirac' x hf
  | succ i ih =>
      intro f hf
      have hg : Measurable fun z => ∫⁻ y, f y ∂(P z) := hf.lintegral_kernel
      have key : ∀ (ν : Measure Om), IsProbabilityMeasure ν →
          ∫⁻ y, f y ∂(iterate P ν (i + 1))
            = ∫⁻ z, (∫⁻ y, f y ∂(P z)) ∂(iterate P ν i) := by
        intro ν _
        show ∫⁻ y, f y ∂(step P (iterate P ν i)) = _
        rw [step]
        exact Measure.lintegral_bind (Kernel.aemeasurable P) hf.aemeasurable
      calc ∫⁻ x, (∫⁻ y, f y ∂(iterate P (Measure.dirac x) (i + 1))) ∂μ
          = ∫⁻ x, (∫⁻ z, (∫⁻ y, f y ∂(P z)) ∂(iterate P (Measure.dirac x) i)) ∂μ :=
            lintegral_congr fun x => key (Measure.dirac x) inferInstance
        _ = ∫⁻ z, (∫⁻ y, f y ∂(P z)) ∂(iterate P μ i) := ih hg
        _ = ∫⁻ y, f y ∂(iterate P μ (i + 1)) := (key μ inferInstance).symm

/-- The `δ_x`-started `i`-step mean is a measurable function of `x`. -/
theorem measurable_lintegral_iterate_dirac {P : Kernel Om Om} [IsMarkovKernel P] (i : ℕ) :
    ∀ {f : Om → ℝ≥0∞}, Measurable f →
      Measurable fun x => ∫⁻ y, f y ∂(iterate P (Measure.dirac x) i) := by
  induction i with
  | zero =>
      intro f hf
      have heq : (fun x => ∫⁻ y, f y ∂(iterate P (Measure.dirac x) 0)) = f := by
        funext x
        simp only [iterate_zero]
        exact lintegral_dirac' x hf
      rw [heq]
      exact hf
  | succ i ih =>
      intro f hf
      have hg : Measurable fun z => ∫⁻ y, f y ∂(P z) := hf.lintegral_kernel
      have heq : (fun x => ∫⁻ y, f y ∂(iterate P (Measure.dirac x) (i + 1)))
          = fun x => ∫⁻ z, (∫⁻ y, f y ∂(P z)) ∂(iterate P (Measure.dirac x) i) := by
        funext x
        rw [iterate_succ, step]
        exact Measure.lintegral_bind (Kernel.aemeasurable P) hf.aemeasurable
      rw [heq]
      exact ih hg

/-- **The `L^p(π)` norm of a `t`-step round mean.**  If the round mean started at `x` is the
sum of the `δ_x`-started kernel iterates of a one-step cost `w`, then its `L^p(π)` norm is at
most `t · ‖w‖_{L^p(π)}` — Minkowski over the `t` steps, then Jensen and invariance for each.

This is the step that turns the one-step bound `LocalConductanceMoment` supplies into the
`L^p(π)` hypothesis that `sum_lintegral_le_of_isWarm_holder` consumes. -/
theorem lintegral_rpow_roundMean_le
    {P : Kernel Om Om} [IsMarkovKernel P] {pi : Measure Om} [IsProbabilityMeasure pi]
    (hinv : Kernel.Invariant P pi) {w : Om → ℝ≥0∞} (hw : Measurable w)
    {p q : ℝ} (hpq : p.HolderConjugate q) (t : ℕ) :
    (∫⁻ x, (∑ i ∈ Finset.range t,
        ∫⁻ y, w y ∂(iterate P (Measure.dirac x) i)) ^ p ∂pi) ^ (1 / p)
      ≤ (t : ℝ≥0∞) * (∫⁻ y, w y ^ p ∂pi) ^ (1 / p) := by
  have hp0 : 0 < p := hpq.pos
  have hp1 : 1 ≤ p := (Real.holderConjugate_iff.1 hpq).1.le
  have hmeas : ∀ i : ℕ, AEMeasurable
      (fun x => ∫⁻ y, w y ∂(iterate P (Measure.dirac x) i)) pi :=
    fun i => (measurable_lintegral_iterate_dirac i hw).aemeasurable
  have hstep : ∀ i : ℕ,
      (∫⁻ x, (∫⁻ y, w y ∂(iterate P (Measure.dirac x) i)) ^ p ∂pi) ^ (1 / p)
        ≤ (∫⁻ y, w y ^ p ∂pi) ^ (1 / p) := by
    intro i
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    calc ∫⁻ x, (∫⁻ y, w y ∂(iterate P (Measure.dirac x) i)) ^ p ∂pi
        ≤ ∫⁻ x, (∫⁻ y, w y ^ p ∂(iterate P (Measure.dirac x) i)) ∂pi :=
          lintegral_mono fun x =>
            rpow_lintegral_le_lintegral_rpow (ν := iterate P (Measure.dirac x) i)
              hw.aemeasurable hpq
      _ = ∫⁻ y, w y ^ p ∂(iterate P pi i) :=
          lintegral_lintegral_iterate_dirac i pi (hw.pow_const p)
      _ = ∫⁻ y, w y ^ p ∂pi := by rw [iterate_invariant hinv i]
  calc (∫⁻ x, (∑ i ∈ Finset.range t,
          ∫⁻ y, w y ∂(iterate P (Measure.dirac x) i)) ^ p ∂pi) ^ (1 / p)
      ≤ ∑ i ∈ Finset.range t,
          (∫⁻ x, (∫⁻ y, w y ∂(iterate P (Measure.dirac x) i)) ^ p ∂pi) ^ (1 / p) :=
        lintegral_rpow_sum_le hmeas hp1 t
    _ ≤ ∑ _i ∈ Finset.range t, (∫⁻ y, w y ^ p ∂pi) ^ (1 / p) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (t : ℝ≥0∞) * (∫⁻ y, w y ^ p ∂pi) ^ (1 / p) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The lever, at a retry loop over a walk.**  Combining the three pieces: each round's
mean is `t` kernel iterates of the one-step cost `w`; its `L^p(π)` norm is `t·‖w‖_p`; and
Hölder against the warm density turns the sum over rounds into `L·η^{1/q} + (1 − r^{1/q})⁻¹`
instead of `L`.

    `∑_{j<L} ∫ (∑_{i<stepsⱼ} P^i w) dμⱼ  ≤  (M·(t^p·A))^{1/p} · (L·η^{1/q} + (1 − r^{1/q})⁻¹)`

for any per-round deadlines `stepsⱼ ≤ t`, which is the shape the retry chain actually has —
`retrySteps i j` varies with the round.

The naive bound, `lintegral_le_of_isWarm` summed, gives `L·M·t·∫w dπ`.  The gain is the
factor `L`; the price is that `A` bounds `∫w^p dπ` rather than `∫w dπ`. -/
theorem sum_lintegral_roundMean_le_holder
    {P : Kernel Om Om} [IsMarkovKernel P] {pi : Measure Om} [IsProbabilityMeasure pi]
    (hinv : Kernel.Invariant P pi) {w : Om → ℝ≥0∞} (hw : Measurable w)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {A : ℝ≥0∞} (hA : ∫⁻ y, w y ^ p ∂pi ≤ A)
    {M : ℝ≥0∞} {mu : ℕ → Measure Om} {L : ℕ} (hwarm : ∀ j, j < L → IsWarm M (mu j) pi)
    {eta r : ℝ≥0∞} (hs : ∀ j, j < L → mu j Set.univ ≤ eta + r ^ j)
    {steps : ℕ → ℕ} {t : ℕ} (hsteps : ∀ j, j < L → steps j ≤ t) :
    ∑ j ∈ Finset.range L,
        ∫⁻ x, (∑ i ∈ Finset.range (steps j),
          ∫⁻ y, w y ∂(iterate P (Measure.dirac x) i)) ∂(mu j)
      ≤ (M * ((t : ℝ≥0∞) ^ p * A)) ^ (1 / p) *
          ((L : ℝ≥0∞) * eta ^ (1 / q) + (1 - r ^ (1 / q))⁻¹) := by
  have hp0 : 0 < p := hpq.pos
  have hmeas : ∀ m : ℕ, Measurable fun x : Om =>
      ∑ i ∈ Finset.range m, ∫⁻ y, w y ∂(iterate P (Measure.dirac x) i) :=
    fun m => Finset.measurable_sum _ fun i _ => measurable_lintegral_iterate_dirac i hw
  have hAt : ∫⁻ x, (∑ i ∈ Finset.range t,
      ∫⁻ y, w y ∂(iterate P (Measure.dirac x) i)) ^ p ∂pi ≤ (t : ℝ≥0∞) ^ p * A := by
    have h := lintegral_rpow_roundMean_le hinv hw hpq t
    have hraise := ENNReal.rpow_le_rpow h hp0.le
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
      inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at hraise
    refine hraise.trans ?_
    exact mul_le_mul_left' hA _
  -- each round's mean is majorised by the `t`-step mean, so one `A` serves every round
  have hAj : ∀ j, j < L → ∫⁻ x, (∑ i ∈ Finset.range (steps j),
      ∫⁻ y, w y ∂(iterate P (Measure.dirac x) i)) ^ p ∂pi ≤ (t : ℝ≥0∞) ^ p * A := by
    intro j hj
    refine le_trans (lintegral_mono fun x => ?_) hAt
    refine ENNReal.rpow_le_rpow ?_ hp0.le
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (hsteps j hj))
  exact sum_lintegral_le_of_isWarm_holder hwarm (fun j => (hmeas (steps j)).aemeasurable) hpq
    hAj hs

/-! ### Axiom audit -/

section AxiomCheck

#print axioms lintegral_le_of_isWarm_holder
#print axioms sum_rpow_le_of_le_add_pow
#print axioms sum_lintegral_le_of_isWarm_holder
#print axioms rpow_lintegral_le_lintegral_rpow
#print axioms lintegral_rpow_sum_le
#print axioms lintegral_lintegral_iterate_dirac
#print axioms measurable_lintegral_iterate_dirac
#print axioms lintegral_rpow_roundMean_le
#print axioms sum_lintegral_roundMean_le_holder

end AxiomCheck

end Arlib.MarkovChains
