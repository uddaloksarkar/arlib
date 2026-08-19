/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Order.Interval.Set.Basic

/-!
# Product estimators, truncation, and the median boost

Generic estimator theory: the ingredients a "run the estimator many times and
aggregate" argument needs, stated for an arbitrary probability space and an
arbitrary family of scores. Nothing here mentions convex bodies, volumes, or
Markov chains.

## Contents

### Truncation

* `sub_min_le_sq_div` — the pointwise core `x - min x a ≤ x ^ 2 / (4 * a)`.
* `expect_min_ge` — its integral form: truncating a random variable at `a`
  costs at most `E(X ^ 2) / (4 * a)` in expectation.

### A quantitative dependence measure

* `NuIndep` — `|P(X ∈ A, Y ∈ B) - P(X ∈ A) P(Y ∈ B)| ≤ ν` for all measurable
  `A`, `B`.
* `NuIndep.comp` — measurable functions cannot decrease independence.

### The product estimator

* `integral_prod_eq_prod_integral'` — `E(∏ W i) = ∏ E(W i)` for an independent
  family.
* `integral_prod_sq` — `E((∏ W i) ^ 2) = ∏ E(W i ^ 2)`.
* `prod_sq_div_le` — if each factor's second-moment ratio obeys
  `E(W i ^ 2) ≤ c * E(W i) ^ 2` then `E((∏ W i) ^ 2) ≤ c ^ m * E(∏ W i) ^ 2`.
* `prod_sq_div_le_exp` — the packaged form: per-factor ratio `1 + c / m` over
  `m` factors gives a global ratio at most `exp c`, so the relative variance of
  the product is `O(1)` uniformly in `m`.

### The median boost

* `IsMedian` — what it means for `z` to be a median of a finite family.
* `median_mem_of_majority` — the deterministic half: if strictly more than half
  the runs land in an interval, every median lands in it.
* `majority_tail_le` — the probabilistic half at the Chebyshev rate, needing
  only *pairwise* independence: failure `≤ 1 / (4 r (q - 1/2) ^ 2)`.
* `hoeffding_sum_le` — Hoeffding's inequality (lower tail) in per-coordinate
  form, packaged from Mathlib's sub-Gaussian machinery.
* `majority_tail_le_exp` — the probabilistic half at the *exponential* rate,
  needing full independence: failure `≤ exp (-2 r (q - 1/2) ^ 2)`.
* `majority_repetitions_suffice` — hence `r ≥ log (1/p) / (2 (q - 1/2) ^ 2)`
  repetitions drive the failure probability below `p`: the `O(log (1/p))`
  repetition count. `majority_repetitions_suffice'` is the `ℝ≥0∞` restatement.
* `median_boost` — the two halves combined: the median of `r` independent runs,
  each correct with probability `q > 1/2`, is correct with probability `1 - p`
  once `r ≥ log (1/p) / (2 (q - 1/2) ^ 2)`.

The exponential rate is a genuine improvement on a Chebyshev-only development:
Mathlib supplies Hoeffding's lemma for bounded variables
(`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) and
Hoeffding's inequality for sums of independent sub-Gaussian variables
(`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`), so the
`O(log (1/p))` repetition count claimed in the literature is available and is
what `majority_repetitions_suffice` proves. `majority_tail_le` keeps the
Chebyshev argument for the case where only pairwise independence is available.

## References

The truncation lemma and the dependence measure are, respectively, `lem:exp-bd`
and `lem:fn-indep` of Cousins–Vempala, *Gaussian cooling and `O*(n³)` algorithms
for volume and Gaussian volume*; the median boost is the amplification step of
that paper's §5.2. All statements here are proved, not assumed.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Set Real ProbabilityTheory
open scoped NNReal ENNReal

/-! ## The cost of truncation -/

/-- **The pointwise core of the truncation bound.** For `0 < a`,

  `x - min x a ≤ x ^ 2 / (4 * a)`.

Above the truncation point this is `4 a (x - a) ≤ x ^ 2`, i.e. `0 ≤ (x - 2a) ^ 2`;
below it the left-hand side is `0`. Nonnegativity of `x` is not needed: for
`x < 0` the left-hand side vanishes as well. -/
lemma sub_min_le_sq_div {x a : ℝ} (ha : 0 < a) :
    x - min x a ≤ x ^ 2 / (4 * a) := by
  rcases le_total x a with h | h
  · rw [min_eq_left h]
    have : (0 : ℝ) ≤ x ^ 2 / (4 * a) := by positivity
    linarith
  · rw [min_eq_right h, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * a)]
    nlinarith [sq_nonneg (x - 2 * a)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The truncation bound.** For `X ≥ 0` and `a > 0`, writing `X' = min X a`,

  `E(X') ≥ E(X) - E(X ^ 2) / (4 * a)`.

The integral form of `sub_min_le_sq_div`. Integrability of the truncation is
automatic: it is sandwiched between `0` and `X`. -/
theorem expect_min_ge {X : Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (hX0 : ∀ ω, 0 ≤ X ω) (hXm : Measurable X)
    (hX : Integrable X μ) (hX2 : Integrable (fun ω => (X ω) ^ 2) μ) :
    (∫ ω, X ω ∂μ) - (∫ ω, (X ω) ^ 2 ∂μ) / (4 * a) ≤ ∫ ω, min (X ω) a ∂μ := by
  have hmin_int : Integrable (fun ω => min (X ω) a) μ := by
    refine Integrable.mono' hX ((hXm.min measurable_const).aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hX0 ω) ha.le)]
    exact min_le_left _ _
  have hdiff_int : Integrable (fun ω => X ω - min (X ω) a) μ := hX.sub hmin_int
  have hsq_int : Integrable (fun ω => (X ω) ^ 2 / (4 * a)) μ := hX2.div_const _
  have hptwise : ∀ ω, X ω - min (X ω) a ≤ (X ω) ^ 2 / (4 * a) :=
    fun _ => sub_min_le_sq_div ha
  have hint := integral_mono hdiff_int hsq_int hptwise
  rw [integral_sub hX hmin_int, integral_div] at hint
  linarith

/-! ## A quantitative dependence measure -/

/-- **`ν`-independence.** Every pair of measurable events pulled back through
`X` and `Y` decorrelates to within `ν`:

  `|P(X ∈ A, Y ∈ B) - P(X ∈ A) * P(Y ∈ B)| ≤ ν`.

Stated as a universally quantified bound rather than as `sup … ≤ ν`; the two are
equivalent, and this form avoids the supremum's existence side conditions. -/
def NuIndep {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (ν : ℝ) : Prop :=
  ∀ A : Set α, ∀ B : Set β, MeasurableSet A → MeasurableSet B →
    |μ.real (X ⁻¹' A ∩ Y ⁻¹' B) - μ.real (X ⁻¹' A) * μ.real (Y ⁻¹' B)| ≤ ν

/-- **Measurable functions cannot decrease independence:**
`ν`-independence of `X` and `Y` implies `ν`-independence of `f ∘ X` and `g ∘ Y`.

A preimage under `f ∘ X` is a preimage under `X` of a measurable set, so the
family of pairs quantified over on the left is a subfamily of the one on the
right; there is nothing else to it. -/
theorem NuIndep.comp {α β α' β' : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace α'] [MeasurableSpace β'] {X : Ω → α} {Y : Ω → β} {ν : ℝ}
    {f : α → α'} {g : β → β'} (h : NuIndep μ X Y ν)
    (hf : Measurable f) (hg : Measurable g) :
    NuIndep μ (fun ω => f (X ω)) (fun ω => g (Y ω)) ν := fun A B hA hB =>
  h (f ⁻¹' A) (g ⁻¹' B) (hf hA) (hg hB)

/-! ## The product estimator

The estimator of interest is a product `W 1 * … * W m` of independent factors,
each of which is itself an estimate of one link in a telescoping chain. Its two
relevant moments both factor, so a per-factor control of the *relative* second
moment `E(W i ^ 2) / E(W i) ^ 2` controls the relative second moment of the
whole product. -/

section Product

variable {ι : Type*} [Fintype ι] {W : ι → Ω → ℝ}

/-- **The expectation of the product estimator.** For an independent family,
`E(∏ i, W i) = ∏ i, E(W i)`.

A repackaging of `ProbabilityTheory.iIndepFun.integral_fun_prod_eq_prod_integral`
in the pointwise `∫ ω, ∏ i, W i ω` form the estimator is written in. -/
theorem integral_prod_eq_prod_integral' (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ) :
    ∫ ω, ∏ i, W i ω ∂μ = ∏ i, ∫ ω, W i ω ∂μ :=
  hindep.integral_fun_prod_eq_prod_integral hmeas

/-- **The second moment of the product estimator.** For an independent family,
`E((∏ i, W i) ^ 2) = ∏ i, E(W i ^ 2)`.

Squaring is measurable, so the squared factors are independent too; the square
of a product is the product of the squares. -/
theorem integral_prod_sq (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ) :
    ∫ ω, (∏ i, W i ω) ^ 2 ∂μ = ∏ i, ∫ ω, (W i ω) ^ 2 ∂μ := by
  have hsqindep : iIndepFun (fun i ω => (W i ω) ^ 2) μ := by
    have := hindep.comp (fun _ (x : ℝ) => x ^ 2) (fun _ => measurable_id.pow_const 2)
    exact this
  have hsqmeas : ∀ i, AEStronglyMeasurable (fun ω => (W i ω) ^ 2) μ :=
    fun i => (continuous_pow 2).comp_aestronglyMeasurable (hmeas i)
  calc ∫ ω, (∏ i, W i ω) ^ 2 ∂μ = ∫ ω, ∏ i, (W i ω) ^ 2 ∂μ := by
        simp_rw [Finset.prod_pow]
    _ = ∏ i, ∫ ω, (W i ω) ^ 2 ∂μ :=
        hsqindep.integral_fun_prod_eq_prod_integral hsqmeas

/-- **A per-factor relative second moment bounds the product's.** If every factor
satisfies `E(W i ^ 2) ≤ c * E(W i) ^ 2`, then

  `E((∏ i, W i) ^ 2) ≤ c ^ card ι * E(∏ i, W i) ^ 2`.

Both sides factor by `integral_prod_sq` and `integral_prod_eq_prod_integral'`,
after which this is `Finset.prod_le_prod`. -/
theorem prod_sq_div_le {c : ℝ} (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (hc : ∀ i, ∫ ω, (W i ω) ^ 2 ∂μ ≤ c * (∫ ω, W i ω ∂μ) ^ 2) :
    ∫ ω, (∏ i, W i ω) ^ 2 ∂μ
      ≤ c ^ Fintype.card ι * (∫ ω, ∏ i, W i ω ∂μ) ^ 2 := by
  rw [integral_prod_sq hindep hmeas, integral_prod_eq_prod_integral' hindep hmeas]
  calc ∏ i, ∫ ω, (W i ω) ^ 2 ∂μ
      ≤ ∏ i, c * (∫ ω, W i ω ∂μ) ^ 2 :=
        Finset.prod_le_prod
          (fun i _ => integral_nonneg fun ω => sq_nonneg (W i ω))
          (fun i _ => hc i)
    _ = c ^ Fintype.card ι * (∏ i, ∫ ω, W i ω ∂μ) ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]

/-- **The product estimator has `O(1)` relative variance.** If each of the
`m = card ι` factors satisfies `E(W i ^ 2) ≤ (1 + κ / m) * E(W i) ^ 2` for some
`κ ≥ 0`, then

  `E((∏ i, W i) ^ 2) ≤ exp κ * E(∏ i, W i) ^ 2`,

uniformly in `m`. This is the shape a telescoping-product estimator is designed
to have: a per-phase relative variance of `1 + O(1/m)` costs only a constant
factor overall, because `(1 + κ/m) ^ m ≤ exp κ`. -/
theorem prod_sq_div_le_exp {κ : ℝ} (hκ : 0 ≤ κ) (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (hc : ∀ i, ∫ ω, (W i ω) ^ 2 ∂μ
      ≤ (1 + κ / Fintype.card ι) * (∫ ω, W i ω ∂μ) ^ 2) :
    ∫ ω, (∏ i, W i ω) ^ 2 ∂μ ≤ Real.exp κ * (∫ ω, ∏ i, W i ω ∂μ) ^ 2 := by
  set m : ℕ := Fintype.card ι with hm
  have hbase : (0 : ℝ) ≤ 1 + κ / m := by positivity
  have hpow : (1 + κ / m) ^ m ≤ Real.exp κ := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero]
      simpa using Real.exp_le_exp.mpr hκ
    · have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.ne'
      have hstep : (1 + κ / m) ^ m ≤ (Real.exp (κ / m)) ^ m :=
        pow_le_pow_left₀ hbase
          (by linarith [Real.add_one_le_exp (κ / (m : ℝ))]) m
      refine hstep.trans_eq ?_
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
  refine (prod_sq_div_le hindep hmeas hc).trans ?_
  exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)

end Product

/-! ## The median boost

An estimator that is correct with some fixed probability `q > 1/2` is turned into
one that is correct with probability `1 - p` by running it `r` times
independently and returning the median. The argument has two halves: a
deterministic one (a majority inside an interval forces every median into that
interval) and a probabilistic one (a majority is likely).

Note the direction of the hypothesis. `q > 1/2` is all the deterministic half
needs; the paper's `4/5` is a convenient concrete value, and the statements below
are deliberately left at the general `q`. -/

/-- **What it means for `z` to be a median** of a finite family `v : Fin r → ℝ`:
at least half the family lies weakly below `z`, and at least half lies weakly
above.

Characterizing medians rather than constructing one keeps the result applicable
to whatever tie-breaking an implementation uses: *every* median satisfies the
conclusion of `median_mem_of_majority`. -/
def IsMedian {r : ℕ} (v : Fin r → ℝ) (z : ℝ) : Prop :=
  r ≤ 2 * (Finset.univ.filter fun i => v i ≤ z).card ∧
  r ≤ 2 * (Finset.univ.filter fun i => z ≤ v i).card

/-- **The deterministic half of the median boost.** If strictly more than half of
the runs land in the target interval `Icc L U`, then *every* median of the runs
lands in `Icc L U`.

This is why the median is the right aggregator: the good set is an interval, and
an interval containing a majority must contain the middle. Proof: were `z < L`,
every good run would satisfy `z < v i`, so the good runs and the runs weakly
below `z` would be disjoint; `IsMedian` forces at least `r/2` of the latter,
leaving at most `r/2` of the former, contradicting the strict majority.
Symmetrically for `U < z`. -/
theorem median_mem_of_majority {r : ℕ} {v : Fin r → ℝ} {z L U : ℝ}
    (hz : IsMedian v z)
    (hmaj : r < 2 * (Finset.univ.filter fun i => v i ∈ Icc L U).card) :
    z ∈ Icc L U := by
  classical
  obtain ⟨hzlo, hzhi⟩ := hz
  set G : Finset (Fin r) := Finset.univ.filter fun i => v i ∈ Icc L U with hG
  constructor
  · -- `L ≤ z`
    by_contra hcon
    replace hlt : z < L := not_le.mp hcon
    set S : Finset (Fin r) := Finset.univ.filter fun i => v i ≤ z with hS
    have hdisj : Disjoint G S := by
      rw [Finset.disjoint_left]
      intro i hiG hiS
      rw [hG, Finset.mem_filter] at hiG
      rw [hS, Finset.mem_filter] at hiS
      exact absurd (hiG.2.1.trans hiS.2) (not_le.mpr hlt)
    have hcard : G.card + S.card ≤ r := by
      have := Finset.card_le_card (Finset.subset_univ (G ∪ S))
      rwa [Finset.card_union_of_disjoint hdisj, Finset.card_univ,
        Fintype.card_fin] at this
    omega
  · -- `z ≤ U`
    by_contra hcon
    replace hlt : U < z := not_le.mp hcon
    set S : Finset (Fin r) := Finset.univ.filter fun i => z ≤ v i with hS
    have hdisj : Disjoint G S := by
      rw [Finset.disjoint_left]
      intro i hiG hiS
      rw [hG, Finset.mem_filter] at hiG
      rw [hS, Finset.mem_filter] at hiS
      exact absurd (hiS.2.trans hiG.2.2) (not_le.mpr hlt)
    have hcard : G.card + S.card ≤ r := by
      have := Finset.card_le_card (Finset.subset_univ (G ∪ S))
      rwa [Finset.card_union_of_disjoint hdisj, Finset.card_univ,
        Fintype.card_fin] at this
    omega

/-! ### The probabilistic half, at the Chebyshev rate

The repetitions are independent, so the number of successes concentrates. The
bound below uses only *pairwise* independence and only `AEMeasurable` scores, at
the cost of a polynomial rather than exponential rate. -/

/-- **A majority of pairwise-independent runs succeeds, with high probability.**

For `r` pairwise-independent `[0,1]`-valued scores each of mean at least
`q > 1/2`, the chance that the total falls to `r/2` or below is at most
`1 / (4 r (q - 1/2) ^ 2)`.

Applied with `ξ i` the indicator of "run `i` succeeded", `∑ ξ i` counts the
successful runs, so together with `median_mem_of_majority` this is the median
boost: failure probability `≤ p` once `r ≥ 1 / (4 p (q - 1/2) ^ 2)`.

This is the *Chebyshev* rate, `O(1/p)` repetitions. It is superseded by
`majority_tail_le_exp`, which costs only `O(log (1/p))` repetitions but demands
full independence; this version is retained because its hypotheses are strictly
weaker. -/
theorem majority_tail_le [IsProbabilityMeasure μ] {r : ℕ} (hr : 0 < r)
    {ξ : Fin r → Ω → ℝ} {q : ℝ}
    (hb : ∀ i, ∀ᵐ ω ∂μ, ξ i ω ∈ Icc (0 : ℝ) 1)
    (hm : ∀ i, AEMeasurable (ξ i) μ)
    (hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin r)))
      fun i j => IndepFun (ξ i) (ξ j) μ)
    (hq : ∀ i, q ≤ ∫ ω, ξ i ω ∂μ) (hq2 : 1 / 2 < q) :
    μ {ω | ∑ i, ξ i ω ≤ (r : ℝ) / 2}
      ≤ ENNReal.ofReal (1 / (4 * r * (q - 1 / 2) ^ 2)) := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqh : (0 : ℝ) < q - 1 / 2 := by linarith
  set c : ℝ := r * (q - 1 / 2) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hLp : ∀ i, MemLp (ξ i) 2 μ :=
    fun i => memLp_of_bounded (hb i) (hm i).aestronglyMeasurable 2
  set S : Ω → ℝ := ∑ i, ξ i with hSdef
  have hSapp : ∀ ω, S ω = ∑ i, ξ i ω := by
    intro ω; rw [hSdef]; exact Finset.sum_apply ω Finset.univ ξ
  have hSLp : MemLp S 2 μ := memLp_finsetSum' _ (fun i _ => hLp i)
  -- variance: additive by pairwise independence, each term at most `1/4`
  have hvi : ∀ i, variance (ξ i) μ ≤ 1 / 4 := by
    intro i
    have h := variance_le_sq_of_bounded (hb i) (hm i)
    norm_num at h
    exact h
  have hvarle : variance S μ ≤ (r : ℝ) / 4 := by
    rw [hSdef, IndepFun.variance_sum (fun i _ => hLp i) hpair]
    calc ∑ i : Fin r, variance (ξ i) μ ≤ ∑ _i : Fin r, (1 / 4 : ℝ) :=
          Finset.sum_le_sum fun i _ => hvi i
      _ = (r : ℝ) / 4 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- mean: at least `q * r`
  have hmean : q * r ≤ ∫ ω, S ω ∂μ := by
    have hint : ∀ i, Integrable (ξ i) μ := fun i => (hLp i).integrable one_le_two
    have hswap : ∫ ω, S ω ∂μ = ∑ i, ∫ ω, ξ i ω ∂μ := by
      simp_rw [hSapp]
      exact integral_finsetSum _ fun i _ => hint i
    rw [hswap]
    calc q * r = ∑ _i : Fin r, q := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ ∑ i, ∫ ω, ξ i ω ∂μ := Finset.sum_le_sum fun i _ => hq i
  -- the low-count event sits inside a Chebyshev deviation event
  have hsub : {ω | ∑ i, ξ i ω ≤ (r : ℝ) / 2}
      ⊆ {ω | c ≤ |S ω - ∫ ω, S ω ∂μ|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [← hSapp ω] at hω
    have hd : c ≤ (∫ ω, S ω ∂μ) - S ω := by rw [hc]; nlinarith
    rw [abs_sub_comm]
    exact le_trans hd (le_abs_self _)
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (meas_ge_le_variance_div_sq hSLp hcpos) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hc2 : c ^ 2 = (r : ℝ) ^ 2 * (q - 1 / 2) ^ 2 := by rw [hc]; ring
  rw [hc2]
  nlinarith [hvarle, hrR, sq_nonneg (q - 1 / 2)]

/-! ### The probabilistic half, at the exponential rate

Mathlib's sub-Gaussian machinery (`ProbabilityTheory.HasSubgaussianMGF`) supplies
Hoeffding's lemma for bounded variables and Hoeffding's inequality for sums of
independent sub-Gaussian variables. That is exactly the ingredient the Chebyshev
argument above lacks, and it upgrades the repetition count from `O(1/p)` to
`O(log (1/p))`. -/

/-- **Hoeffding's inequality (lower tail), in per-coordinate form.** For a fully
independent family with `a i ≤ X i ≤ b i` almost surely, and `t ≥ 0`,

  `P(∑ i, X i ≤ ∑ i, E(X i) - t) ≤ exp (-2 t ^ 2 / ∑ i, (b i - a i) ^ 2)`.

Obtained from `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` applied to the
centred negations `E(X i) - X i`, each sub-Gaussian with parameter
`(b i - a i) ^ 2 / 4` by Hoeffding's lemma.

Full independence is genuinely needed here: the moment generating function
factorizes only for independent families, unlike the variance, which is additive
under mere pairwise independence.

The degenerate case `∑ (b i - a i) ^ 2 = 0` is included: both sides are then `1`
under Mathlib's `x / 0 = 0` convention. -/
theorem hoeffding_sum_le [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ} {a b : ι → ℝ} (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hab : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc (a i) (b i))
    (hindep : iIndepFun X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ i, X i ω ≤ (∑ i, ∫ ω, X i ω ∂μ) - t}
      ≤ Real.exp (-2 * t ^ 2 / ∑ i, (b i - a i) ^ 2) := by
  classical
  set m : ι → ℝ := fun i => ∫ ω, X i ω ∂μ with hm
  have hint : ∀ i, Integrable (X i) μ :=
    fun i => Integrable.of_mem_Icc _ _ (hmeas i) (hab i)
  set Y : ι → Ω → ℝ := fun i ω => m i - X i ω with hY
  have hYindep : iIndepFun Y μ :=
    hindep.comp (fun i (x : ℝ) => m i - x) fun _ => measurable_const.sub measurable_id
  have hYmeas : ∀ i, AEMeasurable (Y i) μ :=
    fun i => aemeasurable_const.sub (hmeas i)
  have hYab : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Icc (m i - b i) (m i - a i) := by
    intro i
    filter_upwards [hab i] with ω hω
    have h1 := hω.1
    have h2 := hω.2
    simp only [hY, mem_Icc]
    constructor <;> linarith
  have hY0 : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    simp only [hY]
    rw [integral_sub (integrable_const _) (hint i), integral_const]
    simp [hm]
  set c : ι → ℝ≥0 := fun i => (‖(m i - a i) - (m i - b i)‖₊ / 2) ^ 2 with hc
  have hsubG : ∀ i, HasSubgaussianMGF (Y i) (c i) μ := fun i =>
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hYmeas i) (hYab i) (hY0 i)
  have hkey := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYindep
    (s := (Finset.univ : Finset ι)) (fun i _ => hsubG i) ht
  -- the event, rewritten
  have hset : {ω | t ≤ ∑ i, Y i ω}
      = {ω | ∑ i, X i ω ≤ (∑ i, ∫ ω, X i ω ∂μ) - t} := by
    ext ω
    simp only [Set.mem_setOf_eq, hY, Finset.sum_sub_distrib, ← hm]
    constructor <;> intro h <;> linarith
  rw [hset] at hkey
  refine hkey.trans (Real.exp_le_exp.mpr ?_)
  -- the variance-proxy sum is a quarter of the total squared range
  have hcoe : ∀ i, ((c i : ℝ≥0) : ℝ) = (b i - a i) ^ 2 / 4 := by
    intro i
    have hx : (m i - a i) - (m i - b i) = b i - a i := by ring
    simp only [hc, hx]
    push_cast
    rw [div_pow, Real.norm_eq_abs, sq_abs]
    norm_num
  have hcsum : ((∑ i, c i : ℝ≥0) : ℝ) = (∑ i, (b i - a i) ^ 2) / 4 := by
    rw [NNReal.coe_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => hcoe i
  rw [hcsum]
  set V : ℝ := ∑ i, (b i - a i) ^ 2 with hV
  rcases eq_or_ne V 0 with h0 | h0
  · simp [h0]
  · have heq : -t ^ 2 / (2 * (V / 4)) = -2 * t ^ 2 / V := by
      field_simp
      ring
    exact le_of_eq heq

/-- **A majority of fully independent runs succeeds, with exponentially small
failure probability.**

For `r` fully independent `[0,1]`-valued scores each of mean at least `q > 1/2`,

  `P(∑ i, ξ i ≤ r/2) ≤ exp (-2 r (q - 1/2) ^ 2)`.

This supersedes `majority_tail_le`, which proves the same tail only at the
Chebyshev rate `1 / (4 r (q - 1/2) ^ 2)`. The hypothesis is strictly stronger —
`iIndepFun` rather than pairwise `IndepFun` — and unavoidably so: the moment
generating function factorizes only under full independence. In the intended
application the `r` runs are independent repetitions of the same algorithm on
fresh randomness, so `iIndepFun` holds on the nose. -/
theorem majority_tail_le_exp [IsProbabilityMeasure μ] {r : ℕ} (hr : 0 < r)
    {ξ : Fin r → Ω → ℝ} {q : ℝ}
    (hb : ∀ i, ∀ᵐ ω ∂μ, ξ i ω ∈ Icc (0 : ℝ) 1)
    (hmeas : ∀ i, AEMeasurable (ξ i) μ)
    (hindep : iIndepFun ξ μ)
    (hq : ∀ i, q ≤ ∫ ω, ξ i ω ∂μ) (hq2 : 1 / 2 < q) :
    μ.real {ω | ∑ i, ξ i ω ≤ (r : ℝ) / 2}
      ≤ Real.exp (-2 * r * (q - 1 / 2) ^ 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqh : (0 : ℝ) < q - 1 / 2 := by linarith
  set mX : ℝ := ∑ i, ∫ ω, ξ i ω ∂μ with hmX
  have hmXge : q * r ≤ mX := by
    rw [hmX]
    calc q * r = ∑ _i : Fin r, q := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ∑ i, ∫ ω, ξ i ω ∂μ := Finset.sum_le_sum fun i _ => hq i
  set t : ℝ := mX - (r : ℝ) / 2 with ht
  have htge : (r : ℝ) * (q - 1 / 2) ≤ t := by rw [ht]; nlinarith
  have ht0 : (0 : ℝ) ≤ t := le_trans (by positivity) htge
  have hV : (∑ _i : Fin r, ((1 : ℝ) - 0) ^ 2) = (r : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hmain := hoeffding_sum_le (μ := μ) (X := ξ) (a := fun _ => (0 : ℝ))
    (b := fun _ => (1 : ℝ)) hmeas hb hindep ht0
  rw [hV] at hmain
  have hset : {ω | ∑ i, ξ i ω ≤ (r : ℝ) / 2}
      = {ω | ∑ i, ξ i ω ≤ (∑ i, ∫ ω, ξ i ω ∂μ) - t} := by
    rw [ht, ← hmX]; ext ω; simp
  rw [hset]
  refine hmain.trans (Real.exp_le_exp.mpr ?_)
  rw [div_le_iff₀ hrR]
  nlinarith [htge, sq_nonneg (q - 1 / 2), mul_pos hrR hqh]

/-- **The repetition count of the median boost is `O(log (1/p))`.** With `r`
fully independent `[0,1]`-valued runs of mean at least `q > 1/2`, taking

  `r ≥ log (1/p) / (2 (q - 1/2) ^ 2)`

makes the chance of failing to obtain a strict majority at most `p`.

Combined with `median_mem_of_majority` — apply it with `ξ i` the indicator of
"run `i` landed in the target interval" — this is the median boost in full: the
median of `r` independent repetitions of an estimator that is correct with
probability `q > 1/2` is correct with probability at least `1 - p`, at a cost of
`O(log (1/p))` repetitions. -/
theorem majority_repetitions_suffice [IsProbabilityMeasure μ] {r : ℕ} (hr : 0 < r)
    {ξ : Fin r → Ω → ℝ} {q p : ℝ}
    (hb : ∀ i, ∀ᵐ ω ∂μ, ξ i ω ∈ Icc (0 : ℝ) 1)
    (hmeas : ∀ i, AEMeasurable (ξ i) μ)
    (hindep : iIndepFun ξ μ)
    (hq : ∀ i, q ≤ ∫ ω, ξ i ω ∂μ) (hq2 : 1 / 2 < q)
    (hp : 0 < p) (hrp : Real.log (1 / p) / (2 * (q - 1 / 2) ^ 2) ≤ (r : ℝ)) :
    μ.real {ω | ∑ i, ξ i ω ≤ (r : ℝ) / 2} ≤ p := by
  have hqh : (0 : ℝ) < q - 1 / 2 := by linarith
  have hcpos : (0 : ℝ) < 2 * (q - 1 / 2) ^ 2 := by positivity
  refine (majority_tail_le_exp hr hb hmeas hindep hq hq2).trans ?_
  have hlog : Real.log (1 / p) ≤ (r : ℝ) * (2 * (q - 1 / 2) ^ 2) := by
    rw [div_le_iff₀ hcpos] at hrp
    linarith
  rw [one_div, Real.log_inv] at hlog
  calc Real.exp (-2 * r * (q - 1 / 2) ^ 2) ≤ Real.exp (Real.log p) :=
        Real.exp_le_exp.mpr (by nlinarith)
    _ = p := Real.exp_log hp

/-- The measure-valued restatement of `majority_repetitions_suffice`: the failure
event has measure at most `ENNReal.ofReal p`. -/
theorem majority_repetitions_suffice' [IsProbabilityMeasure μ] {r : ℕ} (hr : 0 < r)
    {ξ : Fin r → Ω → ℝ} {q p : ℝ}
    (hb : ∀ i, ∀ᵐ ω ∂μ, ξ i ω ∈ Icc (0 : ℝ) 1)
    (hmeas : ∀ i, AEMeasurable (ξ i) μ)
    (hindep : iIndepFun ξ μ)
    (hq : ∀ i, q ≤ ∫ ω, ξ i ω ∂μ) (hq2 : 1 / 2 < q)
    (hp : 0 < p) (hrp : Real.log (1 / p) / (2 * (q - 1 / 2) ^ 2) ≤ (r : ℝ)) :
    μ {ω | ∑ i, ξ i ω ≤ (r : ℝ) / 2} ≤ ENNReal.ofReal p := by
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hp.le]
  exact majority_repetitions_suffice hr hb hmeas hindep hq hq2 hp hrp

/-- **The median boost.** Let `v 0, …, v (r-1)` be `r` independent runs of an
estimator, each landing in the target interval `Icc L U` with probability at
least `q > 1/2`, and let `z ω` be *any* median of the `r` outputs. If

  `r ≥ log (1/p) / (2 (q - 1/2) ^ 2)`

then `z` lands in `Icc L U` with probability at least `1 - p`.

This is the two halves put together: `majority_repetitions_suffice` says a strict
majority of the runs is good except with probability `p`, and
`median_mem_of_majority` says a strict majority forces every median into the
interval. The repetition count is logarithmic in `1/p`. -/
theorem median_boost [IsProbabilityMeasure μ] {r : ℕ} (hr : 0 < r)
    {v : Fin r → Ω → ℝ} {z : Ω → ℝ} {L U q p : ℝ}
    (hv : ∀ i, Measurable (v i)) (hindep : iIndepFun v μ)
    (hmed : ∀ ω, IsMedian (fun i => v i ω) (z ω))
    (hq : ∀ i, q ≤ μ.real {ω | v i ω ∈ Icc L U}) (hq2 : 1 / 2 < q)
    (hp : 0 < p) (hrp : Real.log (1 / p) / (2 * (q - 1 / 2) ^ 2) ≤ (r : ℝ)) :
    1 - p ≤ μ.real {ω | z ω ∈ Icc L U} := by
  classical
  set g : ℝ → ℝ := fun x => if x ∈ Icc L U then (1 : ℝ) else 0 with hg
  have hgmeas : Measurable g :=
    Measurable.ite measurableSet_Icc measurable_const measurable_const
  set ξ : Fin r → Ω → ℝ := fun i ω => g (v i ω) with hξ
  have hξindep : iIndepFun ξ μ := hindep.comp (fun _ => g) fun _ => hgmeas
  have hξmeas : ∀ i, Measurable (ξ i) := fun i => hgmeas.comp (hv i)
  have hgood : ∀ i, MeasurableSet {ω | v i ω ∈ Icc L U} :=
    fun i => (hv i) measurableSet_Icc
  have hb : ∀ i, ∀ᵐ ω ∂μ, ξ i ω ∈ Icc (0 : ℝ) 1 := by
    intro i
    filter_upwards with ω
    simp only [hξ, hg]
    split <;> norm_num
  have hintξ : ∀ i, ∫ ω, ξ i ω ∂μ = μ.real {ω | v i ω ∈ Icc L U} := by
    intro i
    have hrw : (fun ω => ξ i ω) = Set.indicator {ω | v i ω ∈ Icc L U} 1 := by
      funext ω
      simp only [hξ, hg, Set.indicator_apply, Pi.one_apply, Set.mem_setOf_eq]
    rw [hrw, integral_indicator_one (hgood i)]
  have hcount : ∀ ω,
      ∑ i, ξ i ω = ((Finset.univ.filter fun i => v i ω ∈ Icc L U).card : ℝ) := by
    intro ω
    simp only [hξ, hg]
    exact Finset.sum_boole _ _
  have hfail := majority_repetitions_suffice (μ := μ) hr hb
    (fun i => (hξmeas i).aemeasurable) hξindep
    (fun i => by rw [hintξ i]; exact hq i) hq2 hp hrp
  set B : Set Ω := {ω | ∑ i, ξ i ω ≤ (r : ℝ) / 2} with hB
  have hBmeas : MeasurableSet B :=
    measurableSet_le (Finset.measurable_sum _ fun i _ => hξmeas i) measurable_const
  have hsub : Bᶜ ⊆ {ω | z ω ∈ Icc L U} := by
    intro ω hω
    simp only [hB, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    refine median_mem_of_majority (hmed ω) ?_
    rw [hcount ω] at hω
    have hlt : (r : ℝ)
        < 2 * ((Finset.univ.filter fun i => v i ω ∈ Icc L U).card : ℝ) := by linarith
    exact_mod_cast hlt
  have hmono : μ.real Bᶜ ≤ μ.real {ω | z ω ∈ Icc L U} :=
    measureReal_mono hsub (measure_ne_top _ _)
  rw [measureReal_compl hBmeas, probReal_univ] at hmono
  linarith

/-! ## Axiom audit

Every declaration above must rest on nothing beyond Mathlib's three foundational
axioms `[propext, Classical.choice, Quot.sound]`. -/

#print axioms sub_min_le_sq_div
#print axioms expect_min_ge
#print axioms NuIndep.comp
#print axioms integral_prod_eq_prod_integral'
#print axioms integral_prod_sq
#print axioms prod_sq_div_le
#print axioms prod_sq_div_le_exp
#print axioms median_mem_of_majority
#print axioms majority_tail_le
#print axioms hoeffding_sum_le
#print axioms majority_tail_le_exp
#print axioms majority_repetitions_suffice
#print axioms majority_repetitions_suffice'
#print axioms median_boost

end Arlib.GaussianCooling
