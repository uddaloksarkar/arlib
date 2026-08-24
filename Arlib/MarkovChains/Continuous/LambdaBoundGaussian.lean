/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.EllFloor
import Arlib.MarkovChains.Continuous.MetropolisGaussian

/-!
# The Gaussian average local conductance `λ`: the homothety route, and its exact ceiling

Cousins–Vempala `lem:lambda-bound` (`1409.6011/vol3_journal.tex:853`) asserts, for an
`a`-rounded logconcave density `f` on `ℝⁿ`,

    λ(f) = (∫_K ℓ·f)/(∫_K f)  ≥  1 − 32·δ^{1/2}·n^{1/4}/a^{1/2},

`ℓ(x) = vol(B(x,δ) ∩ K)/vol(δBₙ)` being the local conductance (`Arlib.MarkovChains.ell`).
Their proof (`:860`–`:880`) smooths `f` by convolving with a ball of radius `δ`, cites
Lovász 2007 Lemma 6.3 for `∫_K f̂ ≥ 1 − 32 δ^{1/2}n^{1/4}/a^{1/2}`, and then uses the
pointwise inequality `ℓ(x)·f(x) ≥ f̂(x)`.

**This file does not formalize that route.**  It formalizes what the *homothety* `(1−δ)·K` —
the witness of `Arlib.MarkovChains.isSmooth_of_ball_subset` (`EllFloor.lean:549`), which is
the Lebesgue analogue — gives against a Gaussian weight, proves it in the exact form the
Gaussian permits, and then proves that this route has a hard ceiling at `(1−δ)ⁿ`, which at the
operative step size is exponentially small.  Both halves are machine-checked.

## What is proved

* `lintegral_gaussianWeight_smul_set` — the **exact** Gaussian mass of a dilate:
  `∫_{c·K} γ_s = cⁿ·∫_K γ_{s/c²}`, where `γ_s(x) = e^{−‖x‖²/(2s)}` is
  `Arlib.MarkovChains.gaussianWeight`.  Shrinking the body by `c` costs the Jacobian `cⁿ`
  but *widens* the effective variance from `s` to `s/c²`.  Unlike the Lebesgue case, this is
  not a one-sided estimate: it is an identity, and it is where all the content sits.
* `gaussian_lambda_bound_sharp` — `(1−δ)ⁿ·∫_K γ_{s/(1−δ)²} ≤ ∫_K ℓ·γ_s`, for every convex `K`
  containing the unit ball and every `0 < δ < 1`.  This form is *tight*: for `K = ℝⁿ` the
  Gaussian-mass ratio `∫γ_{s/(1−δ)²}/∫γ_s` is exactly `(1−δ)⁻ⁿ`, so both sides equal `∫γ_s`.
* `gaussian_lambda_bound` — the **consumable form** with one and the same weight on both
  sides: `(1−δ)ⁿ·∫_K γ_s ≤ ∫_K ℓ·γ_s`, i.e. `(1−s')·∫_K γ ≤ ∫_K ℓ·γ` with
  `s' = 1 − (1−δ)ⁿ`.
* `avgLocalConductance_gaussian_ge` — the same in the paper's `λ` form: `λ ≥ (1−δ)ⁿ`.
* `exists_gaussian_lambda_bound_instance` — non-vacuity: the cube `[−1,1]ⁿ` at `δ = 1/2`,
  `s = 1` meets every binder.

## The honest verdict: `s' = 1 − (1−δ)ⁿ` is **not** small at the operative step

`homothety_constant_at_operative_step` (from `one_sub_pow_le_exp_neg`, `(1−δ)ⁿ ≤ e^{−nδ}`)
and `homothety_constant_at_operative_step_lower` (from Bernoulli,
`one_sub_mul_le_one_sub_pow`) bracket the delivered `s'` at `δ = σ/(8√n)`:

    1 − e^{−σ√n/8}  ≤  s'  ≤  σ·√n/8.

So there are exactly two regimes:

* `σ < 8/√n` — the bound **is** usable: `s' ≤ σ√n/8 < 1` is a genuine constant (`s' ≤ 1/8`
  at `σ = 1/√n`);
* `σ ≳ 8/√n` — the bound is **useless**: `s' ≥ 1 − e^{−σ√n/8} → 1`, so `(1−s')·∫γ ≤ ∫ℓ·γ`
  degenerates to a triviality.

Since Cousins–Vempala's Gaussian cooling raises `σ` from `Θ(1/√n)` up to `Θ(D)`, only the
coldest phases are covered.  Stated plainly rather than dressed up: **the homothety route
does not deliver `lem:lambda-bound`**, which needs `s'` bounded below `1` uniformly along the
cooling schedule.

## The obstacle, identified exactly

The loss is not slack in the estimate — it is what the witness is worth.  On the cube:

* `ell_eq_one_setOf_cube` — `{x | ℓ(x) = 1} = (1−δ)·[−1,1]ⁿ`, **exactly**.  (A Euclidean
  ball of radius `δ` reaches exactly `δ` in each coordinate direction, `ball_subset_cube_iff`;
  and for closed `K`, `ℓ(x) = 1 ↔ B(x,δ) ⊆ K`, since the deficit is open,
  `ell_eq_one_iff_ball_subset`.)
* `lintegral_ell_eq_one_cube_le` — that region carries at most `(1−δ)ⁿ·e^{n/(2s)}` of the
  Gaussian mass of the cube.

So **every** argument that lower bounds `∫_K ℓ·γ` by the mass of the set where `ℓ = 1` is
capped at `(1−δ)ⁿ` (up to `e^{n/(2s)}`, which is `≤ e` once `s ≥ n`).  Beating it requires
using the points where `0 < ℓ < 1`, which is exactly what Lovász–Vempala's ball-convolution
`f̂` does and what the homothety discards.  Formalizing CV's route needs, in order:
(i) the smoothed density `f̂(x) = min_D (∫_{x+D} f)/vol(D)` over convex `D ⊆ δBₙ` of half the
ball's volume; (ii) the pointwise `ℓ(x)f(x) ≥ f̂(x)`, which is a two-line argument once `f̂`
exists; (iii) Lovász 2007 Lemma 6.3, `∫_K f̂ ≥ 1 − 32δ^{1/2}n^{1/4}/a^{1/2}`, which is the
genuinely hard input and is **not** in this repository; and (iv) `a`-roundedness of the
truncated Gaussian, `lem:sigma-roundness` (`vol3_journal.tex:889`), giving `a = min{σ,1}`.

## Paper-oracle note

Even CV's own constant is not `o(1)` at the step size they use.  With `a = min{σ,1} = σ`
(`σ ≤ 1`) and `δ = σ/(8√n)`, their bound reads
`1 − 32·(σ/(8√n))^{1/2}·n^{1/4}/σ^{1/2} = 1 − 32/√8 ≈ 1 − 11.3`, i.e. **vacuous**.  Their
`λ ≥ 1 − s` is usable only for `δ ≤ c·σ/√n` with `c` a small absolute constant
(`c ≤ 1/4096` for `s ≤ 1/2`).  The consumer therefore needs `s` a constant below `1`, not
`o(1)`; the homothety route fails that test too, for the reason above.

## Scope

Nothing here is a conductance, mixing-time or polynomial-time statement.  There is no `def`,
`structure`, `class` or `axiom` in this file; every declaration is a `theorem`.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1. Dilation: measurability and change of variables -/

/-- A nonzero dilate of a measurable set is measurable. -/
theorem measurableSet_smul_set {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {c : ℝ} (hc : c ≠ 0) : MeasurableSet (c • K) := by
  have hSeq : c • K = (fun y : EuclideanSpace ℝ (Fin n) => c⁻¹ • y) ⁻¹' K := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, smul_smul, inv_mul_cancel₀ hc, one_smul]
      exact hy
    · intro hz
      exact ⟨c⁻¹ • z, hz, by simp [smul_smul, mul_inv_cancel₀ hc]⟩
  rw [hSeq]
  exact hK.preimage (continuous_const_smul _).measurable

/-- Membership in a nonzero dilate. -/
theorem mem_smul_set_iff_of_ne_zero {K : Set (EuclideanSpace ℝ (Fin n))} {c : ℝ} (hc : c ≠ 0)
    (y : EuclideanSpace ℝ (Fin n)) : c • y ∈ c • K ↔ y ∈ K := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have : z = y := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin n) => c⁻¹ • w) hzy
      simpa [smul_smul, inv_mul_cancel₀ hc] using this
    exact this ▸ hz
  · intro hy; exact ⟨y, hy, rfl⟩

/-- **Change of variables under a dilation, `ℝ≥0∞` form.**  Scaling the argument by `c ≠ 0`
scales the integral by `|c|⁻ⁿ`. -/
theorem lintegral_comp_smul_euclidean {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g)
    {c : ℝ} (hc : c ≠ 0) :
    ∫⁻ y, g (c • y) = ENNReal.ofReal |(c ^ n)⁻¹| * ∫⁻ x, g x := by
  have h1 : ∫⁻ x, g x ∂(Measure.map (fun y : EuclideanSpace ℝ (Fin n) => c • y) volume)
      = ∫⁻ y, g (c • y) := lintegral_map hg (continuous_const_smul c).measurable
  rw [← h1, Measure.map_addHaar_smul volume hc, finrank_euclideanSpace_fin,
    lintegral_smul_measure, smul_eq_mul]

/-! ## 2. The Gaussian weight under a dilation -/

/-- **Dilating the argument of a Gaussian weight rescales the variance.**
`e^{-‖c·y‖²/(2s)} = e^{-‖y‖²/(2(s/c²))}`. -/
theorem gaussianWeightReal_smul {c : ℝ} (hc : c ≠ 0) (s : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    gaussianWeightReal s (c • y) = gaussianWeightReal (s / c ^ 2) y := by
  unfold gaussianWeightReal
  congr 1
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hc2 : (c : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  field_simp

/-- `ℝ≥0∞` form of `gaussianWeightReal_smul`. -/
theorem gaussianWeight_smul {c : ℝ} (hc : c ≠ 0) (s : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s (c • y) = gaussianWeight (s / c ^ 2) y := by
  unfold gaussianWeight
  rw [gaussianWeightReal_smul hc]

/-- **The Gaussian weight is monotone in the variance.** -/
theorem gaussianWeightReal_mono_variance {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeightReal s x ≤ gaussianWeightReal t x := by
  unfold gaussianWeightReal
  refine Real.exp_le_exp.2 ?_
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have h2s : (0 : ℝ) < 2 * s := by linarith
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have h : ‖x‖ ^ 2 / (2 * t) ≤ ‖x‖ ^ 2 / (2 * s) := by
    rw [div_le_div_iff₀ h2t h2s]
    nlinarith [sq_nonneg ‖x‖]
  rw [neg_div, neg_div]
  linarith

/-- `ℝ≥0∞` form of `gaussianWeightReal_mono_variance`. -/
theorem gaussianWeight_mono_variance {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s x ≤ gaussianWeight t x :=
  ENNReal.ofReal_le_ofReal (gaussianWeightReal_mono_variance hs hst x)

/-! ## 3. The Gaussian mass of a dilate -/

/-- **The exact Gaussian mass of a dilate.**  Shrinking the body by `c` costs the Jacobian
`cⁿ` but *widens* the effective variance from `s` to `s/c²`:

    ∫_{c·K} e^{-‖x‖²/(2s)} dx = cⁿ · ∫_K e^{-‖x‖²/(2(s/c²))} dx.

This is an equality, not an estimate: the whole content of the homothety route against a
Gaussian weight is here. -/
theorem lintegral_gaussianWeight_smul_set {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {c : ℝ} (hc : 0 < c) (s : ℝ) :
    ∫⁻ x in c • K, gaussianWeight s x
      = ENNReal.ofReal (c ^ n) * ∫⁻ x in K, gaussianWeight (s / c ^ 2) x := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hS : MeasurableSet (c • K) := measurableSet_smul_set hK hc0
  set g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := (c • K).indicator (gaussianWeight s) with hgdef
  have hgm : Measurable g := (measurable_gaussianWeight s).indicator hS
  have hpt : ∀ y : EuclideanSpace ℝ (Fin n),
      g (c • y) = K.indicator (gaussianWeight (s / c ^ 2)) y := by
    intro y
    by_cases hy : y ∈ K
    · rw [hgdef, Set.indicator_of_mem ((mem_smul_set_iff_of_ne_zero hc0 y).2 hy),
        Set.indicator_of_mem hy, gaussianWeight_smul hc0]
    · rw [hgdef, Set.indicator_of_notMem (fun h => hy ((mem_smul_set_iff_of_ne_zero hc0 y).1 h)),
        Set.indicator_of_notMem hy]
  have h1 : ∫⁻ y, g (c • y) = ∫⁻ x in K, gaussianWeight (s / c ^ 2) x := by
    simp_rw [hpt]
    exact lintegral_indicator hK _
  have h2 : ∫⁻ y, g (c • y)
      = ENNReal.ofReal |(c ^ n)⁻¹| * ∫⁻ x in c • K, gaussianWeight s x := by
    rw [lintegral_comp_smul_euclidean hgm hc0, hgdef, lintegral_indicator hS]
  have habs : |(c ^ n)⁻¹| = (c ^ n)⁻¹ := abs_of_pos (by positivity)
  rw [← h1, h2, habs, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    mul_inv_cancel₀ (pow_ne_zero n hc0), ENNReal.ofReal_one, one_mul]

/-! ## 4. The homothety witness: `ℓ = 1` on `(1-δ)·K` -/

/-- A convex set containing the origin contains all its dilates by `c ∈ [0,1]`. -/
theorem smul_subset_of_convex {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c • K ⊆ K := by
  rintro x ⟨y, hy, rfl⟩
  have := hKc hy h0K hc0 (by linarith : (0 : ℝ) ≤ 1 - c) (by ring)
  simpa using this

/-- **The homothety witness.**  If `K` is convex and contains the unit ball, then the
`δ`-ball around any point of `(1-δ)·K` still lies in `K`.  (This is the geometric content of
`Arlib.MarkovChains.isSmooth_of_ball_subset`, re-derived here because it is internal to that
proof.) -/
theorem ball_smul_subset_of_convex {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ y ∈ K, ball ((1 - δ) • y) δ ⊆ K := by
  have hc0 : (0 : ℝ) < 1 - δ := by linarith
  intro y hy z hz
  rw [mem_ball, dist_eq_norm] at hz
  have hw : δ⁻¹ • (z - (1 - δ) • y) ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hδ)]
    calc δ⁻¹ * ‖z - (1 - δ) • y‖ < δ⁻¹ * δ := mul_lt_mul_of_pos_left hz (inv_pos.2 hδ)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hδ)
  have hmem := hKc hy (hball hw) hc0.le hδ.le (by ring)
  have heq : (1 - δ) • y + δ • (δ⁻¹ • (z - (1 - δ) • y)) = z := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hδ), one_smul]; abel
  rwa [heq] at hmem

/-- **The local conductance is exactly `1` on the shrunken body `(1-δ)·K`.** -/
theorem ell_eq_one_of_mem_smul {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (1 - δ) • K) : ell K δ x = 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [ell_apply, Set.inter_eq_self_of_subset_left (ball_smul_subset_of_convex hKc hball hδ hδ1 y hy)]
  exact ENNReal.div_self (Metric.measure_ball_pos volume _ hδ).ne' measure_ball_lt_top.ne

/-! ## 5. The Gaussian average local conductance bound -/

/-- **The sharp homothety bound.**  For every convex `K` containing the unit ball and every
`0 < δ < 1`,

    (1-δ)ⁿ · ∫_K e^{-‖x‖²/(2(s/(1-δ)²))} dx  ≤  ∫_K ℓ(x)·e^{-‖x‖²/(2s)} dx.

The variance on the left is *widened* from `s` to `s/(1-δ)²`; the whole exact content of the
homothety `(1-δ)·K` against a Gaussian weight is retained.  The plain form
`gaussian_lambda_bound` (same variance on both sides) follows by monotonicity in the
variance, and is strictly weaker: for `K = ℝⁿ` the ratio
`∫ γ_{s/(1-δ)²} / ∫ γ_s` is exactly `(1-δ)⁻ⁿ`, which cancels the prefactor entirely. -/
theorem gaussian_lambda_bound_sharp {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (s : ℝ) :
    ENNReal.ofReal ((1 - δ) ^ n) * ∫⁻ x in K, gaussianWeight (s / (1 - δ) ^ 2) x
      ≤ ∫⁻ x in K, ell K δ x * gaussianWeight s x := by
  have hc : (0 : ℝ) < 1 - δ := by linarith
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    hball (by rw [mem_ball, dist_self]; norm_num)
  have hSm : MeasurableSet ((1 - δ) • K) := measurableSet_smul_set hK (ne_of_gt hc)
  have hSK : (1 - δ) • K ⊆ K := smul_subset_of_convex hKc h0K hc.le (by linarith)
  have hEq : ∫⁻ x in (1 - δ) • K, ell K δ x * gaussianWeight s x
      = ∫⁻ x in (1 - δ) • K, gaussianWeight s x :=
    lintegral_congr_ae (by
      filter_upwards [self_mem_ae_restrict hSm] with x hx
      rw [ell_eq_one_of_mem_smul hKc hball hδ hδ1 hx, one_mul])
  calc ENNReal.ofReal ((1 - δ) ^ n) * ∫⁻ x in K, gaussianWeight (s / (1 - δ) ^ 2) x
      = ∫⁻ x in (1 - δ) • K, gaussianWeight s x :=
        (lintegral_gaussianWeight_smul_set hK hc s).symm
    _ = ∫⁻ x in (1 - δ) • K, ell K δ x * gaussianWeight s x := hEq.symm
    _ ≤ ∫⁻ x in K, ell K δ x * gaussianWeight s x :=
        lintegral_mono' (Measure.restrict_mono hSK le_rfl) le_rfl

/-- **The consumable form.**  `(1-s)·∫_K γ ≤ ∫_K ℓ·γ` with `1 - s = (1-δ)ⁿ`, i.e.
`s = 1 - (1-δ)ⁿ`, for the *same* Gaussian weight on both sides. -/
theorem gaussian_lambda_bound {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal ((1 - δ) ^ n) * ∫⁻ x in K, gaussianWeight s x
      ≤ ∫⁻ x in K, ell K δ x * gaussianWeight s x := by
  have hc : (0 : ℝ) < 1 - δ := by linarith
  have hsq1 : (1 - δ) ^ 2 ≤ 1 := by nlinarith
  have hge : s ≤ s / (1 - δ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  refine le_trans ?_ (gaussian_lambda_bound_sharp hK hKc hball hδ hδ1 s)
  gcongr with x
  exact gaussianWeight_mono_variance hs hge x

/-- **The paper's `λ(f)` form.**  `λ = (∫_K ℓ·γ)/(∫_K γ) ≥ (1-δ)ⁿ` for every convex `K` of
finite volume containing the unit ball. -/
theorem avgLocalConductance_gaussian_ge {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKtop : volume K ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal ((1 - δ) ^ n)
      ≤ (∫⁻ x in K, ell K δ x * gaussianWeight s x) / (∫⁻ x in K, gaussianWeight s x) := by
  have hvolK : volume K ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 one_pos) (measure_mono hball))
  have hb0 : ∫⁻ x in K, gaussianWeight s x ≠ 0 := by
    intro h
    rw [lintegral_eq_zero_iff (measurable_gaussianWeight s)] at h
    have h2 : ∀ᵐ x ∂(volume.restrict K), False := by
      filter_upwards [h] with x hx
      exact gaussianWeight_ne_zero s x hx
    rw [ae_iff] at h2
    simp only [not_false_eq_true, Set.setOf_true, Measure.restrict_apply_univ] at h2
    exact hvolK h2
  have hbtop : ∫⁻ x in K, gaussianWeight s x ≠ ⊤ := by
    refine ne_top_of_le_ne_top hKtop ?_
    calc ∫⁻ x in K, gaussianWeight s x ≤ ∫⁻ _ in K, 1 :=
          lintegral_mono fun x => gaussianWeight_le_one hs x
      _ = volume K := setLIntegral_one K
  rw [ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbtop)]
  exact gaussian_lambda_bound hK hKc hball hδ hδ1 hs

/-! ## 6. How big is the achieved `s = 1 - (1-δ)ⁿ`? -/

/-- `(1-δ)ⁿ ≤ e^{-nδ}`. -/
theorem one_sub_pow_le_exp_neg {δ : ℝ} (hδ1 : δ ≤ 1) (n : ℕ) :
    (1 - δ) ^ n ≤ Real.exp (-((n : ℝ) * δ)) := by
  have h1 : 1 - δ ≤ Real.exp (-δ) := by
    have := Real.add_one_le_exp (-δ)
    linarith
  calc (1 - δ) ^ n ≤ (Real.exp (-δ)) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = Real.exp ((n : ℝ) * (-δ)) := (Real.exp_nat_mul (-δ) n).symm
    _ = Real.exp (-((n : ℝ) * δ)) := by ring_nf

/-- **The achieved constant at the operative step size `δ = σ/(8√n)` is `e^{-σ√n/8}`.**

This is the honest reading of `gaussian_lambda_bound`: the `s` it delivers is
`1 - (1-δ)ⁿ ≥ 1 - e^{-σ√n/8}`, which tends to `1` — the bound is *vacuous* — as soon as
`σ√n → ∞`.  It is a genuine constant only in the regime `σ = O(1/√n)`. -/
theorem homothety_constant_at_operative_step {σ : ℝ} (hσ : 0 < σ) (hn : 0 < n)
    (hδ1 : σ / (8 * Real.sqrt n) ≤ 1) :
    (1 - σ / (8 * Real.sqrt n)) ^ n ≤ Real.exp (-(σ * Real.sqrt n / 8)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set r : ℝ := Real.sqrt (n : ℝ) with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hnR
  have hrr : r * r = (n : ℝ) := Real.mul_self_sqrt hnR.le
  have h := one_sub_pow_le_exp_neg (δ := σ / (8 * r)) hδ1 n
  have hkey : (n : ℝ) * (σ / (8 * r)) = σ * r / 8 := by
    rw [← hrr]; field_simp
  rwa [hkey] at h

/-- **Bernoulli.**  `1 - n·δ ≤ (1-δ)ⁿ`. -/
theorem one_sub_mul_le_one_sub_pow {δ : ℝ} (hδ2 : δ ≤ 2) (n : ℕ) :
    1 - (n : ℝ) * δ ≤ (1 - δ) ^ n := by
  have h := one_add_mul_le_pow (a := -δ) (by linarith) n
  simpa [sub_eq_add_neg, mul_neg] using h

/-- **The achieved constant at the operative step size, from below.**  At `δ = σ/(8√n)` the
delivered `s' = 1 - (1-δ)ⁿ` is at most `σ√n/8`.  Together with
`homothety_constant_at_operative_step` this brackets it:

    1 - e^{-σ√n/8}  ≤  s'  ≤  σ·√n/8,

so the bound is a genuine constant exactly in the cold regime `σ < 8/√n`. -/
theorem homothety_constant_at_operative_step_lower {σ : ℝ} (hσ : 0 < σ) (hn : 0 < n)
    (hδ2 : σ / (8 * Real.sqrt n) ≤ 2) :
    1 - σ * Real.sqrt n / 8 ≤ (1 - σ / (8 * Real.sqrt n)) ^ n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set r : ℝ := Real.sqrt (n : ℝ) with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hnR
  have hrr : r * r = (n : ℝ) := Real.mul_self_sqrt hnR.le
  have h := one_sub_mul_le_one_sub_pow (δ := σ / (8 * r)) hδ2 n
  have hkey : (n : ℝ) * (σ / (8 * r)) = σ * r / 8 := by
    rw [← hrr]; field_simp
  rwa [hkey] at h

/-! ## 7. Non-vacuity: the cube is an instance -/

/-- The cube `[-1,1]ⁿ` has finite volume. -/
theorem volume_supNormCube_ne_top :
    volume {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (measure_mono
    (show {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}
        ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) from
      fun _y hy => mem_closedBall_zero_iff.2 (norm_le_sqrt_of_mem_cube hy)))
    measure_closedBall_lt_top)

/-- The cube `[-1,1]ⁿ` has positive volume. -/
theorem volume_supNormCube_ne_zero :
    volume {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 one_pos)
    (measure_mono ball_subset_cube))

/-- **Non-vacuity.**  The whole binder bundle of `avgLocalConductance_gaussian_ge` is met by
the cube `[-1,1]ⁿ` at `δ = 1/2`, `s = 1`, so the bound is not vacuously quantified. -/
theorem exists_gaussian_lambda_bound_instance :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ),
      MeasurableSet K ∧ Convex ℝ K ∧ ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K ∧
      volume K ≠ ⊤ ∧ volume K ≠ 0 ∧ 0 < δ ∧ δ < 1 ∧ 0 < s ∧
      ENNReal.ofReal ((1 - δ) ^ n)
        ≤ (∫⁻ x in K, ell K δ x * gaussianWeight s x) / (∫⁻ x in K, gaussianWeight s x) :=
  ⟨{y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, 1 / 2, 1,
    measurableSet_supNormCube, convex_supNormCube, ball_subset_cube,
    volume_supNormCube_ne_top, volume_supNormCube_ne_zero, by norm_num, by norm_num, one_pos,
    avgLocalConductance_gaussian_ge measurableSet_supNormCube convex_supNormCube
      ball_subset_cube volume_supNormCube_ne_top (by norm_num) (by norm_num) one_pos⟩

/-! ## 8. The homothety witness is capped at `(1-δ)ⁿ`: the cube -/

/-- On the cube `[-1,1]ⁿ` the Gaussian weight is at least `e^{-n/(2s)}`. -/
theorem gaussianWeight_ge_on_cube {s : ℝ} (hs : 0 < s) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ j, |x j| ≤ 1) :
    ENNReal.ofReal (Real.exp (-(n : ℝ) / (2 * s))) ≤ gaussianWeight s x := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hnorm : ‖x‖ ≤ Real.sqrt n := norm_le_sqrt_of_mem_cube hx
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq : ‖x‖ ^ 2 ≤ (n : ℝ) := by
    have := Real.sq_sqrt hn0
    nlinarith [norm_nonneg x, Real.sqrt_nonneg (n : ℝ)]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  linarith

/-- **The homothety witness carries at most a `(1-δ)ⁿ·e^{n/(2s)}` fraction of the Gaussian
mass of the cube.**

`gaussian_lambda_bound` lower-bounds `∫_K ℓ·γ` by the Gaussian mass of the region
`(1-δ)·K`, on which `ℓ = 1`.  On the cube that region carries at most
`(1-δ)ⁿ·e^{n/(2s)}` of the total Gaussian mass — for `s ≥ n` at most `e·(1-δ)ⁿ`.  So the
prefactor `(1-δ)ⁿ` of `gaussian_lambda_bound` is **not an artefact of a lossy estimate**: it
is what the homothety witness is worth, and no sharpening of the argument that keeps this
witness can remove it. -/
theorem lintegral_gaussianWeight_smul_cube_le {δ s : ℝ} (hδ1 : δ < 1) (hs : 0 < s) :
    ∫⁻ x in (1 - δ) • {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, gaussianWeight s x
      ≤ ENNReal.ofReal ((1 - δ) ^ n * Real.exp ((n : ℝ) / (2 * s)))
          * ∫⁻ x in {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, gaussianWeight s x := by
  have hc : (0 : ℝ) < 1 - δ := by linarith
  set C : Set (EuclideanSpace ℝ (Fin n)) := {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}
    with hCdef
  -- upper bound on the mass of the shrunken cube
  have hup : ∫⁻ x in (1 - δ) • C, gaussianWeight s x ≤ ENNReal.ofReal ((1 - δ) ^ n) * volume C := by
    calc ∫⁻ x in (1 - δ) • C, gaussianWeight s x ≤ ∫⁻ _ in (1 - δ) • C, 1 :=
          lintegral_mono fun x => gaussianWeight_le_one hs x
      _ = volume ((1 - δ) • C) := setLIntegral_one _
      _ = ENNReal.ofReal ((1 - δ) ^ n) * volume C := by
          rw [Measure.addHaar_smul, finrank_euclideanSpace_fin,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 - δ) ^ n)]
  -- lower bound on the mass of the cube
  have hlow : ENNReal.ofReal (Real.exp (-(n : ℝ) / (2 * s))) * volume C
      ≤ ∫⁻ x in C, gaussianWeight s x := by
    calc ENNReal.ofReal (Real.exp (-(n : ℝ) / (2 * s))) * volume C
        = ∫⁻ _ in C, ENNReal.ofReal (Real.exp (-(n : ℝ) / (2 * s))) := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ x in C, gaussianWeight s x := by
          refine setLIntegral_mono' measurableSet_supNormCube fun x hx => ?_
          exact gaussianWeight_ge_on_cube hs hx
  -- combine
  have hexp : ENNReal.ofReal (Real.exp ((n : ℝ) / (2 * s)))
      * ENNReal.ofReal (Real.exp (-(n : ℝ) / (2 * s))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      show (n : ℝ) / (2 * s) + -(n : ℝ) / (2 * s) = 0 by ring, Real.exp_zero,
      ENNReal.ofReal_one]
  calc ∫⁻ x in (1 - δ) • C, gaussianWeight s x
      ≤ ENNReal.ofReal ((1 - δ) ^ n) * volume C := hup
    _ = ENNReal.ofReal ((1 - δ) ^ n) * ENNReal.ofReal (Real.exp ((n : ℝ) / (2 * s)))
          * (ENNReal.ofReal (Real.exp (-(n : ℝ) / (2 * s))) * volume C) := by
        rw [mul_assoc, ← mul_assoc (ENNReal.ofReal (Real.exp ((n : ℝ) / (2 * s)))), hexp, one_mul]
    _ ≤ ENNReal.ofReal ((1 - δ) ^ n) * ENNReal.ofReal (Real.exp ((n : ℝ) / (2 * s)))
          * ∫⁻ x in C, gaussianWeight s x := by gcongr
    _ = ENNReal.ofReal ((1 - δ) ^ n * Real.exp ((n : ℝ) / (2 * s)))
          * ∫⁻ x in C, gaussianWeight s x := by
        rw [← ENNReal.ofReal_mul (by positivity)]

/-! ## 9. On the cube the `ℓ = 1` region **is** the homothety witness -/

/-- For a *closed* `K`, `ℓ(x) = 1` exactly when the whole proposal ball lies in `K`: the
deficit `B(x,δ) \ K` is open, so it is null only if it is empty. -/
theorem ell_eq_one_iff_ball_subset {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKcl : IsClosed K) {δ : ℝ} (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n)) :
    ell K δ x = 1 ↔ ball x δ ⊆ K := by
  have hb0 : volume (ball x δ) ≠ 0 := (Metric.measure_ball_pos volume x hδ).ne'
  have hbt : volume (ball x δ) ≠ ⊤ := measure_ball_lt_top.ne
  constructor
  · intro h
    have heq : volume (ball x δ ∩ K) = volume (ball x δ) := by
      rw [ell_apply, ENNReal.div_eq_one_iff hb0 hbt] at h
      exact h
    have hsum := measure_inter_add_sdiff (μ := volume) (ball x δ) hK
    rw [heq] at hsum
    have hdiff : volume (ball x δ \ K) = 0 := by
      have h0 : volume (ball x δ) + volume (ball x δ \ K) = volume (ball x δ) + 0 := by
        rw [add_zero]; exact hsum
      exact (ENNReal.add_right_inj hbt).1 h0
    intro z hz
    by_contra hzK
    exact absurd hdiff ((Metric.isOpen_ball.sdiff hKcl).measure_pos volume ⟨z, hz, hzK⟩).ne'
  · intro h
    rw [ell_apply, Set.inter_eq_self_of_subset_left h]
    exact ENNReal.div_self hb0 hbt

/-- The cube `[-1,1]ⁿ` is closed. -/
theorem isClosed_supNormCube :
    IsClosed {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} := by
  have h : {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}
      = ⋂ j : Fin n, {y : EuclideanSpace ℝ (Fin n) | |y j| ≤ 1} := by ext y; simp
  rw [h]
  exact isClosed_iInter fun j =>
    isClosed_le ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.abs) continuous_const

/-- **The `δ`-interior of the cube is the cube of half-side `1-δ`.**  A Euclidean ball of
radius `δ` reaches exactly `δ` in each coordinate direction, so `B(x,δ) ⊆ [-1,1]ⁿ` iff every
coordinate of `x` is at most `1-δ` in absolute value. -/
theorem ball_subset_cube_iff {δ : ℝ} (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n)) :
    ball x δ ⊆ {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} ↔ ∀ j, |x j| ≤ 1 - δ := by
  constructor
  · intro h j
    have hx1 : |x j| ≤ 1 := h (Metric.mem_ball_self hδ) j
    have key : ∀ t : ℝ, 0 < t → t < δ → |x j| + t ≤ 1 := by
      intro t ht htδ
      set e : ℝ := if 0 ≤ x j then t else -t with hedef
      have habse : |e| = t := by
        rw [hedef]; by_cases hxj : 0 ≤ x j
        · simp [hxj, abs_of_pos ht]
        · simp [hxj, abs_of_pos ht]
      have hnorm : ‖(EuclideanSpace.single j e : EuclideanSpace ℝ (Fin n))‖ = t := by
        rw [PiLp.norm_single, Real.norm_eq_abs, habse]
      have hz : x + (EuclideanSpace.single j e : EuclideanSpace ℝ (Fin n)) ∈ ball x δ := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm]
        exact htδ
      have hzc := h hz j
      have hcoord : (x + (EuclideanSpace.single j e : EuclideanSpace ℝ (Fin n))) j = x j + e := by
        simp
      rw [hcoord] at hzc
      by_cases hxj : 0 ≤ x j
      · have he : e = t := by rw [hedef, if_pos hxj]
        rw [he, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x j + t)] at hzc
        rw [abs_of_nonneg hxj]
        linarith
      · have hxj' : x j < 0 := not_le.1 hxj
        have he : e = -t := by rw [hedef, if_neg hxj]
        rw [he, abs_of_neg (by linarith : x j + -t < 0)] at hzc
        rw [abs_of_neg hxj']
        linarith
    have hδle : δ ≤ 1 - |x j| := by
      refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
      rcases le_or_gt c 0 with h0 | h0
      · linarith
      · have := key c h0 hc; linarith
    linarith
  · intro h z hz j
    rw [mem_ball, dist_eq_norm] at hz
    have hcoord : |z j - x j| ≤ ‖z - x‖ := by
      have := abs_coord_le_norm (z - x) j
      simpa using this
    have h2 : |z j| ≤ |x j| + |z j - x j| := by
      calc |z j| = |x j + (z j - x j)| := by congr 1; ring
        _ ≤ |x j| + |z j - x j| := abs_add_le _ _
    have := h j
    linarith

/-- The cube of half-side `1-δ` is the dilate `(1-δ)·[-1,1]ⁿ`. -/
theorem smul_supNormCube {δ : ℝ} (hc : 0 < 1 - δ) :
    (1 - δ) • {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}
      = {x : EuclideanSpace ℝ (Fin n) | ∀ j, |x j| ≤ 1 - δ} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    have : ((1 - δ) • y) j = (1 - δ) * y j := by simp
    rw [this, abs_mul, abs_of_pos hc]
    nlinarith [hy j, abs_nonneg (y j)]
  · intro hx
    refine ⟨(1 - δ)⁻¹ • x, fun j => ?_, by
      show (1 - δ) • ((1 - δ)⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]⟩
    have : ((1 - δ)⁻¹ • x) j = (1 - δ)⁻¹ * x j := by simp
    rw [this, abs_mul, abs_of_pos (inv_pos.2 hc), inv_mul_le_iff₀ hc, mul_one]
    exact hx j

/-- **The `ℓ = 1` region of the cube is exactly `(1-δ)·[-1,1]ⁿ`.**

Together with `lintegral_gaussianWeight_smul_cube_le` this says: *every* argument that lower
bounds `∫_K ℓ·γ` by the Gaussian mass of the set where `ℓ = 1` is capped at
`(1-δ)ⁿ·e^{n/(2s)}` on the cube.  The `(1-δ)ⁿ` of `gaussian_lambda_bound` is therefore the
exact price of this route, not a slack estimate — and at the operative `δ = σ/(8√n)` it is
`e^{-Θ(σ√n)}` (`homothety_constant_at_operative_step`).  Beating it requires the
Lovász–Vempala ball-convolution smoothing `f̂` of `vol3_journal.tex:860`, which lower bounds
`∫_K ℓ·f` *without* discarding the points where `0 < ℓ < 1`. -/
theorem ell_eq_one_setOf_cube {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    {x : EuclideanSpace ℝ (Fin n) | ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ x = 1}
      = (1 - δ) • {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} := by
  rw [smul_supNormCube (by linarith)]
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
    ell_eq_one_iff_ball_subset measurableSet_supNormCube isClosed_supNormCube hδ x,
    ball_subset_cube_iff hδ x]

/-- **The verdict on the route, in one statement.**  On the cube, the Gaussian mass of the
whole region where `ℓ = 1` is at most `(1-δ)ⁿ·e^{n/(2s)}` times the Gaussian mass of the
body. -/
theorem lintegral_ell_eq_one_cube_le {δ s : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s) :
    ∫⁻ x in {x : EuclideanSpace ℝ (Fin n) |
        ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} δ x = 1}, gaussianWeight s x
      ≤ ENNReal.ofReal ((1 - δ) ^ n * Real.exp ((n : ℝ) / (2 * s)))
          * ∫⁻ x in {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, gaussianWeight s x := by
  rw [ell_eq_one_setOf_cube hδ hδ1]
  exact lintegral_gaussianWeight_smul_cube_le hδ1 hs

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.measurableSet_smul_set
#print axioms Arlib.MarkovChains.mem_smul_set_iff_of_ne_zero
#print axioms Arlib.MarkovChains.lintegral_comp_smul_euclidean
#print axioms Arlib.MarkovChains.gaussianWeightReal_smul
#print axioms Arlib.MarkovChains.gaussianWeight_smul
#print axioms Arlib.MarkovChains.gaussianWeightReal_mono_variance
#print axioms Arlib.MarkovChains.gaussianWeight_mono_variance
#print axioms Arlib.MarkovChains.lintegral_gaussianWeight_smul_set
#print axioms Arlib.MarkovChains.smul_subset_of_convex
#print axioms Arlib.MarkovChains.ball_smul_subset_of_convex
#print axioms Arlib.MarkovChains.ell_eq_one_of_mem_smul
#print axioms Arlib.MarkovChains.gaussian_lambda_bound_sharp
#print axioms Arlib.MarkovChains.gaussian_lambda_bound
#print axioms Arlib.MarkovChains.avgLocalConductance_gaussian_ge
#print axioms Arlib.MarkovChains.one_sub_pow_le_exp_neg
#print axioms Arlib.MarkovChains.homothety_constant_at_operative_step
#print axioms Arlib.MarkovChains.one_sub_mul_le_one_sub_pow
#print axioms Arlib.MarkovChains.homothety_constant_at_operative_step_lower
#print axioms Arlib.MarkovChains.volume_supNormCube_ne_top
#print axioms Arlib.MarkovChains.volume_supNormCube_ne_zero
#print axioms Arlib.MarkovChains.exists_gaussian_lambda_bound_instance
#print axioms Arlib.MarkovChains.gaussianWeight_ge_on_cube
#print axioms Arlib.MarkovChains.lintegral_gaussianWeight_smul_cube_le
#print axioms Arlib.MarkovChains.ell_eq_one_iff_ball_subset
#print axioms Arlib.MarkovChains.isClosed_supNormCube
#print axioms Arlib.MarkovChains.ball_subset_cube_iff
#print axioms Arlib.MarkovChains.smul_supNormCube
#print axioms Arlib.MarkovChains.ell_eq_one_setOf_cube
#print axioms Arlib.MarkovChains.lintegral_ell_eq_one_cube_le
