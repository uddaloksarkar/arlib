/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.LambdaBoundGaussian

/-!
# The two Kannan–Lovász–Simonovits inputs to `lem:map-speedy-to-ball`, at `δ ≤ 1/(2n)`

Cousins–Vempala's `lem:map-speedy-to-ball` (`1409.6011/vol3_journal.tex:942`) maps the speedy
walk's law `∝ ℓ·f` to the target `∝ f` by a rejection routine at shrink factor
`c = 1 − 1/(2n)`.  Its analysis imports two facts, cited as "[18]":

1. `Q̂(cK) ≥ 1/2` — the `ℓf`-mass does not pile up in the boundary shell;
2. `∫_{μ_L ∩ cK} (1 − ℓ(x)) dx ≤ ε·vol(μ_L ∩ cK)` — the average local-conductance *deficit*
   over the shrunken body is small.

**The citation is to the wrong paper.**  Reference [18] is Kannan–Lovász–Simonovits,
*Isoperimetric problems for convex bodies and a localization lemma*, DCG 13 (1995), which
contains only isoperimetry and the localization lemma — no ball walk, no local conductance,
no `Q̂`; its §3 is a single Theorem 3.1 and its §4 a single Theorem 4.1, so the cited
"Theorem 4.16" and "Lemma 3.5" do not exist there.  The random-walk machinery is in the
companion paper, reference **[19]**: *Random walks and an `O*(n⁵)` volume algorithm for convex
bodies*, RSA 11 (1997).  The theorem numbers match [19], not [18].

## What this file proves, and the regime that makes it elementary

Both facts become **provable outright**, with no external input, once `δ ≤ 1 − c = 1/(2n)`.
The reason is a one-line convexity argument:

> if `B ⊆ K` and `x ∈ cK`, say `x = c·y` with `y ∈ K`, then `x + (1−c)·B ⊆ K`, because
> `c·y + (1−c)·z ∈ K` for every `z ∈ B ⊆ K` by convexity.

So every point of `cK` lies at distance at least `1 − c` from the complement of `K`.  If the
step size does not exceed that distance, the proposal ball never escapes, and

    ℓ(x) = 1  for every  x ∈ cK,

which gives fact 2 with `ε = 0` — *pointwise*, not merely on average — and reduces fact 1 to
the volume ratio `cⁿ = (1 − 1/(2n))ⁿ ≥ 1/2`.

**This is a genuine restriction, stated honestly.**  Cousins–Vempala run at
`δ ≤ min{σ,1}/(8√(n log(n/ε)))`, which is much *larger* than `1/(2n)` for `σ = Θ(1)`, and in
that regime the deficit does not vanish and the KLS97 average-deficit bound is genuinely
needed.  What the regime here costs is a worse exponent, not polynomiality: the mixing bound
`Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit` scales as `(σ√n/δ)²`, so at
`δ = Θ(1/n)` it reads `O(σ²n³·log(M/ε))` instead of `O(σ²n²·log(M/ε))`.

## What is proved here

* `Arlib.MarkovChains.half_le_one_sub_inv_two_mul_pow` — `(1 − 1/(2n))ⁿ ≥ 1/2` for `n ≥ 1`.
* `Arlib.MarkovChains.ell_eq_one_on_shrunken` — **KLS97 fact 2 at `ε = 0`**: `ℓ ≡ 1` on `cK`.
* `Arlib.MarkovChains.lintegral_one_sub_ell_shrunken_eq_zero` — the deficit integral vanishes,
  i.e. Cousins–Vempala's display holds for every `ε ≥ 0`.
* `Arlib.MarkovChains.half_le_speedy_shrunken` — **KLS97 fact 1**: `Q̂(cK) ≥ 1/2`, for the
  Gaussian-weighted speedy law.

## Scope

These are the two *inputs* to `lem:map-speedy-to-ball`.  The rejection routine itself, and the
`10ε` total-variation conclusion, are **not** proved here.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1. The volume ratio of the shrunken body -/

/-- **`(1 − 1/(2n))ⁿ ≥ 1/2` for every `n ≥ 1`.**

This is the volume ratio `vol(cK)/vol(K)` at Cousins–Vempala's shrink factor
`c = 1 − 1/(2n)`, and it is what makes that particular factor the right one: it is the largest
shrink that still retains half the volume, and it tends to `e^{−1/2} ≈ 0.6065`.

Proved from Bernoulli's inequality `1 − n·t ≤ (1 − t)ⁿ`
(`Arlib.MarkovChains.one_sub_mul_le_one_sub_pow`) at `t = 1/(2n)`, where the left side is
exactly `1/2`. -/
theorem half_le_one_sub_inv_two_mul_pow (hn : 1 ≤ n) :
    (1 : ℝ) / 2 ≤ (1 - 1 / (2 * (n : ℝ))) ^ n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hb2 : 1 / (2 * (n : ℝ)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hle := one_sub_mul_le_one_sub_pow (δ := 1 / (2 * (n : ℝ))) hb2 n
  have heq : (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 / 2 := by field_simp
  rw [heq] at hle
  linarith

/-! ## 2. KLS97 fact 2, at `ε = 0`: the deficit vanishes on the shrunken body -/

/-- **`ℓ ≡ 1` on the shrunken body, when the step does not exceed the shrink.**

If `B ⊆ K` and `x ∈ c·K`, convexity puts `x + (1−c)·B` inside `K`, so the proposal ball of
radius `δ ≤ 1 − c` never escapes and the local conductance is exactly `1`.

This is Cousins–Vempala's second KLS97 input in its strongest possible form: their
`∫_{μ_L ∩ cK}(1 − ℓ) ≤ ε·vol(μ_L ∩ cK)` holds here **pointwise with `ε = 0`**, for every level
set at once, because the integrand is identically zero on `cK`.

The hypothesis `δ ≤ 1 − c` is exactly the regime restriction discussed in the module
docstring; at Cousins–Vempala's larger step this is false and the genuine averaged KLS97
bound is needed. -/
theorem ell_eq_one_on_shrunken {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {c δ : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hδ : 0 < δ) (hδc : δ ≤ 1 - c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ c • K) :
    ell K δ x = 1 := by
  have hδ1 : δ < 1 := lt_of_le_of_lt hδc (by linarith)
  -- `x = c • y` with `y ∈ K`, and `ball (c • y) (1 − c) ⊆ K` by convexity
  obtain ⟨y, hyK, rfl⟩ := hx
  have hsub : ball ((1 - (1 - c)) • y) (1 - c) ⊆ K :=
    ball_smul_subset_of_convex hKc hball (by linarith) (by linarith) y hyK
  have hcc : (1 : ℝ) - (1 - c) = c := by ring
  rw [hcc] at hsub
  -- the `δ`-ball is inside the `(1−c)`-ball
  have hball' : ball (c • y) δ ⊆ K :=
    subset_trans (Metric.ball_subset_ball hδc) hsub
  -- and a proposal ball inside `K` means `ℓ = 1`
  have hinter : ball (c • y) δ ∩ K = ball (c • y) δ := Set.inter_eq_left.2 hball'
  rw [ell_apply, hinter, ENNReal.div_self]
  · exact (measure_ball_pos volume _ hδ).ne'
  · exact measure_ball_lt_top.ne

/-- **The deficit integral over the shrunken body is zero.**

Cousins–Vempala's display `∫_{cK}(1 − ℓ(x))·g(x) dx ≤ ε·∫_{cK} g` therefore holds for **every**
`ε ≥ 0` and every weight `g` in this regime, since the integrand vanishes identically. -/
theorem lintegral_one_sub_ell_shrunken_eq_zero {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {c δ : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hδ : 0 < δ) (hδc : δ ≤ 1 - c)
    (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    ∫⁻ x in c • K, (1 - ell K δ x) * g x = 0 := by
  rw [setLIntegral_congr_fun (measurableSet_smul_set hK (ne_of_gt hc0)) (fun x hx => ?_)]
  · exact lintegral_zero
  · rw [ell_eq_one_on_shrunken hKc hball hc0 hc1 hδ hδc hx, tsub_self, zero_mul]

/-! ## 3. KLS97 fact 1: the speedy law keeps half its mass on the shrunken body -/

/-- **`Q̂(cK) ≥ 1/2`** for the Gaussian-weighted speedy law `∝ ℓ·γ`, at `c = 1 − 1/(2n)` and
`δ ≤ 1/(2n)`.

Two ingredients, exactly as in Cousins–Vempala's sketch:

* on `cK` the local conductance is `1` (`ell_eq_one_on_shrunken`), so the numerator is the
  plain Gaussian mass of `cK`;
* that mass is at least `cⁿ` times the Gaussian mass of `K`, by the scaling identity
  `Arlib.MarkovChains.lintegral_gaussianWeight_smul_set` together with monotonicity of the
  Gaussian weight in its variance — shrinking moves points *towards* the origin, where the
  weight is larger, so the Gaussian only helps;

and `cⁿ ≥ 1/2` is `half_le_one_sub_inv_two_mul_pow`.  Weighting by `ℓ ≤ 1` in the denominator
can only decrease it, which is the remaining inequality. -/
theorem half_le_speedy_shrunken (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {δ s : ℝ}
    (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) (hs : 0 < s) :
    ENNReal.ofReal (1 / 2) * ∫⁻ x in K, ell K δ x * gaussianWeight s x
      ≤ ∫⁻ x in (1 - 1 / (2 * (n : ℝ))) • K, ell K δ x * gaussianWeight s x := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hhalf : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set c : ℝ := 1 - 1 / (2 * (n : ℝ)) with hcdef
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hδc : δ ≤ 1 - c := by rw [hcdef]; linarith
  -- numerator: `ℓ = 1` on `c • K`
  have hnum : (∫⁻ x in c • K, ell K δ x * gaussianWeight s x)
      = ∫⁻ x in c • K, gaussianWeight s x := by
    refine setLIntegral_congr_fun (measurableSet_smul_set hK (ne_of_gt hc0)) (fun x hx => ?_)
    rw [ell_eq_one_on_shrunken hKc hball hc0 hc1 hδ hδc hx, one_mul]
  -- the Gaussian mass of the shrunken body
  have hscale : (∫⁻ x in c • K, gaussianWeight s x)
      = ENNReal.ofReal (c ^ n) * ∫⁻ x in K, gaussianWeight (s / c ^ 2) x :=
    lintegral_gaussianWeight_smul_set hK hc0 s
  have hmono : (∫⁻ x in K, gaussianWeight s x) ≤ ∫⁻ x in K, gaussianWeight (s / c ^ 2) x := by
    refine lintegral_mono fun x => ?_
    refine gaussianWeight_mono_variance hs ?_ x
    rw [le_div_iff₀ (by positivity)]
    have hcsq : c ^ 2 ≤ 1 := by nlinarith
    nlinarith [hs.le]
  -- the denominator is at most the plain Gaussian mass, since `ℓ ≤ 1`
  have hden : (∫⁻ x in K, ell K δ x * gaussianWeight s x) ≤ ∫⁻ x in K, gaussianWeight s x := by
    refine lintegral_mono fun x => ?_
    calc ell K δ x * gaussianWeight s x ≤ 1 * gaussianWeight s x := by
          exact mul_le_mul_right' (ell_le_one K δ x) _
      _ = gaussianWeight s x := one_mul _
  rw [hnum, hscale]
  calc ENNReal.ofReal (1 / 2) * ∫⁻ x in K, ell K δ x * gaussianWeight s x
      ≤ ENNReal.ofReal (1 / 2) * ∫⁻ x in K, gaussianWeight s x := by gcongr
    _ ≤ ENNReal.ofReal (c ^ n) * ∫⁻ x in K, gaussianWeight s x := by
        have hcn : ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (c ^ n) :=
          ENNReal.ofReal_le_ofReal (by rw [hcdef]; exact half_le_one_sub_inv_two_mul_pow hn)
        exact mul_le_mul_right' hcn _
    _ ≤ ENNReal.ofReal (c ^ n) * ∫⁻ x in K, gaussianWeight (s / c ^ 2) x := by gcongr

section AxiomCheck

#print axioms Arlib.MarkovChains.half_le_one_sub_inv_two_mul_pow
#print axioms Arlib.MarkovChains.ell_eq_one_on_shrunken
#print axioms Arlib.MarkovChains.lintegral_one_sub_ell_shrunken_eq_zero
#print axioms Arlib.MarkovChains.half_le_speedy_shrunken

end AxiomCheck

end Arlib.MarkovChains
