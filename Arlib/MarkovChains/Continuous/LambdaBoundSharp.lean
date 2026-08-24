/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.LambdaBoundGaussian

/-!
# `lem:sigma-roundness`, and what is (and is not) proved of `lem:lambda-bound`

This file attacks Cousins–Vempala §6.4 "Bounding wasted steps"
(`1409.6011/vol3_journal.tex:827`–`:914`), which contains three results:

* `lem:lambda-bound` (`:853`) — for an `a`-rounded logconcave `f`,
  `λ(f) = (∫_K ℓ·f)/(∫_K f) ≥ 1 − 32·δ^{1/2}n^{1/4}/a^{1/2}`;
* `lem:sigma-roundness` (`:882`) — `N(0,σ²I)` restricted to a `K ⊇ Bₙ` is `min{σ,1}`-rounded;
* the unnamed corollary (`:906`) — if `δ ≤ min{σ,1}/(4096√n)` then `λ(f) ≥ 1/2`.

`Arlib.MarkovChains.Continuous.LambdaBoundGaussian` proved the *homothety* route and showed
it has a hard ceiling at `(1−δ)ⁿ`, which is exponentially small at the operative step size.
This file does not revisit that; it proves the second bullet outright, and is explicit about
exactly which piece of the first bullet remains an assumption.

## PROVED, unconditionally

**`lem:sigma-roundness` (`gaussian_rounded`, `gaussian_rounded_levelSet`).**  For any
`K ⊇ B(0,1)` in `ℝⁿ`, `n ≥ 2`, and any `σ > 0`, every level set `L` of the Gaussian weight
`γ_{σ²}` restricted to `K` contains the centred ball of radius `min{σ,1}·μ_f(L)`, where
`μ_f(L) = (∫_L γ_{σ²})/(∫_K γ_{σ²})`.  `K` need not be convex, bounded or even measurable.
`levelSet_gaussianWeightReal` proves that the level sets really are `K ∩ closedBall(0,r)`,
so the statement is about genuine level sets, not a stand-in.

The analytic core is `pow_mul_gaussianWeightReal_le`:

    `c^{n-1}·e^{-c²‖y‖²/(2s)} ≤ e^{-‖y‖²/(2s)}`  for `0 < c ≤ 1`, `n ≥ 2`, `‖y‖² ≤ s`,

whose one-line proof is `Real.log_le_sub_one_of_pos` applied to `c²`.  Combined with the
exact dilation identity `lintegral_gaussianWeight_smul_set` of `LambdaBoundGaussian` it gives
`∫_{B(0,cm)} γ_s ≤ c·∫_{B(0,m)} γ_s` (`lintegral_gaussianWeight_ball_le`) — the linear growth
of the Gaussian ball mass on `[0,σ]` that roundedness needs.  **This replaces the paper's
computation of `g''` on the radial profile `g(t) = ∫₀ᵗ x^{n-1}e^{-x²/2σ²}dx` and avoids
polar coordinates entirely**, which Mathlib supports only in Bochner form.

**`cv_error_term_le_half`** — the corollary's arithmetic, verified exactly: at
`δ ≤ a/(4096√n)` the error term `32·δ^{1/2}n^{1/4}/a^{1/2}` is at most `1/2` (because
`√4096 = 64`), and this is tight at equality.

**`lintegral_sublevel_le_ell_mul`** — the verifiable content of the pointwise display at
`:869`: for `f` supported in `K`,
`∫_{y ∈ B(x,δ), f(y) ≤ f(x)} f ≤ ℓ(x)·vol(δBₙ)·f(x)`.

## ASSUMED — read this before citing anything below

**`lem:lambda-bound` IS NOT PROVED HERE.**  `avgLocalConductance_ge_of_smoothing` and its
corollary `avgLocalConductance_ge_half_of_smoothing` carry **two** unproved hypotheses about
an abstract `fhat`:

1. `hpt : ∀ x, fhat x ≤ ell K δ x * f x` — Cousins–Vempala's pointwise step for the
   ball-convolution `f̂(x) = min_D (∫_{x+D} f)/vol(D)`, the minimum over convex `D ⊆ δBₙ` of
   half the ball's volume.
2. `hLov : ofReal c * ∫_K f ≤ ∫_K fhat` — **Lovász 2007, Lemma 6.3**, which supplies
   `c = 1 − 32·δ^{1/2}n^{1/4}/a^{1/2}` for an `a`-rounded logconcave `f`.  This is the deep
   external input and it is **not in this repository**.

So `avgLocalConductance_ge_half_of_smoothing` is a *conditional* `λ ≥ 1/2`: it says the
paper's two inputs suffice, and it checks the arithmetic.  It is **not** a proof of the
corollary at `:906`.

Both conditional statements come with a **non-vacuity witness**, because an unproved binder
that turns out to be unsatisfiable would make them worthless:

* `exists_smoothing_instance` — the cube `[−1,1]ⁿ` with `γ₁`, `δ = 1/2`, `fhat = ℓ·f`,
  `c = (1/2)ⁿ > 0`, `hLov` discharged by `gaussian_lambda_bound`.
* `exists_lambda_half_instance` — the harder one, for the `λ ≥ 1/2` bundle, where `hLov`
  is a genuine constraint (`hstep` forces `c ≥ 1/2`, so no degenerate `c ≤ 0` escape).
  Witness: `n = 2`, the square `[−1,1]²`, `σ = 1`, `δ = 1/(4096√2)` — `hstep` holds with
  *equality*, the extreme point of the corollary's range — and there the Cousins–Vempala
  constant is exactly `1/2`, discharged against `(1−δ)² ≥ 1/2`.

Hypothesis 1 was briefed as "a two-line argument once `f̂` exists".  It is not.  See the
paper-oracle note below.

**UPDATE — superseded in part.**  `Arlib/MarkovChains/Continuous/LovaszSmoothing.lean` defines
the ball-convolution `ballSmoothing` concretely and proves `f̂(x) ≤ 2·ℓ(x)·f(x)`
(`ballSmoothing_le_two_mul_ell_mul`), so hypothesis 1 is discharged **up to a factor 2** and
the two abstract binders over an arbitrary `fhat` collapse to the single binder `hLov`.  The
sharp constant is *not* available on that route, and the factor 2 is a genuine limit rather
than slack: the separating half-ball forced by convexity of the superlevel set need not carry
at most half of `K`'s share of the proposal ball, and `LovaszSmoothing.lean`'s docstring gives
an instance in `ℝ²` where the ratio tends to exactly 2.  A sharp proof must use a half on
which `f` *exceeds* `f(x)`, i.e. quantitative log-concavity, not merely convexity of superlevel
sets — which is more than CV's three displayed lines contain.  The downstream conclusions are
correspondingly `λ ≥ c/2` and `λ ≥ 1/4`, against the paper's `c` and `1/2`.

## Paper-oracle notes

* **The displayed chain proving the pointwise step at `:869` does not compose as printed.**
  Its first line reads `ℓ(x)f(x) = f(x)·(∫_{x+δBₙ} 1 dy)/vol(δBₙ)`, whose right side is just
  `f(x)`: the numerator must be `∫_{(x+δBₙ)∩K} 1 dy`.  Its second line divides by
  `∫_{y ∈ x+δBₙ : f(y) ≤ f(x)} 1 dy`; with that denominator the middle quantity is the
  *average* of `f` over the sublevel part of the ball, which is `≤ f(x)` and therefore is
  **not** in general `≤ ℓ(x)f(x)` — the claimed first inequality fails whenever `ℓ(x)` is
  small, which is exactly the regime the lemma is about.  With the denominator read as
  `vol(δBₙ)` the first inequality is correct (that is `lintegral_sublevel_le_ell_mul` here),
  but then the second inequality — passing to the minimum over convex half-volume `D` —
  needs a convexity/halving argument on the superlevel set `{f ≥ f(x)}` that the three
  displayed lines do not contain.  The statement is believed true; the printed proof is not
  a proof of it.
* **`lem:sigma-roundness` silently needs `n ≥ 2`.**  The paper's own proof uses it
  (`σ²(n−1) − t² ≥ 0`), but neither the lemma statement nor the corollary at `:906`
  records it.  It is a hypothesis of `gaussian_rounded` here.  (At `n = 1` the radial
  profile `x^{n−1} = 1` is flat rather than increasing, and the convexity argument the
  paper uses collapses; our route needs `n − 1 ≥ 1` at exactly the same point.)
* **CV's own bound is vacuous at their own step size.**  Already recorded in
  `LambdaBoundGaussian`: with `a = min{σ,1}` and `δ = σ/(8√n)` the bound reads
  `1 − 32/√8 ≈ −10.3`.  `cv_error_term_le_half` shows the operative constraint is
  `δ ≤ a/(4096√n)`, i.e. `512×` smaller than `σ/(8√n)`.

## Scope

There is no `def`, `structure`, `class` or `axiom` in this file; every declaration is a
`theorem`.  Nothing here is a conductance, mixing-time or polynomial-time statement.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1. The core scaling inequality -/

/-- **The core scaling inequality.**  For `0 < c ≤ 1`, dimension `n ≥ 2`, and a point `y`
inside the ball of radius `√s`,

    `c^{n-1} · e^{-c²‖y‖²/(2s)} ≤ e^{-‖y‖²/(2s)}`.

Equivalently `c^{n-1}·γ_{s/c²}(y) ≤ γ_s(y)`: the Jacobian factor `c^{n-1}` more than pays
for the widening of the variance from `s` to `s/c²`, *provided* `‖y‖² ≤ s`.

The proof is elementary.  Writing `ρ = ‖y‖²/(2s) ∈ [0,1/2]`, the claim after taking
logarithms is `(n-1)·log c ≤ (c²-1)·ρ`.  Since `log c ≤ 0` and `n-1 ≥ 1`, it suffices that
`log c ≤ (c²-1)·ρ`; since `c² - 1 ≤ 0` and `ρ ≤ 1/2`, it suffices that
`log c ≤ (c²-1)/2`, which is `Real.log_le_sub_one_of_pos` applied to `c²`.

This replaces Cousins–Vempala's convexity computation on the radial profile
`g(t) = ∫₀ᵗ x^{n-1}e^{-x²/2σ²}dx` (`1409.6011/vol3_journal.tex:889`), and in particular
avoids polar coordinates entirely. -/
theorem pow_mul_gaussianWeightReal_le {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hc1 : c ≤ 1)
    (hn : 2 ≤ n) {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ ^ 2 ≤ s) :
    c ^ (n - 1) * gaussianWeightReal (s / c ^ 2) y ≤ gaussianWeightReal s y := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  set ρ : ℝ := ‖y‖ ^ 2 / (2 * s) with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hρ2 : ρ ≤ 1 / 2 := by
    rw [hρdef, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * s)]
    linarith
  have hgs : gaussianWeightReal s y = Real.exp (-ρ) := by
    unfold gaussianWeightReal
    rw [hρdef, neg_div]
  have hgc : gaussianWeightReal (s / c ^ 2) y = Real.exp (-(c ^ 2 * ρ)) := by
    unfold gaussianWeightReal
    congr 1
    rw [hρdef]
    field_simp
  rw [hgs, hgc]
  have hstep1 : c ^ (n - 1) ≤ c := by
    calc c ^ (n - 1) ≤ c ^ 1 := pow_le_pow_of_le_one hc.le hc1 (by omega)
      _ = c := pow_one c
  have hlog : Real.log c ≤ (c ^ 2 - 1) / 2 := by
    have h := Real.log_le_sub_one_of_pos hc2
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hc21 : c ^ 2 ≤ 1 := by nlinarith
  have hprod : 0 ≤ (1 - c ^ 2) * (1 / 2 - ρ) := mul_nonneg (by linarith) (by linarith)
  have hkey : Real.log c - c ^ 2 * ρ ≤ -ρ := by nlinarith
  calc c ^ (n - 1) * Real.exp (-(c ^ 2 * ρ))
      ≤ c * Real.exp (-(c ^ 2 * ρ)) :=
        mul_le_mul_of_nonneg_right hstep1 (Real.exp_nonneg _)
    _ = Real.exp (Real.log c) * Real.exp (-(c ^ 2 * ρ)) := by rw [Real.exp_log hc]
    _ = Real.exp (Real.log c - c ^ 2 * ρ) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-ρ) := Real.exp_le_exp.2 hkey

/-- `ℝ≥0∞` form of `pow_mul_gaussianWeightReal_le`. -/
theorem pow_mul_gaussianWeight_le {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hc1 : c ≤ 1)
    (hn : 2 ≤ n) {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ ^ 2 ≤ s) :
    ENNReal.ofReal (c ^ (n - 1)) * gaussianWeight (s / c ^ 2) y ≤ gaussianWeight s y := by
  unfold gaussianWeight
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (pow_mul_gaussianWeightReal_le hs hc hc1 hn hy)

/-! ## 2. Concentric Gaussian ball masses are subadditive in the radius -/

/-- **The Gaussian mass of a concentric sub-ball is at most proportional to its radius.**
For `0 < c ≤ 1`, `n ≥ 2` and `m² ≤ s` (i.e. `m ≤ σ` for `s = σ²`),

    `∫_{B(0,cm)} γ_s ≤ c · ∫_{B(0,m)} γ_s`.

This is the whole analytic content of `lem:sigma-roundness`: the radial profile of the
Gaussian is *increasing* out to radius `σ√(n-1)`, so the mass of a ball grows at least
linearly in the radius on `[0,σ]`.  Proved from the exact dilation identity
`lintegral_gaussianWeight_smul_set` plus `pow_mul_gaussianWeight_le`. -/
theorem lintegral_gaussianWeight_ball_le {s c m : ℝ} (hs : 0 < s) (hc : 0 < c) (hc1 : c ≤ 1)
    (hn : 2 ≤ n) (hms : m ^ 2 ≤ s) :
    ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (c * m), gaussianWeight s x
      ≤ ENNReal.ofReal c * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) m, gaussianWeight s x := by
  have hsmul : c • ball (0 : EuclideanSpace ℝ (Fin n)) m = ball 0 (c * m) := by
    rw [_root_.smul_ball (ne_of_gt hc), smul_zero, Real.norm_eq_abs, abs_of_pos hc]
  have hcn : c ^ n = c * c ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  calc ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (c * m), gaussianWeight s x
      = ∫⁻ x in c • ball (0 : EuclideanSpace ℝ (Fin n)) m, gaussianWeight s x := by rw [hsmul]
    _ = ENNReal.ofReal (c ^ n)
          * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) m, gaussianWeight (s / c ^ 2) x :=
        lintegral_gaussianWeight_smul_set measurableSet_ball hc s
    _ = ENNReal.ofReal c * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) m,
          ENNReal.ofReal (c ^ (n - 1)) * gaussianWeight (s / c ^ 2) x := by
        rw [lintegral_const_mul _ (measurable_gaussianWeight _), hcn,
          ENNReal.ofReal_mul hc.le, mul_assoc]
    _ ≤ ENNReal.ofReal c * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) m, gaussianWeight s x := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_ball fun x hx => ?_)
        have hxm : ‖x‖ < m := by
          rw [mem_ball, dist_zero_right] at hx; exact hx
        have hx2 : ‖x‖ ^ 2 ≤ s := by nlinarith [norm_nonneg x]
        exact pow_mul_gaussianWeight_le hs hc hc1 hn hx2

/-! ## 3. `lem:sigma-roundness` -/

/-- The Gaussian mass of a small centred ball, relative to the mass of the whole body, is at
most `r/min{σ,1}`.  This is the quantitative form of `lem:sigma-roundness`. -/
theorem gaussian_ball_ratio_le {K : Set (EuclideanSpace ℝ (Fin n))}
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {σ : ℝ} (hσ : 0 < σ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) (hra : r ≤ min σ 1) :
    (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) r, gaussianWeight (σ ^ 2) x)
        / (∫⁻ x in K, gaussianWeight (σ ^ 2) x)
      ≤ ENNReal.ofReal (r / min σ 1) := by
  have ha0 : (0 : ℝ) < min σ 1 := lt_min hσ one_pos
  have ha1 : min σ 1 ≤ 1 := min_le_right _ _
  have haσ : min σ 1 ≤ σ := min_le_left _ _
  have has : min σ 1 ^ 2 ≤ σ ^ 2 := by nlinarith
  have hc0 : 0 < r / min σ 1 := div_pos hr ha0
  have hc1 : r / min σ 1 ≤ 1 := (div_le_one ha0).2 hra
  have hca : r / min σ 1 * min σ 1 = r := div_mul_cancel₀ r (ne_of_gt ha0)
  have hsub : ball (0 : EuclideanSpace ℝ (Fin n)) (min σ 1) ⊆ K :=
    (Metric.ball_subset_ball ha1).trans hball
  refine ENNReal.div_le_of_le_mul ?_
  calc ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) r, gaussianWeight (σ ^ 2) x
      = ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (r / min σ 1 * min σ 1),
          gaussianWeight (σ ^ 2) x := by rw [hca]
    _ ≤ ENNReal.ofReal (r / min σ 1)
          * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (min σ 1), gaussianWeight (σ ^ 2) x :=
        lintegral_gaussianWeight_ball_le (by positivity) hc0 hc1 hn has
    _ ≤ ENNReal.ofReal (r / min σ 1) * ∫⁻ x in K, gaussianWeight (σ ^ 2) x :=
        mul_le_mul' le_rfl (lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl)

/-- **`lem:sigma-roundness`, ball form** (`1409.6011/vol3_journal.tex:882`).

For a body `K` containing the unit ball, the Gaussian `N(0,σ²I)` restricted to `K` is
`min{σ,1}`-rounded: the set `K ∩ B(0,r)` contains a centred ball of radius
`min{σ,1} · μ_f(K ∩ B(0,r))`, where `μ_f` is the normalised restricted Gaussian measure.

`K` is *not* required to be convex, measurable, or bounded — only to contain `B(0,1)`.
The hypothesis `2 ≤ n` is genuinely used (it is what makes the radial profile increasing);
the paper states it inside the proof of `lem:sigma-roundness` but omits it from the
statements that consume it. -/
theorem gaussian_rounded_ball {K : Set (EuclideanSpace ℝ (Fin n))}
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {σ : ℝ} (hσ : 0 < σ) (hn : 2 ≤ n)
    (r : ℝ) :
    ball (0 : EuclideanSpace ℝ (Fin n))
        (min σ 1 * ((∫⁻ x in K ∩ ball (0 : EuclideanSpace ℝ (Fin n)) r,
              gaussianWeight (σ ^ 2) x) / (∫⁻ x in K, gaussianWeight (σ ^ 2) x)).toReal)
      ⊆ K ∩ ball (0 : EuclideanSpace ℝ (Fin n)) r := by
  have ha0 : (0 : ℝ) < min σ 1 := lt_min hσ one_pos
  have ha1 : min σ 1 ≤ 1 := min_le_right _ _
  set A : ℝ≥0∞ := ∫⁻ x in K ∩ ball (0 : EuclideanSpace ℝ (Fin n)) r,
    gaussianWeight (σ ^ 2) x with hAdef
  set T : ℝ≥0∞ := ∫⁻ x in K, gaussianWeight (σ ^ 2) x with hTdef
  have hμ0 : (0 : ℝ) ≤ (A / T).toReal := ENNReal.toReal_nonneg
  have hAT : A ≤ T :=
    lintegral_mono' (Measure.restrict_mono Set.inter_subset_left le_rfl) le_rfl
  have hμ1 : (A / T).toReal ≤ 1 := by
    have h : A / T ≤ 1 := ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hAT)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h
  have hle1 : min σ 1 * (A / T).toReal ≤ 1 := by nlinarith
  rcases le_or_gt (min σ 1 * (A / T).toReal) 0 with h0 | h0
  · rw [Metric.ball_eq_empty.2 h0]
    exact Set.empty_subset _
  have hμpos : 0 < (A / T).toReal := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hrpos : 0 < r := by
    by_contra hcon
    push_neg at hcon
    have hemp : ball (0 : EuclideanSpace ℝ (Fin n)) r = ∅ := Metric.ball_eq_empty.2 hcon
    have hA : A = 0 := by rw [hAdef, hemp, Set.inter_empty]; simp
    rw [hA, ENNReal.zero_div, ENNReal.toReal_zero] at hμpos
    exact lt_irrefl 0 hμpos
  have hsubr : min σ 1 * (A / T).toReal ≤ r := by
    rcases le_or_gt (min σ 1) r with hcase | hcase
    · calc min σ 1 * (A / T).toReal ≤ min σ 1 * 1 := by nlinarith
        _ = min σ 1 := mul_one _
        _ ≤ r := hcase
    · have hAle : A ≤ ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) r, gaussianWeight (σ ^ 2) x :=
        lintegral_mono' (Measure.restrict_mono Set.inter_subset_right le_rfl) le_rfl
      have hdiv : A / T ≤ ENNReal.ofReal (r / min σ 1) :=
        le_trans (ENNReal.div_le_div_right hAle T)
          (gaussian_ball_ratio_le hball hσ hn hrpos hcase.le)
      have hμr : (A / T).toReal ≤ r / min σ 1 :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) hdiv
      calc min σ 1 * (A / T).toReal ≤ min σ 1 * (r / min σ 1) := by nlinarith
        _ = r := by field_simp
  exact Set.subset_inter ((Metric.ball_subset_ball hle1).trans hball)
    (Metric.ball_subset_ball hsubr)

/-! ## 4. The same for the actual level sets, which are *closed* balls -/

/-- Spheres are Lebesgue-null, so restricting to `K ∩ closedBall` and to `K ∩ ball` gives the
same lower integral. -/
theorem lintegral_inter_closedBall_eq_ball (hn : 2 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (r : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    ∫⁻ x in K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r, f x
      = ∫⁻ x in K ∩ ball (0 : EuclideanSpace ℝ (Fin n)) r, f x := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hae : (closedBall (0 : EuclideanSpace ℝ (Fin n)) r : Set (EuclideanSpace ℝ (Fin n)))
      =ᵐ[volume] ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [Metric.closedBall_sdiff_ball]
      exact Measure.addHaar_sphere volume 0 r
    · rw [Set.sdiff_eq_empty.2 Metric.ball_subset_closedBall]
      exact measure_empty
  rw [Measure.restrict_congr_set ((Filter.EventuallyEq.refl _ K).inter hae)]

/-- **`lem:sigma-roundness`** (`1409.6011/vol3_journal.tex:882`), stated on the closed balls
that are the actual level sets of the truncated Gaussian.  For `K ⊇ B(0,1)` and `n ≥ 2`,

    `B(0, min{σ,1} · μ_f(L))  ⊆  L`,   `L = K ∩ closedBall(0,r)`,

`μ_f(L) = (∫_L γ_{σ²})/(∫_K γ_{σ²})` being the normalised restricted-Gaussian measure of `L`.
That is: *the Gaussian `N(0,σ²I)` restricted to `K` is `min{σ,1}`-rounded*. -/
theorem gaussian_rounded {K : Set (EuclideanSpace ℝ (Fin n))}
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {σ : ℝ} (hσ : 0 < σ) (hn : 2 ≤ n)
    (r : ℝ) :
    ball (0 : EuclideanSpace ℝ (Fin n))
        (min σ 1 * ((∫⁻ x in K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r,
              gaussianWeight (σ ^ 2) x) / (∫⁻ x in K, gaussianWeight (σ ^ 2) x)).toReal)
      ⊆ K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r := by
  rw [lintegral_inter_closedBall_eq_ball hn]
  exact (gaussian_rounded_ball hball hσ hn r).trans
    (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall)

/-- **The level sets of the truncated Gaussian are exactly the closed balls cut by `K`.**
For `0 < c ≤ 1`, `{x ∈ K : γ_s(x) ≥ c} = K ∩ closedBall(0, √(-2s·log c))`. -/
theorem levelSet_gaussianWeightReal {s : ℝ} (hs : 0 < s) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    {x : EuclideanSpace ℝ (Fin n) | x ∈ K ∧ c ≤ gaussianWeightReal s x}
      = K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n))
          (Real.sqrt (-(2 * s * Real.log c))) := by
  have hlog : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have h2s : (0 : ℝ) < 2 * s := by positivity
  have hR : 0 ≤ -(2 * s * Real.log c) := by nlinarith
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_closedBall, dist_zero_right]
  refine and_congr_right fun _ => ?_
  have hiff : c ≤ gaussianWeightReal s x ↔ ‖x‖ ^ 2 ≤ -(2 * s * Real.log c) := by
    rw [show gaussianWeightReal s x = Real.exp (-‖x‖ ^ 2 / (2 * s)) from rfl,
      ← Real.log_le_iff_le_exp hc, le_div_iff₀ h2s]
    constructor <;> intro h <;> nlinarith
  rw [hiff]
  constructor
  · intro h
    calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ Real.sqrt (-(2 * s * Real.log c)) := Real.sqrt_le_sqrt h
  · intro h
    have hsq := Real.sq_sqrt hR
    nlinarith [norm_nonneg x, Real.sqrt_nonneg (-(2 * s * Real.log c))]

/-- **`lem:sigma-roundness` in the paper's own words**: *every* level set `L` of the Gaussian
density restricted to `K` contains a ball of radius `min{σ,1}·μ_f(L)`. -/
theorem gaussian_rounded_levelSet {K : Set (EuclideanSpace ℝ (Fin n))}
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {σ : ℝ} (hσ : 0 < σ) (hn : 2 ≤ n)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ball (0 : EuclideanSpace ℝ (Fin n))
        (min σ 1
          * ((∫⁻ x in {x : EuclideanSpace ℝ (Fin n) | x ∈ K ∧ c ≤ gaussianWeightReal (σ ^ 2) x},
                gaussianWeight (σ ^ 2) x) / (∫⁻ x in K, gaussianWeight (σ ^ 2) x)).toReal)
      ⊆ {x : EuclideanSpace ℝ (Fin n) | x ∈ K ∧ c ≤ gaussianWeightReal (σ ^ 2) x} := by
  rw [levelSet_gaussianWeightReal (by positivity) hc hc1 K]
  exact gaussian_rounded hball hσ hn _

/-! ## 5. The verifiable content of Cousins–Vempala's pointwise step -/

/-- **`ℓ(x)·f(x)` dominates the sublevel mass of `f` on the proposal ball.**  For a density
`f` supported in `K`,

    `∫_{y ∈ B(x,δ), f(y) ≤ f(x)} f(y) dy  ≤  ℓ(x)·vol(δBₙ)·f(x)`.

This is the *provable* content of the three-line display at `vol3_journal.tex:869`: the
sublevel part of the proposal ball is inside `K` up to a null set where `f` vanishes, and
there `f ≤ f(x)`, so its mass is at most `f(x)·vol(B(x,δ) ∩ K)`.

**It is NOT `ℓ(x)f(x) ≥ f̂(x)`.**  See the module docstring: the paper's chain as printed
divides by `vol{y ∈ x+δBₙ : f(y) ≤ f(x)}` on the middle line, with which the chain does not
compose; and the step from here to the ball-convolution `f̂` (a minimum over *convex*
`D ⊆ δBₙ` of half the ball's volume) needs a convex-separation/halving argument that is not
formalised in this repository. -/
theorem lintegral_sublevel_le_ell_mul {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f)
    (hfK : ∀ y, y ∉ K → f y = 0) {δ : ℝ} (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | y ∈ ball x δ ∧ f y ≤ f x}, f y
      ≤ ell K δ x * volume (ball x δ) * f x := by
  have hb0 : volume (ball x δ) ≠ 0 := (Metric.measure_ball_pos volume x hδ).ne'
  have hbt : volume (ball x δ) ≠ ⊤ := measure_ball_lt_top.ne
  have hell : ell K δ x * volume (ball x δ) = volume (ball x δ ∩ K) := by
    rw [ell_apply, ENNReal.div_mul_cancel hb0 hbt]
  have hS : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | y ∈ ball x δ ∧ f y ≤ f x} :=
    measurableSet_ball.inter (hf measurableSet_Iic)
  have hbK : MeasurableSet (ball x δ ∩ K) := measurableSet_ball.inter hK
  rw [hell]
  calc ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | y ∈ ball x δ ∧ f y ≤ f x}, f y
      = ∫⁻ y, {y : EuclideanSpace ℝ (Fin n) | y ∈ ball x δ ∧ f y ≤ f x}.indicator f y :=
        (lintegral_indicator hS f).symm
    _ ≤ ∫⁻ y, (ball x δ ∩ K).indicator (fun _ => f x) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ {y : EuclideanSpace ℝ (Fin n) | y ∈ ball x δ ∧ f y ≤ f x}
        · rw [Set.indicator_of_mem hy]
          by_cases hyK : y ∈ K
          · rw [Set.indicator_of_mem (Set.mem_inter hy.1 hyK)]
            exact hy.2
          · rw [hfK y hyK]
            simp
        · rw [Set.indicator_of_notMem hy]
          simp
    _ = volume (ball x δ ∩ K) * f x := by
        rw [lintegral_indicator hbK, setLIntegral_const, mul_comm]

/-! ## 6. `lem:lambda-bound`, with Lovász 2007 Lemma 6.3 carried as an explicit hypothesis -/

/-- **`lem:lambda-bound` (`vol3_journal.tex:853`), conditional.**

Given *any* function `fhat` that (i) is pointwise dominated by `ℓ·f` and (ii) has
`∫_K fhat ≥ c·∫_K f`, the average local conductance satisfies `λ(f) ≥ c`.

Cousins–Vempala instantiate this with `fhat = f̂`, the ball-convolution smoothing; (i) is
their pointwise step (`:869`) and (ii) is **Lovász 2007, Lemma 6.3**, which gives
`c = 1 − 32·δ^{1/2}n^{1/4}/a^{1/2}` for an `a`-rounded logconcave `f`.

**Neither (i) nor (ii) is proved in this repository.**  Both are hypotheses of this theorem.
What *is* proved here is only that they suffice — which is the two-line part of CV's proof.
`exists_smoothing_instance` gives a non-vacuity witness for the hypothesis bundle. -/
theorem avgLocalConductance_ge_of_smoothing {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    {f fhat : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {c : ℝ}
    (hpt : ∀ x, fhat x ≤ ell K δ x * f x)
    (hLov : ENNReal.ofReal c * ∫⁻ x in K, f x ≤ ∫⁻ x in K, fhat x)
    (h0 : (∫⁻ x in K, f x) ≠ 0) (htop : (∫⁻ x in K, f x) ≠ ⊤) :
    ENNReal.ofReal c ≤ (∫⁻ x in K, ell K δ x * f x) / (∫⁻ x in K, f x) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop)]
  exact hLov.trans (lintegral_mono fun x => hpt x)

/-! ## 7. The `λ ≥ 1/2` corollary: the paper's arithmetic, verified -/

/-- **The corollary's arithmetic (`vol3_journal.tex:906`), verified exactly.**  At
`δ ≤ a/(4096√n)` the Cousins–Vempala error term `32·δ^{1/2}n^{1/4}/a^{1/2}` is at most
`1/2`, because `√4096 = 64` and `32/64 = 1/2`.  The bound is *tight* at `δ = a/(4096√n)`. -/
theorem cv_error_term_le_half {a δ : ℝ} (ha : 0 < a) (hn : 1 ≤ n)
    (hstep : δ ≤ a / (4096 * Real.sqrt n)) :
    32 * Real.sqrt δ * Real.sqrt (Real.sqrt n) / Real.sqrt a ≤ 1 / 2 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set q : ℝ := Real.sqrt (Real.sqrt (n : ℝ)) with hqdef
  have hq1 : 1 ≤ q := by
    rw [hqdef]
    have h1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hnR
    calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_le_sqrt h1
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq1
  have hq2 : q ^ 2 = Real.sqrt (n : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsa2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  -- `√δ ≤ √a / (64 q)`
  have hkey : Real.sqrt δ * (64 * q) ≤ Real.sqrt a := by
    have hrw : a / (4096 * Real.sqrt (n : ℝ)) = (Real.sqrt a / (64 * q)) ^ 2 := by
      rw [div_pow, mul_pow, hsa2, hq2]
      norm_num
    have h1 : Real.sqrt δ ≤ Real.sqrt a / (64 * q) := by
      calc Real.sqrt δ ≤ Real.sqrt (a / (4096 * Real.sqrt (n : ℝ))) := Real.sqrt_le_sqrt hstep
        _ = Real.sqrt ((Real.sqrt a / (64 * q)) ^ 2) := by rw [hrw]
        _ = Real.sqrt a / (64 * q) := Real.sqrt_sq (by positivity)
    rw [← le_div_iff₀ (by positivity : (0 : ℝ) < 64 * q)]
    exact h1
  rw [div_le_iff₀ hsa]
  nlinarith [Real.sqrt_nonneg δ, hq0]

/-- **The `λ ≥ 1/2` corollary (`vol3_journal.tex:906`), conditional on Lovász 2007 Lemma 6.3.**

With `a = min{σ,1}` — which is what `gaussian_rounded` supplies — and step size
`δ ≤ min{σ,1}/(4096√n)`, the Cousins–Vempala bound reads `λ(f) ≥ 1/2`.

The hypotheses `hpt` and `hLov` are exactly the two unproved inputs of
`avgLocalConductance_ge_of_smoothing`; `hLov` is Lovász 2007 Lemma 6.3, which is **not**
proved here. -/
theorem avgLocalConductance_ge_half_of_smoothing {K : Set (EuclideanSpace ℝ (Fin n))}
    {δ σ : ℝ} {f fhat : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hσ : 0 < σ) (hn : 1 ≤ n)
    (hstep : δ ≤ min σ 1 / (4096 * Real.sqrt n))
    (hpt : ∀ x, fhat x ≤ ell K δ x * f x)
    (hLov : ENNReal.ofReal
              (1 - 32 * Real.sqrt δ * Real.sqrt (Real.sqrt n) / Real.sqrt (min σ 1))
              * ∫⁻ x in K, f x ≤ ∫⁻ x in K, fhat x)
    (h0 : (∫⁻ x in K, f x) ≠ 0) (htop : (∫⁻ x in K, f x) ≠ ⊤) :
    ENNReal.ofReal (1 / 2) ≤ (∫⁻ x in K, ell K δ x * f x) / (∫⁻ x in K, f x) := by
  have ha : (0 : ℝ) < min σ 1 := lt_min hσ one_pos
  have harith := cv_error_term_le_half (a := min σ 1) ha hn hstep
  refine avgLocalConductance_ge_of_smoothing hpt ?_ h0 htop
  refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl) hLov

/-! ## 8. Non-vacuity of the hypothesis bundles -/

/-- The Gaussian mass of the cube is nonzero. -/
theorem lintegral_gaussianWeight_cube_ne_zero :
    (∫⁻ x in {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, gaussianWeight 1 x) ≠ 0 := by
  have hlow : ENNReal.ofReal (Real.exp (-(n : ℝ) / (2 * 1)))
        * volume {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}
      ≤ ∫⁻ x in {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, gaussianWeight 1 x := by
    calc ENNReal.ofReal (Real.exp (-(n : ℝ) / (2 * 1)))
          * volume {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}
        = ∫⁻ _ in {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1},
            ENNReal.ofReal (Real.exp (-(n : ℝ) / (2 * 1))) := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ _ := setLIntegral_mono' measurableSet_supNormCube fun x hx =>
            gaussianWeight_ge_on_cube one_pos hx
  intro h
  rw [h, le_zero_iff, mul_eq_zero] at hlow
  rcases hlow with h1 | h2
  · exact absurd (ENNReal.ofReal_eq_zero.1 h1) (not_le.2 (Real.exp_pos _))
  · exact volume_supNormCube_ne_zero h2

/-- The Gaussian mass of the cube is finite. -/
theorem lintegral_gaussianWeight_cube_ne_top :
    (∫⁻ x in {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, gaussianWeight 1 x) ≠ ⊤ := by
  have hle : (∫⁻ x in {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, gaussianWeight 1 x)
      ≤ volume {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} := by
    calc ∫⁻ x in {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, gaussianWeight 1 x
        ≤ ∫⁻ _ in {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, 1 :=
          lintegral_mono fun x => gaussianWeight_le_one one_pos x
      _ = volume {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} := setLIntegral_one _
  exact ne_top_of_le_ne_top volume_supNormCube_ne_top hle

/-- **Non-vacuity witness for `avgLocalConductance_ge_of_smoothing`.**  The cube `[-1,1]ⁿ`
with the Gaussian weight `γ₁`, `δ = 1/2`, `fhat = ℓ·f` and `c = (1/2)ⁿ` satisfies every
hypothesis, with `c > 0`.  So the conditional `lem:lambda-bound` above is not vacuously
quantified.

The witness is *not* degenerate in `ℓ`: on the cube the set `{ℓ = 1}` is exactly the
sub-cube `(1-δ)·[-1,1]ⁿ` (`ell_eq_one_setOf_cube` in `LambdaBoundGaussian`), so `ℓ < 1` on a
set of positive measure. -/
theorem exists_smoothing_instance :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
      (f fhat : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (c : ℝ),
      0 < c ∧ 0 < δ ∧ δ < 1 ∧
      (∀ x, fhat x ≤ ell K δ x * f x) ∧
      (ENNReal.ofReal c * ∫⁻ x in K, f x ≤ ∫⁻ x in K, fhat x) ∧
      (∫⁻ x in K, f x) ≠ 0 ∧ (∫⁻ x in K, f x) ≠ ⊤ ∧
      ENNReal.ofReal c ≤ (∫⁻ x in K, ell K δ x * f x) / (∫⁻ x in K, f x) :=
  ⟨{y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1}, (1 / 2 : ℝ),
    (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeight 1 x),
    (fun x : EuclideanSpace ℝ (Fin n) =>
      ell {y : EuclideanSpace ℝ (Fin n) | ∀ j, |y j| ≤ 1} (1 / 2) x * gaussianWeight 1 x),
    (1 - 1 / 2 : ℝ) ^ n, by positivity, by norm_num, by norm_num, fun x => le_rfl,
    gaussian_lambda_bound measurableSet_supNormCube convex_supNormCube ball_subset_cube
      (by norm_num) (by norm_num) one_pos,
    lintegral_gaussianWeight_cube_ne_zero, lintegral_gaussianWeight_cube_ne_top,
    avgLocalConductance_gaussian_ge measurableSet_supNormCube convex_supNormCube
      ball_subset_cube volume_supNormCube_ne_top (by norm_num) (by norm_num) one_pos⟩

/-- **Non-vacuity witness for `avgLocalConductance_ge_half_of_smoothing`** — the bundle that
carries Lovász 2007 Lemma 6.3.

This is the binder that matters: `avgLocalConductance_ge_half_of_smoothing` derives
`1/2 ≤ c` from `hstep`, so its `hLov` is a *genuine* constraint (`ofReal c ≥ ofReal (1/2)`),
not something a degenerate `c ≤ 0` could satisfy for free.  We exhibit an inhabitant in
dimension `n = 2`: the square `[-1,1]²`, `σ = 1`, `δ = 1/(4096·√2)` — which makes `hstep`
an *equality*, the extreme point of the corollary's range — `f = γ₁` and `fhat = ℓ·f`.  At
that `δ` the Cousins–Vempala constant is exactly `1/2`, and `hLov` is discharged by
`gaussian_lambda_bound`, whose `(1-δ)² ≥ 1/2` at `δ ≤ 1/4096`.

So the `λ ≥ 1/2` corollary above is a statement about a nonempty hypothesis set. -/
theorem exists_lambda_half_instance :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2))) (δ σ : ℝ)
      (f fhat : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞),
      0 < σ ∧ 0 < δ ∧
      δ ≤ min σ 1 / (4096 * Real.sqrt ((2 : ℕ) : ℝ)) ∧
      (∀ x, fhat x ≤ ell K δ x * f x) ∧
      (ENNReal.ofReal
          (1 - 32 * Real.sqrt δ * Real.sqrt (Real.sqrt ((2 : ℕ) : ℝ))
            / Real.sqrt (min σ 1)) * ∫⁻ x in K, f x ≤ ∫⁻ x in K, fhat x) ∧
      (∫⁻ x in K, f x) ≠ 0 ∧ (∫⁻ x in K, f x) ≠ ⊤ := by
  have h2R : ((2 : ℕ) : ℝ) = 2 := by norm_num
  set r : ℝ := Real.sqrt ((2 : ℕ) : ℝ) with hrdef
  have hr1 : (1 : ℝ) ≤ r := by
    have h : Real.sqrt 1 ≤ Real.sqrt ((2 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by rw [h2R]; norm_num)
    rw [hrdef]; simpa using h
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  set q : ℝ := Real.sqrt r with hqdef
  have hq2 : q ^ 2 = r := Real.sq_sqrt hr0.le
  have hq1 : (1 : ℝ) ≤ q := by
    have h : Real.sqrt 1 ≤ Real.sqrt r := Real.sqrt_le_sqrt hr1
    rw [hqdef]; simpa using h
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq1
  set δ : ℝ := 1 / (4096 * q ^ 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδsmall : δ ≤ 1 / 4096 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hδ1 : δ < 1 := by linarith
  -- `√δ = 1/(64q)`
  have hsd : Real.sqrt δ = 1 / (64 * q) := by
    have hsq : δ = (1 / (64 * q)) ^ 2 := by
      rw [hδdef, div_pow, mul_pow]
      norm_num
    rw [hsq]
    exact Real.sqrt_sq (by positivity)
  have hmin : min (1 : ℝ) 1 = 1 := min_self 1
  -- the Cousins–Vempala constant is exactly `1/2` at this step size
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hconst : 1 - 32 * Real.sqrt δ * q / Real.sqrt (min (1 : ℝ) 1) = 1 / 2 := by
    rw [hmin, Real.sqrt_one, hsd]
    field_simp
    ring
  refine ⟨{y : EuclideanSpace ℝ (Fin 2) | ∀ j, |y j| ≤ 1}, δ, 1,
    (fun x : EuclideanSpace ℝ (Fin 2) => gaussianWeight 1 x),
    (fun x : EuclideanSpace ℝ (Fin 2) =>
      ell {y : EuclideanSpace ℝ (Fin 2) | ∀ j, |y j| ≤ 1} δ x * gaussianWeight 1 x),
    one_pos, hδ0, ?_, fun x => le_rfl, ?_,
    lintegral_gaussianWeight_cube_ne_zero, lintegral_gaussianWeight_cube_ne_top⟩
  · rw [hmin, hδdef, hq2]
  · rw [hconst]
    refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      (gaussian_lambda_bound measurableSet_supNormCube convex_supNormCube ball_subset_cube
        hδ0 hδ1 one_pos)
    show (1 : ℝ) / 2 ≤ (1 - δ) ^ 2
    nlinarith [hδ0, hδsmall]

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.pow_mul_gaussianWeightReal_le
#print axioms Arlib.MarkovChains.pow_mul_gaussianWeight_le
#print axioms Arlib.MarkovChains.lintegral_gaussianWeight_ball_le
#print axioms Arlib.MarkovChains.gaussian_ball_ratio_le
#print axioms Arlib.MarkovChains.gaussian_rounded_ball
#print axioms Arlib.MarkovChains.lintegral_inter_closedBall_eq_ball
#print axioms Arlib.MarkovChains.gaussian_rounded
#print axioms Arlib.MarkovChains.levelSet_gaussianWeightReal
#print axioms Arlib.MarkovChains.gaussian_rounded_levelSet
#print axioms Arlib.MarkovChains.lintegral_sublevel_le_ell_mul
#print axioms Arlib.MarkovChains.avgLocalConductance_ge_of_smoothing
#print axioms Arlib.MarkovChains.cv_error_term_le_half
#print axioms Arlib.MarkovChains.avgLocalConductance_ge_half_of_smoothing
#print axioms Arlib.MarkovChains.lintegral_gaussianWeight_cube_ne_zero
#print axioms Arlib.MarkovChains.lintegral_gaussianWeight_cube_ne_top
#print axioms Arlib.MarkovChains.exists_smoothing_instance
#print axioms Arlib.MarkovChains.exists_lambda_half_instance
