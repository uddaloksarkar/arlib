/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.ZLogconcave
import Arlib.Convexity.GaussianCooling.Chain
import Arlib.Convexity.GaussianCooling.Schedule
import Arlib.Probability.TV

/-!
# `hphase_var` for a *sampled* phase: transporting the second-moment bound across TV

`Arlib.GaussianCooling.fixed_var_bound_ratio_indicator` proves the Cousins–Vempala
per-phase second-moment bound **at an exact sample** from the phase density, with no
assumed input: for `K` convex and measurable and the fixed cooling rate
`σᵢ₊₁² = σᵢ²(1 + 1/n)`,

  `E_π(W²) ≤ (1 + 2/n) · E_π(W)²`,

where `π` is the phase-`i` density `∝ 1_K(x) e^{−‖x‖²/(2σᵢ²)}` and `W = coolRatio i` is the
pointwise phase ratio.

The algorithm never has an exact sample. It has a draw from a law `ν` that a Markov chain
has reached, known only to be within total variation `ε` of `π`. This file does the
**transport**: it converts the bound at `π` into a bound at `ν`, in exactly the shape the
volume algorithm's `hphase_var` hypothesis consumes,

  `∫ ω, W(ω)² ∂μ ≤ (1 + κ/m) · (∫ ω, W(ω) ∂μ)²`,

with the TV error `ε` appearing explicitly in the hypotheses.

## The three things the transport has to get right

**1. `Arlib.TVLe.integral_le` is for `[0,1]`-valued observables; `W²` is not one.**
The rescaling is explicit: `W/B` and `W²/B²` are `[0,1]`-valued as soon as `0 ≤ W ≤ B`,
and the two transport lemmas below (`abs_integral_sub_le_of_tvLe`,
`abs_integral_sq_sub_le_of_tvLe`) carry the factors `B` and `B²` out front. **A bound `B`
is genuinely needed and is a real hypothesis, not a formality:** `coolRatio` is
`e^{‖x‖²/2·(1/σᵢ² − 1/σᵢ₊₁²)}`, which is *unbounded on an unbounded body*.
`coolRatio_le_exp` gives `B = e^{R²/(2σᵢ²)}` on a body contained in `R·Bₙ`, and there is
no bound at all without such a radius. See the scope section below.

**2. The bound is on a ratio of moments, so the TV error enters twice, in opposite
directions.** The numerator needs an **upper** transport `E_ν(W²) ≤ E_π(W²) + B²ε`; the
denominator needs a **lower** transport `E_ν(W) ≥ E_π(W) − Bε`, and then a proof that
`E_π(W) − Bε ≥ 0` so that squaring is monotone. A one-sided transport is not enough, which
is why `abs_integral_sub_le_of_tvLe` is stated with an absolute value and both halves are
used.

**3. `1 + 2/n` is not `1 + κ/m`.** The exact-sample constant is `1 + 2/n`; the hypothesis
asks for `1 + κ/m` with `κ = varBudget ε` and `m` the number of phases. The transport
consumes a *strict* slack `s > 0` between the two — the TV error has to fit somewhere.
`fixedRate_meets_budget_iff` records the exact relation (`2m ≤ nκ`), and
`geomSchedule_total_cooling_lt` shows what that costs: **at the fixed rate `α = 1/n` a
schedule meeting the budget can cool by a total factor of less than `1.1`**, i.e. it
cannot cool at all. This is a genuine obstruction, not a bookkeeping loss; see
"What this does *not* give" below.

## Main results

* `Arlib.GaussianCooling.abs_integral_sub_le_of_tvLe` — first-moment transport, `B·ε`.
* `Arlib.GaussianCooling.abs_integral_sq_sub_le_of_tvLe` — second-moment transport, `B²·ε`.
* `Arlib.GaussianCooling.sq_moment_le_of_tvLe` — **the headline.** From an exact-law bound
  `E_π(W²) ≤ C·E_π(W)²`, a bound `0 ≤ W ≤ B`, a slack `s ≥ 0` and the explicit smallness
  condition `ε·B²·(1 + 2(C+s)) ≤ s·E_π(W)²`, conclude `E_ν(W²) ≤ (C+s)·E_ν(W)²`.
* `Arlib.GaussianCooling.sq_moment_le_of_tvLe_map` — the same through a sampling map
  `X : Ω → EuclSpace n`, i.e. literally in `hphase_var`'s shape over the algorithm's own
  probability space.
* `Arlib.GaussianCooling.sq_moment_le_of_tvLe_exact` — non-vacuity: at `ε = 0` and `s = 0`
  the conclusion is the exact-law bound with no loss.
* `Arlib.GaussianCooling.coolRatio_le_exp` — `coolRatio m σsq i x ≤ e^{R²/(2σᵢ²)}` for
  `‖x‖ ≤ R`; the bound `B` above, for the observable this is all about.
* `Arlib.GaussianCooling.fixedRate_meets_budget_iff` — `1 + 2/n ≤ 1 + κ/m ↔ 2m ≤ nκ`.
* `Arlib.GaussianCooling.geomSchedule_total_cooling_lt` — the obstruction: `2m ≤ n·varBudget ε`
  and `ε ≤ 1` force `(1 + 1/n)^m < 11/10`.

## Scope: what this does *not* give

This file is **transport only**. It does not:

* produce the TV bound `ε`. Nothing here says a ball walk or a Metropolis chain is within
  `ε` of the phase density; that is conductance/mixing, and is not touched.
* remove the radius hypothesis. The observable `coolRatio` is unbounded on an unbounded
  body, so the bound `B` must come from `K ⊆ R·Bₙ`.
  `Ttc.VolumeAlgorithm.cousinsVempala`'s `hphase_var` is quantified over every `K` with
  `ball 0 1 ⊆ K` and `volume K ≠ ⊤`. Those two *do* imply `K` is bounded — a convex set
  containing a ball and an unbounded direction contains a cone of infinite volume — but
  they expose no **radius**, and `R` is not a bookkeeping detail here: it enters the
  transport quantitatively, through `B = e^{R²/(2σᵢ²)}` and hence through the smallness
  condition on `ε`, which reads roughly `ε ≲ s·E(W)²·e^{−R²/σᵢ²}`. Instantiating
  `hphase_var` through this file therefore needs `cousinsVempala` to carry an explicit
  radius parameter (the one the rounding step produces) that it currently does not have.
  This is reported, not patched: no file under `Ttc/` is edited here.
* reconcile `1 + 2/n` with `1 + κ/m`. It does not, at the fixed rate — see
  `geomSchedule_total_cooling_lt`. The general-`α` input
  `Arlib.GaussianCooling.G_mul_G_le_of_zLogconcave` (constant `(1−α²)^{−(n+1)}`) is what a
  schedule meeting the budget has to be built on; that schedule is not constructed here.

Nothing below is stated as an unproved `Prop` and no new hypothesis class is introduced:
every declaration is either explicit data or a theorem proved outright, and the exact-law
input is always an ordinary hypothesis of the theorem that uses it, discharged for the
convex-body case by `fixed_var_bound_ratio_indicator`.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal

/-! ## Integrability of a bounded observable -/

section Transport

variable {Ω : Type*} [MeasurableSpace Ω] {μ π : Measure Ω} {ε : ℝ≥0∞}

/-- A nonnegative measurable function bounded by `B` is integrable against a finite
measure. (`Arlib.integrable_of_forall_mem_Icc` is the `B = 1` case.) -/
theorem integrable_of_bounded [IsFiniteMeasure μ] {W : Ω → ℝ} {B : ℝ}
    (hWm : Measurable W) (hW0 : ∀ x, 0 ≤ W x) (hWB : ∀ x, W x ≤ B) :
    Integrable W μ := by
  refine Integrable.mono' (integrable_const B) hWm.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hW0 x)]
  exact hWB x

/-- The mean of an observable bounded by `B` is at most `B`. -/
theorem integral_le_bound [IsProbabilityMeasure μ] {W : Ω → ℝ} {B : ℝ}
    (hWm : Measurable W) (hW0 : ∀ x, 0 ≤ W x) (hWB : ∀ x, W x ≤ B) :
    ∫ x, W x ∂μ ≤ B := by
  have hint : Integrable W μ := integrable_of_bounded (μ := μ) hWm hW0 hWB
  have h := integral_mono hint (integrable_const (μ := μ) B) hWB
  rwa [integral_const, measureReal_univ_eq_one, one_smul] at h

/-! ## The two transport steps

`Arlib.TVLe.integral_le` bounds `|∫ f ∂μ − ∫ f ∂π|` by `ε` for `f` with values in `[0,1]`.
Neither `W` nor `W²` is `[0,1]`-valued, so each is rescaled by its own bound before the
lemma is applied and the scale is carried back out. -/

/-- **First-moment transport.** For `0 ≤ W ≤ B`, a TV bound `ε` costs `B·ε` on the mean.
Both directions are needed downstream: the upper one is never used, the *lower* one is
what keeps the denominator of `E(W²)/E(W)²` away from `0`. -/
theorem abs_integral_sub_le_of_tvLe [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (h : TVLe μ π ε) (hεtop : ε ≠ ⊤) {B : ℝ} (hB : 0 < B) {W : Ω → ℝ}
    (hWm : Measurable W) (hW0 : ∀ x, 0 ≤ W x) (hWB : ∀ x, W x ≤ B) :
    |∫ x, W x ∂μ - ∫ x, W x ∂π| ≤ B * ε.toReal := by
  have key := h.integral_le hεtop (f := fun x => W x / B) (hWm.div_const B)
    (fun x => div_nonneg (hW0 x) hB.le) (fun x => (div_le_one hB).2 (hWB x))
  simp only [integral_div, div_sub_div_same] at key
  rw [abs_div, abs_of_pos hB, div_le_iff₀ hB] at key
  linarith [key]

/-- **Second-moment transport.** For `0 ≤ W ≤ B`, a TV bound `ε` costs `B²·ε` on the second
moment. The observable rescaled to `[0,1]` is `W²/B²`, which is where the `B²` comes
from. -/
theorem abs_integral_sq_sub_le_of_tvLe [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (h : TVLe μ π ε) (hεtop : ε ≠ ⊤) {B : ℝ} (hB : 0 < B) {W : Ω → ℝ}
    (hWm : Measurable W) (hW0 : ∀ x, 0 ≤ W x) (hWB : ∀ x, W x ≤ B) :
    |∫ x, W x ^ 2 ∂μ - ∫ x, W x ^ 2 ∂π| ≤ B ^ 2 * ε.toReal := by
  have hB2 : (0 : ℝ) < B ^ 2 := by positivity
  have hsq : ∀ x, W x ^ 2 ≤ B ^ 2 := fun x => by nlinarith [hW0 x, hWB x]
  have key := h.integral_le hεtop (f := fun x => W x ^ 2 / B ^ 2)
    ((hWm.pow_const 2).div_const (B ^ 2))
    (fun x => div_nonneg (by positivity) hB2.le)
    (fun x => (div_le_one hB2).2 (hsq x))
  simp only [integral_div, div_sub_div_same] at key
  rw [abs_div, abs_of_pos hB2, div_le_iff₀ hB2] at key
  linarith [key]

/-! ## The headline: the second-moment bound at the sampled law -/

/-- **The transported per-phase second-moment bound.**

Given

* a sampled law `μ` within total variation `ε` of the exact phase law `π`;
* an observable `W` with `0 ≤ W ≤ B` everywhere (for `coolRatio` this needs a bounded body
  — see `coolRatio_le_exp`);
* the **exact-law** bound `E_π(W²) ≤ C · E_π(W)²` (for a convex body this is
  `fixed_var_bound_ratio_indicator`, with `C = 1 + 2/n`);
* a slack `s ≥ 0` and the explicit smallness condition
  `ε · B² · (1 + 2(C+s)) ≤ s · E_π(W)²`,

the same bound holds at the sampled law with constant `C + s`:

  `E_μ(W²) ≤ (C + s) · E_μ(W)²`.

The two transport steps enter in opposite directions: the numerator upward
(`abs_integral_sq_sub_le_of_tvLe`), the denominator downward
(`abs_integral_sub_le_of_tvLe`), and the smallness condition is exactly what makes the
downward one leave `E_π(W) − Bε ≥ 0` so the square can be compared. -/
theorem sq_moment_le_of_tvLe [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (h : TVLe μ π ε) (hεtop : ε ≠ ⊤) {B : ℝ} (hB : 0 < B) {W : Ω → ℝ}
    (hWm : Measurable W) (hW0 : ∀ x, 0 ≤ W x) (hWB : ∀ x, W x ≤ B)
    {C s : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hexact : ∫ x, W x ^ 2 ∂π ≤ C * (∫ x, W x ∂π) ^ 2)
    (hslack : ε.toReal * (B ^ 2 * (1 + 2 * (C + s))) ≤ s * (∫ x, W x ∂π) ^ 2) :
    ∫ x, W x ^ 2 ∂μ ≤ (C + s) * (∫ x, W x ∂μ) ^ 2 := by
  set δ : ℝ := ε.toReal with hδdef
  set M : ℝ := ∫ x, W x ∂π with hMdef
  set N : ℝ := ∫ x, W x ∂μ with hNdef
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ M := integral_nonneg hW0
  have hMB : M ≤ B := integral_le_bound hWm hW0 hWB
  have hD0 : 0 ≤ C + s := by linarith
  -- the two transport steps
  have h1 : M - B * δ ≤ N := by
    have := abs_integral_sub_le_of_tvLe h hεtop hB hWm hW0 hWB
    rw [abs_sub_le_iff] at this
    linarith [this.2]
  have h2 : ∫ x, W x ^ 2 ∂μ ≤ (∫ x, W x ^ 2 ∂π) + B ^ 2 * δ := by
    have := abs_integral_sq_sub_le_of_tvLe h hεtop hB hWm hW0 hWB
    rw [abs_sub_le_iff] at this
    linarith [this.1]
  -- the denominator stays nonnegative: `2 B δ ≤ M`
  have hMB2 : M * B ≤ B ^ 2 := by nlinarith
  have hbase : δ * (B ^ 2 * (1 + 2 * (C + s))) ≤ s * (M * B) := by
    refine hslack.trans ?_
    have hsq' : M ^ 2 ≤ M * B := by nlinarith
    nlinarith
  have hlow : 0 ≤ M - B * δ := by
    have hδB2 : 2 * s * (δ * B ^ 2) ≤ δ * (B ^ 2 * (1 + 2 * (C + s))) := by
      have hnn : (0 : ℝ) ≤ δ * B ^ 2 := by positivity
      nlinarith
    have hmul : B * (s * (2 * (δ * B))) ≤ B * (s * M) := by nlinarith
    have hcancel : s * (2 * (δ * B)) ≤ s * M := le_of_mul_le_mul_left hmul hB
    rcases hs.eq_or_lt with hs0 | hs0
    · -- no slack: the smallness condition forces `ε = 0`
      have hpos : (0 : ℝ) < B ^ 2 * (1 + 2 * (C + s)) := by positivity
      have hz : δ * (B ^ 2 * (1 + 2 * (C + s))) ≤ 0 := by
        rw [← hs0] at hslack; nlinarith
      have hδ0' : δ ≤ 0 := nonpos_of_mul_nonpos_right (by linarith) hpos
      have hδz : δ = 0 := le_antisymm hδ0' hδ0
      rw [hδz]; linarith
    · have := le_of_mul_le_mul_left hcancel hs0
      linarith
  -- the arithmetic that closes the ratio
  have hnum : C * M ^ 2 + B ^ 2 * δ ≤ (C + s) * (M - B * δ) ^ 2 := by
    have hcoef : (0 : ℝ) ≤ 2 * (C + s) * δ := by positivity
    have hcross := mul_le_mul_of_nonneg_left hMB2 hcoef
    have hsquare : (0 : ℝ) ≤ (C + s) * (δ ^ 2 * B ^ 2) := by positivity
    have hexp : (C + s) * (M - B * δ) ^ 2
        = (C + s) * M ^ 2 - 2 * (C + s) * δ * (M * B) + (C + s) * (δ ^ 2 * B ^ 2) := by
      ring
    rw [hexp]
    nlinarith [hslack, hcross, hsquare]
  have hsq : (M - B * δ) ^ 2 ≤ N ^ 2 := by nlinarith
  calc ∫ x, W x ^ 2 ∂μ ≤ (∫ x, W x ^ 2 ∂π) + B ^ 2 * δ := h2
    _ ≤ C * M ^ 2 + B ^ 2 * δ := by linarith
    _ ≤ (C + s) * (M - B * δ) ^ 2 := hnum
    _ ≤ (C + s) * N ^ 2 := by nlinarith

/-- **Non-vacuity of the transport** (`CLAUDE.md` §11): at `ε = 0` and slack `s = 0` the
smallness condition is `0 ≤ 0` and the conclusion is the exact-law bound verbatim, with no
degradation of the constant. So `sq_moment_le_of_tvLe` is not vacuously guarded. -/
theorem sq_moment_le_of_tvLe_exact [IsProbabilityMeasure μ] {B : ℝ} (hB : 0 < B)
    {W : Ω → ℝ} (hWm : Measurable W) (hW0 : ∀ x, 0 ≤ W x) (hWB : ∀ x, W x ≤ B)
    {C : ℝ} (hC : 0 ≤ C) (hexact : ∫ x, W x ^ 2 ∂μ ≤ C * (∫ x, W x ∂μ) ^ 2) :
    ∫ x, W x ^ 2 ∂μ ≤ (C + 0) * (∫ x, W x ∂μ) ^ 2 :=
  sq_moment_le_of_tvLe (ε := 0) (TVLe.refl μ) (by simp) hB hWm hW0 hWB hC le_rfl hexact
    (by simp)

end Transport

/-! ## Through a sampling map: `hphase_var`'s own shape

The volume algorithm's `hphase_var` is a statement about `∫ ω, W(ω)^k ∂μ` on the
algorithm's probability space `Ω`, where `W ω = f (X ω)` for a sample `X : Ω → EuclSpace n`
and the phase score `f`. The TV bound, on the other hand, is between the *law* `μ.map X` of
the sample and the exact phase law. This is the bridge. -/

section Map

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {π : Measure (EuclSpace n)} {ε : ℝ≥0∞}

/-- **`hphase_var`'s shape.** With `X` the phase sample, `f` the phase score bounded in
`[0, B]`, the law of `X` within total variation `ε` of the exact phase law `π`, and the
exact-law second-moment bound with constant `C`, the score `W = f ∘ X` obeys

  `∫ ω, W(ω)² ∂μ ≤ (C + s) · (∫ ω, W(ω) ∂μ)²`

on the algorithm's own probability space. Take `C = 1 + 2/n` (from
`fixed_var_bound_ratio_indicator`) and `C + s = 1 + κ/m` to land the hypothesis; the
relation between the two constants is `fixedRate_meets_budget_iff`. -/
theorem sq_moment_le_of_tvLe_map [IsProbabilityMeasure π]
    {X : Ω → EuclSpace n} (hX : Measurable X)
    (h : TVLe (μ.map X) π ε) (hεtop : ε ≠ ⊤) {B : ℝ} (hB : 0 < B)
    {f : EuclSpace n → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    {C s : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hexact : ∫ x, f x ^ 2 ∂π ≤ C * (∫ x, f x ∂π) ^ 2)
    (hslack : ε.toReal * (B ^ 2 * (1 + 2 * (C + s))) ≤ s * (∫ x, f x ∂π) ^ 2) :
    ∫ ω, f (X ω) ^ 2 ∂μ ≤ (C + s) * (∫ ω, f (X ω) ∂μ) ^ 2 := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hmap1 : ∫ x, f x ∂(μ.map X) = ∫ ω, f (X ω) ∂μ :=
    integral_map hX.aemeasurable hfm.aestronglyMeasurable
  have hmap2 : ∫ x, f x ^ 2 ∂(μ.map X) = ∫ ω, f (X ω) ^ 2 ∂μ :=
    integral_map hX.aemeasurable (hfm.pow_const 2).aestronglyMeasurable
  have := sq_moment_le_of_tvLe h hεtop hB hfm hf0 hfB hC hs hexact hslack
  rwa [hmap1, hmap2] at this

end Map

/-! ## The bound `B`: `coolRatio` on a bounded body

The transport needs `0 ≤ W ≤ B` **everywhere**, and this is where a real hypothesis
appears. `coolRatio m σsq i x = e^{‖x‖²/2·(1/σᵢ² − 1/σᵢ₊₁²)}` (and `e^{‖x‖²/(2σᵢ²)}` at the
terminal step) grows without bound in `‖x‖`, so there is **no** bound on an unbounded body.
On a body inside `R·Bₙ` the single crude bound `e^{R²/(2σᵢ²)}` covers all three cases of
`coolRatio` at once, with no monotonicity assumption on the schedule. -/

section Bound

variable {n : ℕ}

/-- **`coolRatio` is bounded on a bounded body.** For `‖x‖ ≤ R` and a positive schedule,

  `coolRatio m σsq i x ≤ e^{R²/(2σᵢ²)}`,

uniformly in `i` and covering all three regimes (interior step, terminal step, past the
end). No monotonicity of `σsq` is needed: if the exponent `1/σᵢ² − 1/σᵢ₊₁²` happens to be
negative the ratio is below `1` and the bound is trivial. -/
theorem coolRatio_le_exp {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j) (i : ℕ) {R : ℝ}
    {x : EuclSpace n} (hx : ‖x‖ ≤ R) :
    coolRatio m σsq i x ≤ Real.exp (R ^ 2 / (2 * σsq i)) := by
  have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hR0 : (0 : ℝ) ≤ R := hx0.trans hx
  have hxsq : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith
  have hi0 := hσ i
  have hi1 := hσ (i + 1)
  by_cases hi : i < m
  · by_cases hi' : i + 1 < m
    · rw [coolRatio_of_succ_lt hi']
      refine Real.exp_le_exp.2 ?_
      rcases le_or_gt 0 (1 / σsq i - 1 / σsq (i + 1)) with hc | hc
      · have hstep : ‖x‖ ^ 2 / 2 * (1 / σsq i - 1 / σsq (i + 1))
            ≤ R ^ 2 / 2 * (1 / σsq i - 1 / σsq (i + 1)) := by nlinarith
        have hstep2 : R ^ 2 / 2 * (1 / σsq i - 1 / σsq (i + 1))
            ≤ R ^ 2 / (2 * σsq i) := by
          have hinv : (0 : ℝ) < 1 / σsq (i + 1) := by positivity
          have : R ^ 2 / 2 * (1 / σsq i - 1 / σsq (i + 1)) ≤ R ^ 2 / 2 * (1 / σsq i) := by
            nlinarith
          have heq : R ^ 2 / 2 * (1 / σsq i) = R ^ 2 / (2 * σsq i) := by
            field_simp
          linarith [heq ▸ this]
        linarith
      · have : ‖x‖ ^ 2 / 2 * (1 / σsq i - 1 / σsq (i + 1)) ≤ 0 := by nlinarith
        have hpos : (0 : ℝ) ≤ R ^ 2 / (2 * σsq i) := by positivity
        linarith
    · rw [coolRatio_of_last hi (not_lt.1 hi')]
      refine Real.exp_le_exp.2 ?_
      gcongr
  · rw [coolRatio_of_ge (not_lt.1 hi)]
    exact Real.one_le_exp (by positivity)

/-- The phase score as a globally bounded observable: `coolRatio` cut off outside the body.
On `K` it agrees with `coolRatio` (`phaseScore_of_mem`), and globally it lies in
`[0, e^{R²/(2σᵢ²)}]` once `K ⊆ R·Bₙ`. Cutting off outside the body is what makes the
`[0,1]`-rescaling of `Arlib.TVLe.integral_le` available at all. -/
noncomputable def phaseScore (m : ℕ) (σsq : ℕ → ℝ) (K : Set (EuclSpace n)) (i : ℕ) :
    EuclSpace n → ℝ :=
  Set.indicator K (coolRatio m σsq i)

theorem phaseScore_of_mem {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    {x : EuclSpace n} (hx : x ∈ K) :
    phaseScore m σsq K i x = coolRatio m σsq i x :=
  Set.indicator_of_mem hx _

theorem phaseScore_nonneg (m : ℕ) (σsq : ℕ → ℝ) (K : Set (EuclSpace n)) (i : ℕ)
    (x : EuclSpace n) : 0 ≤ phaseScore m σsq K i x :=
  Set.indicator_nonneg (fun y _ => (coolRatio_pos m σsq i y).le) x

/-- The bound `B` for the transport, in the form the theorems above consume. -/
theorem phaseScore_le {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} {R : ℝ} (hK : K ⊆ closedBall (0 : EuclSpace n) R) (i : ℕ)
    (x : EuclSpace n) :
    phaseScore m σsq K i x ≤ Real.exp (R ^ 2 / (2 * σsq i)) := by
  by_cases hx : x ∈ K
  · rw [phaseScore_of_mem hx]
    exact coolRatio_le_exp hσ i (by simpa using mem_closedBall_zero_iff.1 (hK hx))
  · rw [phaseScore, Set.indicator_of_notMem hx]
    exact (Real.exp_pos _).le

theorem measurable_phaseScore {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)}
    (hKm : MeasurableSet K) (i : ℕ) : Measurable (phaseScore m σsq K i) := by
  have hc : Measurable (coolRatio (n := n) m σsq i) :=
    (continuous_coolWeight m σsq (i + 1)).measurable.div
      (continuous_coolWeight m σsq i).measurable
  exact Measurable.indicator hc hKm

end Bound

/-! ## The exact phase law, and the exact-sample bound it satisfies

The transport above takes the exact-law bound `E_π(W²) ≤ C·E_π(W)²` as an input. For a
convex body that input is **not** an assumption: it is
`fixed_var_bound_indicator`, with `C = 1 + 2/n`. This section builds the exact phase law
`π` as a genuine measure and discharges the input against it, so that nothing in the chain
is asserted without proof. -/

section ExactLaw

variable {n : ℕ}

/-- **The exact phase-`i` law**: Lebesgue measure on `K`, reweighted by the normalized
phase density `coolWeight i / chain i`. This is the distribution an exact sampler would
return and the one a Markov chain is only TV-close to. -/
noncomputable def coolLaw (m : ℕ) (σsq : ℕ → ℝ) (K : Set (EuclSpace n)) (i : ℕ) :
    Measure (EuclSpace n) :=
  (volume.restrict K).withDensity
    (fun x => ENNReal.ofReal (coolWeight m σsq i x / chain m σsq K i))

/-- The phase law is a probability measure: this is `coolDensity_integral_eq_one` moved
across `ofReal_integral_eq_lintegral_ofReal`. -/
theorem coolLaw_isProbabilityMeasure {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (i : ℕ) : IsProbabilityMeasure (coolLaw m σsq K i) := by
  have hchain := chain_pos (m := m) hσ hball hfin i
  have hint : IntegrableOn (fun x => coolWeight m σsq i x / chain m σsq K i) K volume :=
    (integrableOn_coolWeight (hσ i) hfin).div_const _
  have hnn : (0 : EuclSpace n → ℝ) ≤ᵐ[volume.restrict K]
      fun x => coolWeight m σsq i x / chain m σsq K i :=
    Filter.Eventually.of_forall fun x =>
      div_nonneg (coolWeight_pos m σsq i x).le hchain.le
  constructor
  rw [coolLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    coolDensity_integral_eq_one hσ hball hfin i, ENNReal.ofReal_one]

/-- Integration against the phase law is integration against the density on `K`. -/
theorem integral_coolLaw {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (hchain : 0 < chain m σsq K i) (F : EuclSpace n → ℝ) :
    ∫ x, F x ∂(coolLaw m σsq K i)
      = ∫ x in K, (coolWeight m σsq i x / chain m σsq K i) * F x := by
  have hmeas : Measurable fun x : EuclSpace n =>
      (coolWeight m σsq i x / chain m σsq K i).toNNReal :=
    ((continuous_coolWeight m σsq i).measurable.div_const _).real_toNNReal
  have hrw : coolLaw m σsq K i = (volume.restrict K).withDensity
      (fun x => ((coolWeight m σsq i x / chain m σsq K i).toNNReal : ℝ≥0∞)) := rfl
  rw [hrw, integral_withDensity_eq_integral_smul hmeas]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal _ (div_nonneg (coolWeight_pos m σsq i x).le hchain.le)]

/-- **First moment at the exact law**: the phase score is unbiased for the chain ratio.
This is `chain_ratio_eq` read against `coolLaw`. -/
theorem integral_phaseScore_coolLaw {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (hKm : MeasurableSet K) (hchain : 0 < chain m σsq K i) :
    ∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)
      = chain m σsq K (i + 1) / chain m σsq K i := by
  rw [integral_coolLaw hchain]
  rw [show (∫ x in K, (coolWeight m σsq i x / chain m σsq K i) * phaseScore m σsq K i x)
      = ∫ x in K, coolRatio m σsq i x * (coolWeight m σsq i x / chain m σsq K i) from
    setIntegral_congr_fun hKm fun x hx => by rw [phaseScore_of_mem hx]; ring]
  exact chain_ratio_eq m σsq K i

/-- The squared phase ratio against the phase weight is again a Gaussian weight, at the
harmonic parameter `c = ab/(2a−b)`. This is `gW_sq_div` (the `E(Y²)` computation of §5.1)
transported to `coolWeight`/`coolRatio`. -/
theorem coolRatio_sq_mul_coolWeight {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (hi : i + 1 < m)
    (ha : σsq i ≠ 0) (hb : σsq (i + 1) ≠ 0) (hab : 2 * σsq i - σsq (i + 1) ≠ 0)
    (x : EuclSpace n) :
    coolRatio m σsq i x ^ 2 * coolWeight m σsq i x
      = Real.exp (-(‖x‖ ^ 2)
          / (2 * (σsq i * σsq (i + 1) / (2 * σsq i - σsq (i + 1))))) := by
  have hkey := gW_sq_div (f := fun _ : EuclSpace n => (1 : ℝ)) ha hb hab x
  simp only [gW, one_mul] at hkey
  rw [coolRatio, coolWeight_of_lt hi, coolWeight_of_lt (Nat.lt_of_succ_lt hi), ← hkey,
    div_pow, div_mul_eq_mul_div, sq (Real.exp (-(‖x‖ ^ 2) / (2 * σsq i)))]
  rw [mul_comm (Real.exp (-(‖x‖ ^ 2) / (2 * σsq i))) _, ← div_div,
    mul_div_assoc, div_self (Real.exp_pos (-(‖x‖ ^ 2) / (2 * σsq i))).ne', mul_one]

/-- Restating a Gaussian set-integral over `K` as `G` of the indicator, so §5.1's variance
machinery applies. (Same content as `chain_eq_G`, but at a variance that need not be a
schedule value.) -/
theorem setIntegral_gauss_eq_G {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (s : ℝ) :
    ∫ x in K, Real.exp (-(‖x‖ ^ 2) / (2 * s))
      = G (Set.indicator K (1 : EuclSpace n → ℝ)) s := by
  rw [G, show (fun x => gW (Set.indicator K (1 : EuclSpace n → ℝ)) s x)
      = Set.indicator K (fun y => Real.exp (-(‖y‖ ^ 2) / (2 * s))) from
    funext (gW_indicator' K s)]
  exact (integral_indicator hKm).symm

/-- **Second moment at the exact law**, in closed form: `E_π(W²) = G(c)/G(a)` with
`a = σᵢ²` and `c = ab/(2a−b)` the harmonic partner of `b = σᵢ₊₁²`. -/
theorem integral_phaseScore_sq_coolLaw {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)}
    {i : ℕ} (hKm : MeasurableSet K) (hchain : 0 < chain m σsq K i) (hi : i + 1 < m)
    (ha : σsq i ≠ 0) (hb : σsq (i + 1) ≠ 0) (hab : 2 * σsq i - σsq (i + 1) ≠ 0) :
    ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      = G (Set.indicator K (1 : EuclSpace n → ℝ))
          (σsq i * σsq (i + 1) / (2 * σsq i - σsq (i + 1))) / chain m σsq K i := by
  rw [integral_coolLaw hchain]
  rw [show (∫ x in K, (coolWeight m σsq i x / chain m σsq K i)
        * phaseScore m σsq K i x ^ 2)
      = ∫ x in K, Real.exp (-(‖x‖ ^ 2)
          / (2 * (σsq i * σsq (i + 1) / (2 * σsq i - σsq (i + 1)))))
            / chain m σsq K i from
    setIntegral_congr_fun hKm fun x hx => by
      rw [phaseScore_of_mem hx, ← coolRatio_sq_mul_coolWeight hi ha hb hab x]
      ring]
  rw [integral_div, setIntegral_gauss_eq_G hKm]

/-- **The exact-sample second-moment bound for a convex body, at the phase law.**

For `K` convex and measurable with `ball 0 1 ⊆ K` and finite volume, and for the fixed
cooling rate `σᵢ₊₁² = σᵢ²(1 + 1/n)` at an interior phase (`i + 1 < m`) with `n ≥ 3`,

  `E_π(W²) ≤ (1 + 2/n) · E_π(W)²`,

where `π = coolLaw m σsq K i` and `W = phaseScore m σsq K i`. **No assumed input**: the
`ZLogconcaveHypothesis` of `fixed_var_bound` is discharged for the indicator of a convex
set by `zLogconcaveHypothesis_indicator`. -/
theorem coolLaw_sq_moment_le {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) {i : ℕ} (hi : i + 1 < m)
    (hn : 3 ≤ n) (hrate : σsq (i + 1) = σsq i * (1 + 1 / (n : ℝ))) :
    ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ (1 + 2 / (n : ℝ))
        * (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)) ^ 2 := by
  have hN : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hαp : (0 : ℝ) < 1 + 1 / (n : ℝ) := by positivity
  have hαm : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) < 1 := by rw [div_lt_one hN0]; linarith
    linarith
  have ha0 := hσ i
  have hb0 := hσ (i + 1)
  have hab : 2 * σsq i - σsq (i + 1) ≠ 0 := by
    rw [hrate]; nlinarith
  -- name the three variance parameters `a = σᵢ²`, `b = σᵢ₊₁²`, `c = ab/(2a−b)`
  set a : ℝ := σsq i with hadef
  set b : ℝ := σsq (i + 1) with hbdef
  set c : ℝ := a * b / (2 * a - b) with hcdef
  set F : EuclSpace n → ℝ := Set.indicator K (1 : EuclSpace n → ℝ) with hFdef
  have hchain := chain_pos (m := m) hσ hball hfin i
  have hchain1 := chain_pos (m := m) hσ hball hfin (i + 1)
  have hGa : G F a = chain m σsq K i := (chain_eq_G (Nat.lt_of_succ_lt hi) hKm).symm
  have hGb : G F b = chain m σsq K (i + 1) := (chain_eq_G hi hKm).symm
  -- put the fixed-rate bound in the `a, b, c` parametrisation, via `σ = √b`
  have hσb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have hcore := fixed_var_bound_indicator (K := K) hK hKm
    (σ := Real.sqrt b) (Real.sqrt_pos.2 hb0) hn
  rw [hσb] at hcore
  have h2ab : 2 * a - b = a * (1 - 1 / (n : ℝ)) := by rw [hrate]; ring
  have hba : b / (1 + 1 / (n : ℝ)) = a := by
    rw [hrate, mul_div_assoc, div_self hαp.ne', mul_one]
  have hbc : b / (1 - 1 / (n : ℝ)) = c := by
    rw [hcdef, h2ab, div_eq_div_iff hαm.ne' (mul_pos ha0 hαm).ne']
    ring
  rw [hba, hbc, ← hFdef] at hcore
  have hGApos : (0 : ℝ) < G F a := by rw [hGa]; exact hchain
  -- assemble
  rw [integral_phaseScore_sq_coolLaw hKm hchain hi ha0.ne' hb0.ne' hab,
    integral_phaseScore_coolLaw hKm hchain, ← hcdef, ← hFdef, ← hGa, ← hGb]
  rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ hGApos (pow_pos hGApos 2)]
  nlinarith [mul_le_mul_of_nonneg_right hcore hGApos.le]

end ExactLaw

/-! ## `1 + 2/n` versus `1 + κ/m`

The exact-sample constant is `1 + 2/n` at the fixed rate `α = 1/n`
(`fixed_var_bound_ratio_indicator`). The volume algorithm asks for `1 + κ/m` with
`κ = varBudget ε` and `m` phases. These are **not** the same number, and the relation is
recorded here rather than assumed away. -/

section Budget

/-- The exact relation: the fixed-rate constant meets the algorithm's budget **iff**
`2m ≤ nκ`. Everything downstream of `1 + 2/n` needs this, plus strict slack for the TV
error. -/
theorem fixedRate_meets_budget_iff {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (κ : ℝ) :
    1 + 2 / (n : ℝ) ≤ 1 + κ / (m : ℝ) ↔ 2 * (m : ℝ) ≤ (n : ℝ) * κ := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [add_le_add_iff_left, div_le_div_iff₀ hn' hm']
  constructor <;> intro h <;> linarith

/-- **The obstruction, part 1.** If the fixed rate `α = 1/n` is to meet the budget
(`2m ≤ nκ`), the schedule's *total* cooling factor `(1 + 1/n)^m` is at most `e^{κ/2}`.
Uses only `1 + t ≤ e^t`. -/
theorem geomSchedule_pow_le_exp {n m : ℕ} (hn : 0 < n) {κ : ℝ}
    (hmeet : 2 * (m : ℝ) ≤ (n : ℝ) * κ) :
    (1 + 1 / (n : ℝ)) ^ m ≤ Real.exp (κ / 2) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hstep : (1 : ℝ) + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
    have := Real.add_one_le_exp (1 / (n : ℝ))
    linarith
  have hbase : (0 : ℝ) ≤ 1 + 1 / (n : ℝ) := by positivity
  have hpow : (1 + 1 / (n : ℝ)) ^ m ≤ (Real.exp (1 / (n : ℝ))) ^ m :=
    pow_le_pow_left₀ hbase hstep m
  have hexp : (Real.exp (1 / (n : ℝ))) ^ m = Real.exp ((m : ℝ) * (1 / (n : ℝ))) := by
    rw [← Real.exp_nat_mul]
  have harg : (m : ℝ) * (1 / (n : ℝ)) ≤ κ / 2 := by
    rw [mul_one_div, div_le_iff₀ hn']
    linarith
  calc (1 + 1 / (n : ℝ)) ^ m ≤ (Real.exp (1 / (n : ℝ))) ^ m := hpow
    _ = Real.exp ((m : ℝ) * (1 / (n : ℝ))) := hexp
    _ ≤ Real.exp (κ / 2) := Real.exp_le_exp.2 harg

/-- `e^{varBudget ε / 2} = √(1 + ε²/5)`, from `exp_varBudget`. -/
theorem exp_varBudget_half (ε : ℝ) :
    Real.exp (varBudget ε / 2) = Real.sqrt (1 + ε ^ 2 / 5) := by
  have hsq : (Real.exp (varBudget ε / 2)) ^ 2 = 1 + ε ^ 2 / 5 := by
    rw [sq, ← Real.exp_add, show varBudget ε / 2 + varBudget ε / 2 = varBudget ε by ring,
      exp_varBudget]
  rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]

/-- **The obstruction, part 2 — the finding.** For a target accuracy `ε ≤ 1`, a schedule at
the fixed rate `α = 1/n` that meets the algorithm's variance budget can cool by a total
factor of **less than `1.1`** over all `m` phases:

  `2m ≤ n · varBudget ε  ⟹  (1 + 1/n)^m < 11/10`.

Since `σ_m²/σ_0² = (1 + 1/n)^m` for the geometric schedule, this says the schedule cannot
cool at all. So `1 + 2/n` **does not** meet `1 + κ/m` for any schedule that actually anneals
from `σ₀² ≈ 1/n` up to `σ_m² ≈ R²`: the fixed rate must be replaced by a smaller `α`, for
which the available input is the general-`α` bound `G_mul_G_le_of_zLogconcave` with constant
`(1 − α²)^{−(n+1)}`, not the fixed-rate `1 + 2/n`. -/
theorem geomSchedule_total_cooling_lt {n m : ℕ} (hn : 0 < n) {ε : ℝ} (hε1 : ε ≤ 1)
    (hε0 : 0 ≤ ε) (hmeet : 2 * (m : ℝ) ≤ (n : ℝ) * varBudget ε) :
    (1 + 1 / (n : ℝ)) ^ m < 11 / 10 := by
  have h1 := geomSchedule_pow_le_exp hn hmeet
  rw [exp_varBudget_half] at h1
  have h2 : Real.sqrt (1 + ε ^ 2 / 5) < 11 / 10 := by
    rw [show (11 : ℝ) / 10 = ((11 : ℝ) / 10) from rfl]
    refine (Real.sqrt_lt' (by norm_num)).2 ?_
    nlinarith
  linarith

/-- **The geometric schedule really is the fixed-rate one.** `geomSchedule σ₀sq (1/n)`
satisfies `σᵢ₊₁² = σᵢ²(1 + 1/n)`, the hypothesis `fixed_var_bound_indicator` is stated for,
and its total cooling factor after `m` phases is `(1 + 1/n)^m` — the quantity
`geomSchedule_total_cooling_lt` bounds. -/
theorem geomSchedule_succ (σ₀sq α : ℝ) (i : ℕ) :
    geomSchedule σ₀sq α (i + 1) = geomSchedule σ₀sq α i * (1 + α) := by
  simp only [geomSchedule, pow_succ]
  ring

theorem geomSchedule_div_zero {σ₀sq α : ℝ} (h0 : σ₀sq ≠ 0) (m : ℕ) :
    geomSchedule σ₀sq α m / geomSchedule σ₀sq α 0 = (1 + α) ^ m := by
  simp [geomSchedule, h0]

end Budget

/-! ## The capstone: `hphase_var` for a sampled phase

Everything above, assembled. The only input that is *not* proved here is the TV bound
itself — which is the sampler's job, not this file's. -/

section Capstone

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ} {X : Ω → EuclSpace n}
  {ε : ℝ≥0∞}

/-- **The per-phase second-moment bound for a TV-approximate sample**, in the shape
`Ttc.VolumeAlgorithm.cousinsVempala`'s `hphase_var` consumes.

Inputs, all of them either proved elsewhere in `Arlib` or explicit:

* `hK`, `hKm`, `hball`, `hfin` — the body: convex, measurable, containing the unit ball,
  finite volume. Exactly `cousinsVempala`'s hypotheses on `K`.
* `hKR : K ⊆ R·Bₙ` — **an extra hypothesis `cousinsVempala` does not have.** It is what
  makes the score bounded (`phaseScore_le`), without which no TV transport of `W²` is
  possible at all. `cousinsVempala`'s hypotheses already force `K` bounded, but supply no
  radius, and `R` is not cosmetic: it enters `hslack` through `e^{R²/(2σᵢ²)}`.
* `hi : i + 1 < m`, `hn : 3 ≤ n`, `hrate : σᵢ₊₁² = σᵢ²(1 + 1/n)` — an interior phase of the
  fixed-rate schedule, the regime of `fixed_var_bound_indicator`.
* `hTV` — the sampler's guarantee: the law of `X` is within total variation `ε` of the
  exact phase law.
* `hs`, `hslack` — the slack `s` above `1 + 2/n` and the explicit smallness condition on
  `ε` that pays for the transport. The exact mean `chain (i+1) / chain i` appearing there
  is a concrete quantity, not an unknown.

The exact-sample bound is **not** assumed: it is `coolLaw_sq_moment_le`. -/
theorem sampled_phase_sq_moment_le (hσ : ∀ j, 0 < σsq j)
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R)
    (hi : i + 1 < m) (hn : 3 ≤ n) (hrate : σsq (i + 1) = σsq i * (1 + 1 / (n : ℝ)))
    (hX : Measurable X) (hTV : TVLe (μ.map X) (coolLaw m σsq K i) ε) (hεtop : ε ≠ ⊤)
    {s : ℝ} (hs : 0 ≤ s)
    (hslack : ε.toReal * (Real.exp (R ^ 2 / (2 * σsq i)) ^ 2
          * (1 + 2 * (1 + 2 / (n : ℝ) + s)))
        ≤ s * (chain m σsq K (i + 1) / chain m σsq K i) ^ 2) :
    ∫ ω, phaseScore m σsq K i (X ω) ^ 2 ∂μ
      ≤ (1 + 2 / (n : ℝ) + s) * (∫ ω, phaseScore m σsq K i (X ω) ∂μ) ^ 2 := by
  haveI := coolLaw_isProbabilityMeasure (m := m) hσ hball hfin i
  have hN : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hchain := chain_pos (m := m) hσ hball hfin i
  have hC : (0 : ℝ) ≤ 1 + 2 / (n : ℝ) := by positivity
  have hmean := integral_phaseScore_coolLaw (m := m) (σsq := σsq) hKm hchain
  rw [← hmean] at hslack
  exact sq_moment_le_of_tvLe_map hX hTV hεtop (Real.exp_pos _)
    (measurable_phaseScore hKm i) (phaseScore_nonneg m σsq K i)
    (phaseScore_le hσ hKR i) hC hs
    (coolLaw_sq_moment_le hσ hK hKm hball hfin hi hn hrate) hslack

/-- **The same, with the constant written as the algorithm writes it.** The volume
algorithm asks for `1 + κ/m`, not `1 + 2/n + s`. The two agree exactly when
`s = κ/m − 2/n`, which is nonnegative precisely when `2m ≤ nκ`
(`fixedRate_meets_budget_iff`) — and `geomSchedule_total_cooling_lt` says what that costs.

So the *statement* the algorithm needs is available; what it needs to be **usable** is a
schedule with `2m ≤ n·varBudget ε`, which the fixed rate `α = 1/n` cannot supply. -/
theorem sampled_phase_sq_moment_le_budget (hσ : ∀ j, 0 < σsq j)
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R)
    (hi : i + 1 < m) (hn : 3 ≤ n) (hrate : σsq (i + 1) = σsq i * (1 + 1 / (n : ℝ)))
    (hX : Measurable X) (hTV : TVLe (μ.map X) (coolLaw m σsq K i) ε) (hεtop : ε ≠ ⊤)
    {κ : ℝ} (hm : 0 < m) (hbudget : 2 * (m : ℝ) ≤ (n : ℝ) * κ)
    (hslack : ε.toReal * (Real.exp (R ^ 2 / (2 * σsq i)) ^ 2 * (1 + 2 * (1 + κ / (m : ℝ))))
        ≤ (κ / (m : ℝ) - 2 / (n : ℝ)) * (chain m σsq K (i + 1) / chain m σsq K i) ^ 2) :
    ∫ ω, phaseScore m σsq K i (X ω) ^ 2 ∂μ
      ≤ (1 + κ / (m : ℝ)) * (∫ ω, phaseScore m σsq K i (X ω) ∂μ) ^ 2 := by
  have hn0 : 0 < n := by omega
  have hs : (0 : ℝ) ≤ κ / (m : ℝ) - 2 / (n : ℝ) := by
    have := (fixedRate_meets_budget_iff hn0 hm κ).2 hbudget
    linarith
  have heq : 1 + 2 / (n : ℝ) + (κ / (m : ℝ) - 2 / (n : ℝ)) = 1 + κ / (m : ℝ) := by ring
  have := sampled_phase_sq_moment_le hσ hK hKm hball hfin hKR hi hn hrate hX hTV hεtop hs
    (by rw [heq]; exact hslack)
  rwa [heq] at this

end Capstone

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms integrable_of_bounded
#print axioms integral_le_bound
#print axioms abs_integral_sub_le_of_tvLe
#print axioms abs_integral_sq_sub_le_of_tvLe
#print axioms sq_moment_le_of_tvLe
#print axioms sq_moment_le_of_tvLe_exact
#print axioms sq_moment_le_of_tvLe_map
#print axioms coolRatio_le_exp
#print axioms phaseScore_of_mem
#print axioms phaseScore_nonneg
#print axioms phaseScore_le
#print axioms measurable_phaseScore
#print axioms phaseScore
#print axioms coolLaw
#print axioms coolLaw_isProbabilityMeasure
#print axioms integral_coolLaw
#print axioms integral_phaseScore_coolLaw
#print axioms coolRatio_sq_mul_coolWeight
#print axioms setIntegral_gauss_eq_G
#print axioms integral_phaseScore_sq_coolLaw
#print axioms coolLaw_sq_moment_le
#print axioms sampled_phase_sq_moment_le
#print axioms sampled_phase_sq_moment_le_budget
#print axioms fixedRate_meets_budget_iff
#print axioms geomSchedule_pow_le_exp
#print axioms exp_varBudget_half
#print axioms geomSchedule_total_cooling_lt
#print axioms geomSchedule_succ
#print axioms geomSchedule_div_zero

end Arlib.GaussianCooling
