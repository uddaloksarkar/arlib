/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.Chain
import Arlib.Convexity.GaussianCooling.Estimator
import Arlib.Probability.TV

/-!
# Approximately unbiased phase estimators, and how their bias compounds

Cousins–Vempala §5.2 telescopes a chain `A 0, …, A m` of Gaussian integrals by estimating
each ratio `A (i+1) / A i` with a random score `W i`, and multiplying the `m` estimates.
The assembled statement in the downstream development
(`Ttc.VolumeAlgorithm.cousinsVempala`) asks for those estimates to be **exactly** unbiased,

  `∫ W i dμ = A (i+1) / A i`,

which **no mixing bound can ever supply**: the score is evaluated at a sample drawn from a
chain run for finitely many steps, so its law is at total-variation distance `> 0` from the
phase-`i` target density and its mean is off by a corresponding amount. This file replaces
that equality by the honest two-sided *relative* statement

  `∫ W i dμ ∈ (1 ± η)·(A (i+1) / A i)`,

and does the bookkeeping that pushes it through the `m`-fold product.

## The answer, in one line

Per-phase relative bias `η` compounds to a relative bias `(1 + η)^m − 1` on the product,
and

  **`2·m·η ≤ τ`  (i.e. `η ≤ τ/(2m)`)  and  `τ ≤ 1`   ⟹   `(1 + η)^m − 1 ≤ τ`.**

So the per-phase budget really is `Θ(τ/m)`, not `Θ(τ)`; see `phaseBias_le` and
`phaseBias_le_of_div`. Combined with the `ε + τ + ε·τ` composition performed downstream by
`Ttc.CV.relErr_trans`, a requested end-to-end accuracy `ε` is met by, e.g., running the
Chebyshev half at `ε/2` and the mean bias at `τ = ε/4`, which asks each phase for
`η ≤ ε/(8m)`.

## Why the interval must be two-sided

A one-sided per-phase bound does not compose. In `prod_mem_Icc` the *lower* halves are used
twice — once for the product's lower bound, and once (via `hxnn`) to supply the factor
nonnegativity without which `Finset.prod_le_prod` cannot even deliver the *upper* bound. And
the downstream Chebyshev step (`Ttc.CV.measure_notMem_relErr_le`) needs `0 < E(∏ W i)`,
which again is the lower half; `integral_prod_pos` below is that step. So an upper-only
per-phase bound yields neither half of the conclusion.

## Main results

* `two_sub_pow_one_add_le_pow_one_sub` — `2 − (1+η)^m ≤ (1−η)^m`: the *lower* endpoint of
  the compounded interval is no worse than the *upper* one, so the compounded error is a
  single symmetric relative bias `(1+η)^m − 1`. (Two applications of Bernoulli.)
* `pow_one_add_le_one_add_two_mul` — `(1+η)^m ≤ 1 + 2mη` whenever `2mη ≤ 1`. Elementary
  induction; no `exp`/`log` and no asymptotics.
* `phaseBias_le`, `phaseBias_le_of_div` — **the per-phase budget**, in the two equivalent
  forms `2mη ≤ τ` and `η ≤ τ/(2m)`.
* `prod_mem_Icc` — a product of factors each in `(1 ± η)·r i` lies in
  `((1−η)^N ∏ r, (1+η)^N ∏ r)`, `N` the number of factors.
* `prod_fin_telescope` — the telescoping identity `∏_{i<m} A(i+1)/A i = A m / A 0`.
* `integral_prod_mem_Icc_pow` — the mean of the product estimator, from independence plus
  the per-phase interval: `E(∏ W) ∈ ((1−η)^m·(A m/A 0), (1+η)^m·(A m/A 0))`.
* `integral_prod_mem_relErr` — the same, rewritten as the single symmetric relative bias
  `(1+η)^m − 1` around `A m / A 0`; this is *literally* the interval
  `Ttc.relErr ((1+η)^m − 1) (A m / A 0)`, see the interoperability note below.
* `integral_prod_mem_relErr_of_budget` — the headline: under `2mη ≤ τ ≤ 1`,
  `E(∏ W) ∈ (1 ± τ)·(A m / A 0)`.
* `integral_prod_pos` — `0 < E(∏ W)` from the lower half, the side condition Chebyshev
  needs downstream.
* `abs_integral_sub_le_of_tvLe_scaled`, `integral_mem_Icc_of_tvLe` — **the total-variation
  bookkeeping**: a sampler whose law is
  within `TVLe … e` of the phase target, evaluated on a score with values in `[0, B]`,
  has mean within a relative `η` of the target's mean as soon as `B·e ≤ η·r`. This is the
  step `Ttc/Volume/CousinsVempala.lean` records as "needs the total-variation bookkeeping
  of `Arlib.Probability.TV`, and is not done".

## Interoperability with `Ttc.relErr` (`Arlib` may not import `Ttc`)

`Ttc.relErr ε b` is `@[reducible] def relErr (ε b : ℝ) : Set ℝ := Set.Icc ((1-ε)*b) ((1+ε)*b)`
(`Ttc/Model/ProblemSetting.lean:58`). Every statement here is phrased in exactly that
`Set.Icc ((1 - η) * b) ((1 + η) * b)` form and **no `Arlib`-side copy of `relErr`,
`relErr_trans` or `relErr_mono` is introduced**. Because `relErr` is a reducible
abbreviation for precisely this interval, a `Ttc`-side consumer can feed the conclusions
below straight into `Ttc.CV.relErr_trans` / `Ttc.CV.relErr_mono` with no glue lemma at all.
Duplicating the composition lemmas on this side would have created two names for one notion
in a repository that already flags that hazard; duplicating the *interval* costs nothing
because it is a Mathlib notion (`Set.Icc`) to begin with.

Two items are duplicated. The telescoping identity `prod_fin_telescope`
(= `Ttc.CV.prod_fin_ratio`) is pure arithmetic about `A : ℕ → ℝ` and has no business living
downstream of the volume oracle; the `Ttc` copy can be replaced by this one. And
`abs_integral_sub_le_of_tvLe_scaled` is the same statement as
`Arlib.GaussianCooling.abs_integral_sub_le_of_tvLe` in the sibling file
`PhaseVar.lean` (the second-moment side of the same §5.1/§5.2 split); it carries the
`_scaled` suffix only to keep the two files independently compilable, and one of the two
should be deleted once both have landed.

## Honesty note

Nothing here is a `Prop` that assumes its own conclusion. `integral_mem_Icc_of_tvLe` takes
a `TVLe` bound as an *input* — it does not assert that any particular sampler achieves one;
producing such a bound is the ball-walk mixing problem, and it is not addressed here. What
this file establishes is the implication *from* such a bound *to* the accuracy of the
telescoped product, which is the piece that was missing.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

/-! ## How a per-phase relative bias compounds

Two elementary facts about `(1 ± η)^m`. The first says the compounded interval is
*symmetric enough*: its lower endpoint `(1−η)^m` is at least `2 − (1+η)^m`, so both
endpoints are covered by the single relative bias `(1+η)^m − 1`. The second is the
quantitative bound that turns a per-phase budget into an aggregate one. -/

/-- **The compounded interval is dominated by a symmetric one.**
`2 − (1 + η)^m ≤ (1 − η)^m` for `0 ≤ η ≤ 1`.

Both Bernoulli inequalities: `1 + mη ≤ (1+η)^m` and `1 − mη ≤ (1−η)^m`, whose sum is the
claim. This is what lets the two-sided interval
`((1−η)^m·b, (1+η)^m·b)` be reported as the single relative error `(1+η)^m − 1`. -/
theorem two_sub_pow_one_add_le_pow_one_sub {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (m : ℕ) :
    2 - (1 + η) ^ m ≤ (1 - η) ^ m := by
  have h1 : 1 + (m : ℝ) * η ≤ (1 + η) ^ m := one_add_mul_le_pow (by linarith) m
  have h2 : 1 + (m : ℝ) * (-η) ≤ (1 + -η) ^ m := one_add_mul_le_pow (by linarith) m
  have h3 : (1 + -η : ℝ) = 1 - η := by ring
  rw [h3] at h2
  nlinarith

/-- **The aggregate bias is at most `2mη`**, provided `2mη ≤ 1`.

Induction on `m`: the step is `(1 + 2kη)(1 + η) ≤ 1 + 2(k+1)η`, i.e. `2kη² ≤ η`, which is
`2kη ≤ 1`. The hypothesis is *not* fixed along the induction — it weakens automatically,
since `2kη ≤ 2(k+1)η` for `η ≥ 0`.

This is deliberately elementary: no `exp`, no `log`, no asymptotics, so the resulting
budget is an inequality a caller can actually discharge. -/
theorem pow_one_add_le_one_add_two_mul {η : ℝ} (hη : 0 ≤ η) :
    ∀ m : ℕ, 2 * (m : ℝ) * η ≤ 1 → (1 + η) ^ m ≤ 1 + 2 * (m : ℝ) * η := by
  intro m
  induction m with
  | zero => intro _; norm_num
  | succ k ih =>
      intro h
      push_cast at h ⊢
      have hk : 2 * (k : ℝ) * η ≤ 1 := by nlinarith
      have hik := ih (by linarith)
      have hpos : (0 : ℝ) ≤ 1 + η := by linarith
      calc (1 + η) ^ (k + 1) = (1 + η) ^ k * (1 + η) := pow_succ _ _
        _ ≤ (1 + 2 * (k : ℝ) * η) * (1 + η) := mul_le_mul_of_nonneg_right hik hpos
        _ ≤ 1 + 2 * ((k : ℝ) + 1) * η := by nlinarith

/-- **The per-phase budget, multiplicative form.** If the per-phase relative bias `η`
satisfies `2mη ≤ τ` for a target aggregate bias `τ ≤ 1`, then the `m`-fold product's
relative bias `(1 + η)^m − 1` is at most `τ`.

Note the shape: the budget is `Θ(τ/m)`, **not** `Θ(τ)`. The `m` is not cosmetic — the
per-phase errors multiply, and `(1 + τ)^m − 1 ≈ e^{mτ} − 1` blows up. -/
theorem phaseBias_le {η τ : ℝ} {m : ℕ} (hη : 0 ≤ η) (hτ : τ ≤ 1)
    (hbudget : 2 * (m : ℝ) * η ≤ τ) :
    (1 + η) ^ m - 1 ≤ τ := by
  have h := pow_one_add_le_one_add_two_mul hη m (by linarith)
  linarith

/-- **The per-phase budget, divided form: `η ≤ τ/(2m)`.** The same statement as
`phaseBias_le` in the shape a schedule is written in. -/
theorem phaseBias_le_of_div {η τ : ℝ} {m : ℕ} (hm : 0 < m) (hη : 0 ≤ η) (hτ : τ ≤ 1)
    (hbudget : η ≤ τ / (2 * m)) :
    (1 + η) ^ m - 1 ≤ τ := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have h2m : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  refine phaseBias_le hη hτ ?_
  calc 2 * (m : ℝ) * η ≤ 2 * (m : ℝ) * (τ / (2 * (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hbudget h2m.le
    _ = τ := by field_simp

/-- **A per-phase bias of `η` is `≤ 1/2` once the budget holds** (for `m ≥ 1`, `τ ≤ 1`).
Recorded because `prod_mem_Icc` needs `η ≤ 1` to know the interval's lower endpoint is
nonnegative. -/
theorem le_one_of_budget {η τ : ℝ} {m : ℕ} (hm : 0 < m) (hη : 0 ≤ η) (hτ : τ ≤ 1)
    (hbudget : 2 * (m : ℝ) * η ≤ τ) : η ≤ 1 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith [mul_nonneg (sub_nonneg.mpr hmR) hη]

/-! ## The product of approximately correct factors -/

/-- **Relative errors multiply.** If every factor `x i` lies in `(1 ± η)·r i` with
`r i ≥ 0` and `η ≤ 1`, then `∏ x i` lies in `((1−η)^N·∏ r i, (1+η)^N·∏ r i)`, `N` the
number of factors.

Both halves of each hypothesis interval are used: the lower halves give the factors'
nonnegativity, without which `Finset.prod_le_prod` cannot even state the upper bound. -/
theorem prod_mem_Icc {ι : Type*} [Fintype ι] {x r : ι → ℝ} {η : ℝ}
    (hη1 : η ≤ 1) (hr : ∀ i, 0 ≤ r i)
    (hx : ∀ i, x i ∈ Set.Icc ((1 - η) * r i) ((1 + η) * r i)) :
    ∏ i, x i ∈ Set.Icc ((1 - η) ^ Fintype.card ι * ∏ i, r i)
      ((1 + η) ^ Fintype.card ι * ∏ i, r i) := by
  have hlow : ∀ i, 0 ≤ (1 - η) * r i := fun i => mul_nonneg (by linarith) (hr i)
  have hxnn : ∀ i, 0 ≤ x i := fun i => le_trans (hlow i) (hx i).1
  constructor
  · calc (1 - η) ^ Fintype.card ι * ∏ i, r i = ∏ i, (1 - η) * r i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ ≤ ∏ i, x i :=
          Finset.prod_le_prod (fun i _ => hlow i) (fun i _ => (hx i).1)
  · calc ∏ i, x i ≤ ∏ i, (1 + η) * r i :=
          Finset.prod_le_prod (fun i _ => hxnn i) (fun i _ => (hx i).2)
      _ = (1 + η) ^ Fintype.card ι * ∏ i, r i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-! ## The telescoping identity

Pure arithmetic about a chain `A : ℕ → ℝ` of nonzero reals. (The downstream copy is
`Ttc.CV.prod_range_ratio` / `Ttc.CV.prod_fin_ratio`; this side is where it belongs, since
nothing about it mentions a volume oracle.) -/

/-- The telescoping product over `Finset.range`. -/
theorem prod_range_telescope {A : ℕ → ℝ} (hA : ∀ i, A i ≠ 0) (m : ℕ) :
    ∏ i ∈ Finset.range m, A (i + 1) / A i = A m / A 0 := by
  induction m with
  | zero => simp [div_self (hA 0)]
  | succ k ih =>
      have h0 := hA 0
      have hk := hA k
      rw [Finset.prod_range_succ, ih]
      field_simp

/-- The telescoping product indexed by `Fin m` — the form the product estimator is written
in. -/
theorem prod_fin_telescope {A : ℕ → ℝ} (hA : ∀ i, A i ≠ 0) (m : ℕ) :
    ∏ i : Fin m, A ((i : ℕ) + 1) / A (i : ℕ) = A m / A 0 := by
  rw [Fin.prod_univ_eq_prod_range (fun i => A (i + 1) / A i) m]
  exact prod_range_telescope hA m

/-! ## §5.2's mean step, with an approximate mean

`Arlib.GaussianCooling.integral_prod_eq_prod_integral'` factors the mean of the product
over an independent family; `prod_mem_Icc` propagates the per-factor intervals; and
`prod_fin_telescope` collapses the product of targets. Nothing else is needed — this really
is bookkeeping, and no new probability enters. -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The product estimator's mean, from approximate per-phase means.** With the `m` phases
independent and each phase's mean within a relative `η` of the chain ratio
`A (i+1) / A i`, the product's mean is within `((1−η)^m, (1+η)^m)` of `A m / A 0`. -/
theorem integral_prod_mem_Icc_pow {m : ℕ} {W : Fin m → Ω → ℝ} {A : ℕ → ℝ} {η : ℝ}
    (hη1 : η ≤ 1) (hindep : iIndepFun W μ) (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (hApos : ∀ i, 0 < A i)
    (hmean : ∀ i : Fin m, ∫ ω, W i ω ∂μ ∈
      Set.Icc ((1 - η) * (A ((i : ℕ) + 1) / A (i : ℕ)))
        ((1 + η) * (A ((i : ℕ) + 1) / A (i : ℕ)))) :
    ∫ ω, ∏ i, W i ω ∂μ ∈
      Set.Icc ((1 - η) ^ m * (A m / A 0)) ((1 + η) ^ m * (A m / A 0)) := by
  rw [integral_prod_eq_prod_integral' hindep hmeas]
  have h := prod_mem_Icc (ι := Fin m) (x := fun i => ∫ ω, W i ω ∂μ)
    (r := fun i : Fin m => A ((i : ℕ) + 1) / A (i : ℕ)) hη1
    (fun i => (div_pos (hApos _) (hApos _)).le) hmean
  rwa [Fintype.card_fin, prod_fin_telescope (fun i => (hApos i).ne') m] at h

/-- **The product estimator's mean, as one relative error.** The compounded bias is
`(1 + η)^m − 1`, symmetrically on both sides.

This interval is *definitionally* `Ttc.relErr ((1 + η)^m − 1) (A m / A 0)`, so downstream it
composes with `Ttc.CV.relErr_trans` (against the Chebyshev step) and `Ttc.CV.relErr_mono`
(to report at the requested accuracy) with no glue. -/
theorem integral_prod_mem_relErr {m : ℕ} {W : Fin m → Ω → ℝ} {A : ℕ → ℝ} {η : ℝ}
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ) (hApos : ∀ i, 0 < A i)
    (hmean : ∀ i : Fin m, ∫ ω, W i ω ∂μ ∈
      Set.Icc ((1 - η) * (A ((i : ℕ) + 1) / A (i : ℕ)))
        ((1 + η) * (A ((i : ℕ) + 1) / A (i : ℕ)))) :
    ∫ ω, ∏ i, W i ω ∂μ ∈
      Set.Icc ((1 - ((1 + η) ^ m - 1)) * (A m / A 0))
        ((1 + ((1 + η) ^ m - 1)) * (A m / A 0)) := by
  have hR : (0 : ℝ) ≤ A m / A 0 := (div_pos (hApos m) (hApos 0)).le
  obtain ⟨hlo, hhi⟩ := integral_prod_mem_Icc_pow hη1 hindep hmeas hApos hmean
  have hsym := two_sub_pow_one_add_le_pow_one_sub hη hη1 m
  constructor
  · refine le_trans ?_ hlo
    have : (1 - ((1 + η) ^ m - 1)) = 2 - (1 + η) ^ m := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hsym hR
  · refine le_trans hhi (le_of_eq ?_)
    ring

/-- **The headline restatement of §5.2's mean step.** Under the per-phase budget
`2mη ≤ τ ≤ 1`, the telescoped product's mean is within a relative `τ` of `A m / A 0`.

This is the hypothesis `hphase_mean` of `Ttc.VolumeAlgorithm.cousinsVempala`, weakened from
an equality to a two-sided relative bound, and carried through the product. -/
theorem integral_prod_mem_relErr_of_budget {m : ℕ} {W : Fin m → Ω → ℝ} {A : ℕ → ℝ}
    {η τ : ℝ} (hm : 0 < m) (hη : 0 ≤ η) (hτ : τ ≤ 1)
    (hbudget : 2 * (m : ℝ) * η ≤ τ)
    (hindep : iIndepFun W μ) (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (hApos : ∀ i, 0 < A i)
    (hmean : ∀ i : Fin m, ∫ ω, W i ω ∂μ ∈
      Set.Icc ((1 - η) * (A ((i : ℕ) + 1) / A (i : ℕ)))
        ((1 + η) * (A ((i : ℕ) + 1) / A (i : ℕ)))) :
    ∫ ω, ∏ i, W i ω ∂μ ∈ Set.Icc ((1 - τ) * (A m / A 0)) ((1 + τ) * (A m / A 0)) := by
  have hη1 : η ≤ 1 := le_one_of_budget hm hη hτ hbudget
  have hR : (0 : ℝ) ≤ A m / A 0 := (div_pos (hApos m) (hApos 0)).le
  have hbias : (1 + η) ^ m - 1 ≤ τ := phaseBias_le hη hτ hbudget
  obtain ⟨hlo, hhi⟩ := integral_prod_mem_relErr hη hη1 hindep hmeas hApos hmean
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hR) hlo
  · exact le_trans hhi (mul_le_mul_of_nonneg_right (by linarith) hR)

/-- **Positivity of the product estimator's mean** — the side condition Chebyshev needs.
Read off the *lower* half of the relative-error interval; this is the concrete reason a
one-sided (upper) bound on the phase means would be useless. -/
theorem integral_prod_pos {x r τ : ℝ} (hτ : τ < 1) (hr : 0 < r)
    (h : x ∈ Set.Icc ((1 - τ) * r) ((1 + τ) * r)) : 0 < x :=
  lt_of_lt_of_le (by nlinarith) h.1

/-! ## The total-variation bookkeeping

Where the approximate mean comes from. A sampler produces a law `ρ` instead of the phase
target `ν`; a mixing bound gives `TVLe ρ ν e`; and a bounded score `f` then has
`|∫ f dρ − ∫ f dν| ≤ B·e` by `Arlib.TVLe.integral_le` (which is stated for `f` valued in
`[0,1]`; the rescaling to `[0,B]` is the only work below).

Turning that *absolute* error into a *relative* one is division by the target mean `r`,
which is why `Chain.chain_pos` matters: the phase targets `A (i+1)/A i` are bounded away
from `0` by explicit constants, so a TV bound of `η·r/B` buys a relative bias of `η`. -/

section TV

variable {Ω : Type*} [MeasurableSpace Ω] {ρ ν : Measure Ω}

/-- **Absolute TV error, rescaled to a bounded score.** For `f` with values in `[0, B]` and
`TVLe ρ ν e`, `|∫ f dρ − ∫ f dν| ≤ B·e`. `Arlib.TVLe.integral_le` is the `B = 1` case; this
applies it to `f / B`. -/
theorem abs_integral_sub_le_of_tvLe_scaled [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    {e : ℝ≥0∞} (hTV : TVLe ρ ν e) (he : e ≠ ⊤) {f : Ω → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : 0 < B) (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    |∫ x, f x ∂ρ - ∫ x, f x ∂ν| ≤ B * e.toReal := by
  have key := hTV.integral_le he (f := fun x => f x / B) (hf.div_const B)
    (fun x => div_nonneg (hf0 x) hB.le) (fun x => (div_le_one hB).mpr (hfB x))
  rw [integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hB,
    div_le_iff₀ hB] at key
  linarith [key]

/-- **A mixing bound gives an approximately unbiased phase score.**

If the sampler's law `ρ` is within total variation `e` of the phase target `ν`, the score
`f` takes values in `[0, B]`, the target mean is `∫ f dν = r`, and the slack satisfies
`B·e ≤ η·r`, then the *realised* mean is within a relative `η` of the target:

  `∫ f dρ ∈ (1 ± η)·r`.

This is exactly the hypothesis `integral_prod_mem_relErr_of_budget` consumes, one phase at a
time; chaining the two says a per-phase TV budget of `η·r/B` with `η ≤ τ/(2m)` delivers a
relative bias `τ` on the whole telescoped product.

Nothing here asserts that any sampler *achieves* a given `e`: `hTV` is an input. -/
theorem integral_mem_Icc_of_tvLe [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    {e : ℝ≥0∞} (hTV : TVLe ρ ν e) (he : e ≠ ⊤) {f : Ω → ℝ} (hf : Measurable f) {B r η : ℝ}
    (hB : 0 < B) (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hr : ∫ x, f x ∂ν = r) (hslack : B * e.toReal ≤ η * r) :
    ∫ x, f x ∂ρ ∈ Set.Icc ((1 - η) * r) ((1 + η) * r) := by
  have key := abs_integral_sub_le_of_tvLe_scaled hTV he hf hB hf0 hfB
  rw [hr] at key
  rw [abs_le] at key
  constructor <;> nlinarith [key.1, key.2]

end TV

/-! ## Axiom audit

Every declaration above must rest on nothing beyond Mathlib's three foundational axioms
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms two_sub_pow_one_add_le_pow_one_sub
#print axioms pow_one_add_le_one_add_two_mul
#print axioms phaseBias_le
#print axioms phaseBias_le_of_div
#print axioms le_one_of_budget
#print axioms prod_mem_Icc
#print axioms prod_range_telescope
#print axioms prod_fin_telescope
#print axioms integral_prod_mem_Icc_pow
#print axioms integral_prod_mem_relErr
#print axioms integral_prod_mem_relErr_of_budget
#print axioms integral_prod_pos
#print axioms abs_integral_sub_le_of_tvLe_scaled
#print axioms integral_mem_Icc_of_tvLe

end Arlib.GaussianCooling
