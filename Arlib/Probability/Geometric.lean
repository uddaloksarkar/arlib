/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The mean of the geometric distribution, and expected round counts

Mathlib has the geometric *measure* (`ProbabilityTheory.geometricMeasure`) and its
integral (`ProbabilityTheory.integral_geometricMeasure`), but **no lemma computing
its mean**, and no discrete tail-sum identity for `ℕ`-valued random variables.
This file supplies both.

## Counting conventions — read this first

There are two geometric distributions and they differ by one:

* **failures before the first success** — this is Mathlib's convention.
  `geometricMeasure p {n} = (1 - p) ^ n * p`, supported on `n = 0, 1, 2, …`.
  Its mean is `(1 - p) / p`  (`Arlib.Geometric.integral_geometricMeasure_id`).
* **trials up to and including the first success** — the count a rejection loop
  cares about, namely `1 + (failures)`, supported on `1, 2, 3, …`.
  Its mean is `1 / p`  (`Arlib.Geometric.integral_geometricMeasure_trials`).

Every statement below says in its own docstring which of the two it uses.

## Main results

Generic machinery, stated for an arbitrary `ℕ`-valued random variable `N` on an
arbitrary measure space (no independence, no product structure, no probability
measure unless named):

* `Arlib.Geometric.lintegral_natCast_eq_tsum_meas_lt` — the **tail-sum identity**
  `∫⁻ ω, N ω = ∑' n, μ {ω | n < N ω}`.  Missing from Mathlib; this is the bulk of
  the work here.  Mathlib's layer-cake (`MeasureTheory.lintegral_eq_lintegral_meas_lt`)
  is the continuous analogue and does not give this.
* `Arlib.Geometric.meas_lt_le_pow_of_step` — a one-step contraction
  `μ {N > n+1} ≤ q * μ {N > n}` upgrades to the geometric tail `μ {N > n} ≤ q ^ n`.
* `Arlib.Geometric.lintegral_natCast_le_of_geometric_tail` — from that tail,
  `∫⁻ ω, N ω ≤ (1 - q)⁻¹`, and with `q = 1 - p`, `≤ p⁻¹`.
* `Arlib.Geometric.integral_natCast_le_inv` — the real-valued (Bochner) form:
  `∫ ω, (N ω : ℝ) ∂μ ≤ 1 / p`, together with `integrable_natCast_of_geometric_tail`.

Exact means of Mathlib's `geometricMeasure`:

* `Arlib.Geometric.integral_geometricMeasure_id` : `∫ n, (n : ℝ) = (1 - p) / p`.
* `Arlib.Geometric.integral_geometricMeasure_trials` : `∫ n, ((n : ℝ) + 1) = 1 / p`.

## Why a *bound* and not just the identity

A rejection loop is rarely handed an exact per-round success probability; it is
handed a lower bound (in the motivating application, `9 / (20 e)`).  So the
headline consumer-facing lemma is the monotone one: *if each round succeeds with
probability at least `p`, the expected number of rounds is at most `1 / p`*.  The
hypothesis is packaged as the tail bound `μ {ω | n < N ω} ≤ (1 - p) ^ n`, which is
what "every round succeeds with probability `≥ p`, whatever happened before"
gives after `n` steps — and which `meas_lt_le_pow_of_step` derives from the
one-step form.
-/

namespace Arlib.Geometric

open MeasureTheory Set
open scoped ENNReal NNReal

/-! ## Part 1: the tail-sum identity for `ℕ`-valued random variables -/

section TailSum

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `∑' n : ℕ, 1_{n < k} = k`, in `ℝ≥0∞`.  The pointwise heart of the tail-sum
identity: a natural number is the number of `n` below it. -/
lemma tsum_ite_lt_eq (k : ℕ) : ∑' n : ℕ, (if n < k then (1 : ℝ≥0∞) else 0) = k := by
  rw [tsum_eq_sum (s := Finset.range k) ?_]
  · rw [Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_range.mp hn)]
    simp
  · intro n hn
    rw [if_neg]
    simpa using Finset.mem_range.not.mp hn

/-- **Tail-sum identity.**  For a `ℕ`-valued random variable `N`, the expectation
of `N` is the sum of its tail probabilities:
`∫⁻ ω, N ω ∂μ = ∑' n, μ {ω | n < N ω}`.

No hypothesis on `μ` beyond measurability of `N`; in particular `μ` need not be a
probability measure and `N` need not be integrable (both sides may be `∞`).

Mathlib has the continuous layer-cake formula
(`MeasureTheory.lintegral_eq_lintegral_meas_lt`) but not this discrete form. -/
theorem lintegral_natCast_eq_tsum_meas_lt {N : Ω → ℕ} (hN : Measurable N) :
    ∫⁻ ω, (N ω : ℝ≥0∞) ∂μ = ∑' n : ℕ, μ {ω | n < N ω} := by
  have hmeas : ∀ n : ℕ, MeasurableSet {ω | n < N ω} := fun n =>
    hN (MeasurableSet.of_discrete (s := {m : ℕ | n < m}))
  have key : (fun ω => (N ω : ℝ≥0∞))
      = fun ω => ∑' n : ℕ, Set.indicator {ω | n < N ω} 1 ω := by
    funext ω
    rw [← tsum_ite_lt_eq (N ω)]
    refine tsum_congr fun n => ?_
    by_cases h : n < N ω <;> simp [h]
  rw [key, lintegral_tsum fun n => (measurable_one.indicator (hmeas n)).aemeasurable]
  exact tsum_congr fun n => lintegral_indicator_one (hmeas n)

end TailSum

/-! ## Part 2: geometric tails give an expectation bound -/

section Bound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : Ω → ℕ}

/-- `ℕ` carries the discrete σ-algebra, so the cast `ℕ → ℝ` is measurable. -/
private lemma measurable_natCast_real : Measurable ((↑) : ℕ → ℝ) := Measurable.of_discrete

/-- A **one-step contraction** of the tails upgrades to a geometric tail bound.
If `μ` has total mass at most `1` (e.g. a probability measure) and the tails
contract by a factor `q` at every step, then `μ {ω | n < N ω} ≤ q ^ n`.

In the intended reading `N` is a round count, `μ {ω | n < N ω}` is the probability
of surviving `n` rounds, and the hypothesis says each further round fails with
probability at most `q`, conditionally on anything that came before. -/
theorem meas_lt_le_pow_of_step {q : ℝ≥0∞} (hμ : μ Set.univ ≤ 1)
    (hstep : ∀ n : ℕ, μ {ω | n + 1 < N ω} ≤ q * μ {ω | n < N ω}) (n : ℕ) :
    μ {ω | n < N ω} ≤ q ^ n := by
  induction n with
  | zero => simpa using (measure_mono (Set.subset_univ _)).trans hμ
  | succ n ih =>
      refine (hstep n).trans ?_
      rw [pow_succ, mul_comm (q ^ n) q]
      gcongr

/-- **Expected value from a geometric tail**, in `ℝ≥0∞` and at its most general:
if `μ {ω | n < N ω} ≤ q ^ n` for every `n`, then `∫⁻ ω, N ω ∂μ ≤ (1 - q)⁻¹`.

`N` is a count of *trials including the successful one* exactly when the tail at
`n` is the probability of surviving `n` trials; with `q = 1 - p` the bound reads
`1 / p`, which is `lintegral_natCast_le_inv_of_geometric_tail`. -/
theorem lintegral_natCast_le_of_geometric_tail (hN : Measurable N) {q : ℝ≥0∞}
    (htail : ∀ n : ℕ, μ {ω | n < N ω} ≤ q ^ n) :
    ∫⁻ ω, (N ω : ℝ≥0∞) ∂μ ≤ (1 - q)⁻¹ := by
  rw [lintegral_natCast_eq_tsum_meas_lt hN, ← ENNReal.tsum_geometric q]
  exact ENNReal.tsum_le_tsum htail

/-- **Expected round count of a `p`-successful loop is at most `1 / p`**, in `ℝ≥0∞`.

`μ {ω | n < N ω} ≤ (1 - p) ^ n` says "the probability of still running after `n`
rounds is at most `(1-p)^n`", i.e. every round succeeds with probability at least
`p`.  Then `E[N] ≤ p⁻¹`.  `N` counts **trials including the successful one**. -/
theorem lintegral_natCast_le_inv_of_geometric_tail (hN : Measurable N) {p : ℝ≥0∞}
    (hp : p ≤ 1) (htail : ∀ n : ℕ, μ {ω | n < N ω} ≤ (1 - p) ^ n) :
    ∫⁻ ω, (N ω : ℝ≥0∞) ∂μ ≤ p⁻¹ := by
  have h := lintegral_natCast_le_of_geometric_tail hN htail
  rwa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hp] at h

/-- The same bound with a **real** success probability `p ∈ (0, 1]`: the tail
hypothesis and the conclusion are both phrased through `ENNReal.ofReal`.
`N` counts **trials including the successful one**. -/
theorem lintegral_natCast_le_ofReal_inv (hN : Measurable N) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) (htail : ∀ n : ℕ, μ {ω | n < N ω} ≤ ENNReal.ofReal ((1 - p) ^ n)) :
    ∫⁻ ω, (N ω : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (1 / p) := by
  have h1p : (0 : ℝ) ≤ 1 - p := by linarith
  have hsub : ENNReal.ofReal (1 - p) = 1 - ENNReal.ofReal p := by
    rw [ENNReal.ofReal_sub _ hp0.le, ENNReal.ofReal_one]
  have htail' : ∀ n : ℕ, μ {ω | n < N ω} ≤ (1 - ENNReal.ofReal p) ^ n := by
    intro n
    refine (htail n).trans ?_
    rw [ENNReal.ofReal_pow h1p, hsub]
  have hple : ENNReal.ofReal p ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1
  refine (lintegral_natCast_le_inv_of_geometric_tail hN hple htail').trans_eq ?_
  rw [one_div, ENNReal.ofReal_inv_of_pos hp0]

/-- Under a geometric tail bound with a real `p ∈ (0, 1]`, the round count is
integrable — a finite expectation, so `∫` below is not the junk value `0`. -/
theorem integrable_natCast_of_geometric_tail (hN : Measurable N) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) (htail : ∀ n : ℕ, μ {ω | n < N ω} ≤ ENNReal.ofReal ((1 - p) ^ n)) :
    Integrable (fun ω => (N ω : ℝ)) μ := by
  have henorm : ∀ ω, ‖((N ω : ℝ))‖ₑ = (N ω : ℝ≥0∞) := by
    intro ω
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_natCast]
  refine ⟨(measurable_natCast_real.comp hN).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, funext henorm]
  exact lt_of_le_of_lt (lintegral_natCast_le_ofReal_inv hN hp0 hp1 htail) ENNReal.ofReal_lt_top

/-- **The consumer-facing statement.**  If every round of a loop succeeds with
probability at least `p ∈ (0, 1]` — packaged as the tail bound
`μ {ω | n < N ω} ≤ (1 - p) ^ n`, "still running after `n` rounds has probability
at most `(1-p)^n`" — then the expected number of rounds is at most `1 / p`.

`N` counts **trials including the successful one**, so at `p = 1` the bound is
`E[N] ≤ 1`, as it should be.  See `meas_lt_le_pow_of_step` for deriving the tail
hypothesis from a one-step conditional bound. -/
theorem integral_natCast_le_inv (hN : Measurable N) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (htail : ∀ n : ℕ, μ {ω | n < N ω} ≤ ENNReal.ofReal ((1 - p) ^ n)) :
    ∫ ω, (N ω : ℝ) ∂μ ≤ 1 / p := by
  have hnn : 0 ≤ᵐ[μ] fun ω => (N ω : ℝ) :=
    Filter.Eventually.of_forall fun ω => Nat.cast_nonneg (N ω)
  have hmeas := (measurable_natCast_real.comp hN).aestronglyMeasurable (μ := μ)
  have hlint : ∫⁻ ω, ENNReal.ofReal ((N ω : ℝ)) ∂μ ≤ ENNReal.ofReal (1 / p) := by
    refine le_trans (le_of_eq ?_) (lintegral_natCast_le_ofReal_inv hN hp0 hp1 htail)
    exact lintegral_congr fun ω => ENNReal.ofReal_natCast (N ω)
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  calc (∫⁻ ω, ENNReal.ofReal ((N ω : ℝ)) ∂μ).toReal
      ≤ (ENNReal.ofReal (1 / p)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    _ = 1 / p := ENNReal.toReal_ofReal (by positivity)

end Bound

/-! ## Part 3: the exact mean of Mathlib's `geometricMeasure` -/

section Exact

open ProbabilityTheory

variable {p : unitInterval}

private lemma coe_pos (hp : p ≠ 0) : 0 < (p : ℝ) :=
  lt_of_le_of_ne p.2.1 fun h => hp (Subtype.ext h.symm)

private lemma norm_one_sub_lt_one (hp : p ≠ 0) : ‖(1 - p : ℝ)‖ < 1 := by
  have h0 : 0 < (p : ℝ) := coe_pos hp
  have h1 : (p : ℝ) ≤ 1 := p.2.2
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

/-- **The mean of the geometric distribution, Mathlib's convention.**
`geometricMeasure p` is the law of the number of **failures before the first
success**, so its mean is `(1 - p) / p`, *not* `1 / p`. -/
theorem integral_geometricMeasure_id (hp : p ≠ 0) :
    ∫ n, (n : ℝ) ∂(geometricMeasure p) = (1 - p) / p := by
  have h0 : 0 < (p : ℝ) := coe_pos hp
  have hr := norm_one_sub_lt_one hp
  have hA : HasSum (fun n : ℕ => ((n : ℝ) * (1 - p) ^ n) * p)
      ((1 - p) / (1 - (1 - p)) ^ 2 * p) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).mul_right _
  rw [integral_geometricMeasure hp]
  rw [(show (fun n : ℕ => ((1 - p : ℝ) ^ n * p) • (n : ℝ))
      = fun n : ℕ => ((n : ℝ) * (1 - p) ^ n) * p by funext n; simp [smul_eq_mul]; ring)]
  rw [hA.tsum_eq, show (1 : ℝ) - (1 - (p : ℝ)) = (p : ℝ) by ring]
  have h0' : (p : ℝ) ≠ 0 := ne_of_gt h0
  field_simp

/-- **The mean of the geometric distribution, trials convention.**
The number of **trials up to and including the first success** is `1 +` the
number of failures, so its mean is `1 / p`.  This is the form a rejection loop
wants; `Arlib.Geometric.integral_natCast_le_inv` is its one-sided, monotone
counterpart for a success probability known only from below. -/
theorem integral_geometricMeasure_trials (hp : p ≠ 0) :
    ∫ n, ((n : ℝ) + 1) ∂(geometricMeasure p) = 1 / p := by
  have h0 : 0 < (p : ℝ) := coe_pos hp
  have hr := norm_one_sub_lt_one hp
  have hA : HasSum (fun n : ℕ => ((n : ℝ) * (1 - p) ^ n) * p)
      ((1 - p) / (1 - (1 - p)) ^ 2 * p) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).mul_right _
  have hB : HasSum (fun n : ℕ => ((1 - p : ℝ)) ^ n * p) 1 := hasSum_one_geometricMeasure hp
  have hAB := hA.add hB
  rw [integral_geometricMeasure hp]
  rw [(show (fun n : ℕ => ((1 - p : ℝ) ^ n * p) • ((n : ℝ) + 1))
      = fun n : ℕ => ((n : ℝ) * (1 - p) ^ n) * p + (1 - p : ℝ) ^ n * p by
        funext n; simp [smul_eq_mul]; ring)]
  rw [hAB.tsum_eq, show (1 : ℝ) - (1 - (p : ℝ)) = (p : ℝ) by ring]
  have h0' : (p : ℝ) ≠ 0 := ne_of_gt h0
  field_simp
  ring

end Exact

end Arlib.Geometric
