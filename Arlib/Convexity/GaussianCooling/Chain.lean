/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Arlib.Convexity.GaussianCooling.Variance

/-!
# The Gaussian cooling chain and its two endpoints

The Gaussian-cooling volume algorithm estimates `Vol(K)` by telescoping a chain of
Gaussian-annealed integrals

  `Z(i) = ∫_K exp(-‖x‖² / (2 σᵢ²)) dx`,

along a schedule `σ₀ < σ₁ < ⋯ < σ_{m-1}` whose last entry is replaced by the *unweighted*
integral `∫_K 1 = Vol(K)`. The telescoping product `Z(m)/Z(0) · Z(0)` then recovers the
volume from a starting value `Z(0)` that is a known constant (essentially the Gaussian
normalisation `(2πσ₀²)^{n/2}`) rather than an unknown one.

This file constructs that chain as explicit data and proves everything about it that is
**pure integration** — no probability space, no sampler, no Markov chain.

## Main definitions

* `Arlib.GaussianCooling.coolWeight m σsq i` — the phase-`i` weight
  `x ↦ exp(-‖x‖²/(2 σsq i))` for `i < m`, and the constant `1` for `i ≥ m`. Making the
  terminal weight literally `1` is what makes the hot endpoint exact.
* `Arlib.GaussianCooling.chain m σsq K i = ∫ x in K, coolWeight m σsq i x` — the chain.
* `Arlib.GaussianCooling.coolRatio m σsq i` — the pointwise phase ratio
  `coolWeight (i+1) / coolWeight i`; the score whose mean an unbiased per-phase estimator
  must reproduce.
* `Arlib.GaussianCooling.geomSchedule σ₀sq α i = σ₀sq (1 + α)ⁱ` — a concrete geometric
  schedule, so the family above is demonstrably non-empty.

## Main results

* `chain_end` — **the hot endpoint, exactly**: `chain m σsq K m = (volume K).toReal`.
  More generally `chain_of_ge` for every index `≥ m`.
* `chain_pos` — **positivity**: `0 < chain m σsq K i` for *every* `i`, assuming only
  `ball 0 1 ⊆ K` and `volume K ≠ ⊤`. Both hypotheses are load-bearing: the ball gives the
  body positive volume, and finiteness is what stops `ENNReal.toReal ⊤ = 0` from
  collapsing the terminal entry to `0`. Convexity of `K` is *not* needed.
* `chain_ge_ball` — the quantitative form of positivity that `chain_pos` is read off:
  `coolLow m σsq i · Vol(B₁) ≤ chain m σsq K i`.
* `chain_le_volume` — the trivial upper bound `chain m σsq K i ≤ Vol(K)`.
* `chain_zero_ge`, `chain_zero_le`, `chain_zero_mem_Icc` — **the cold endpoint**, two
  sided and in terms of `σ₀` and the inscribed unit ball alone:
  `e^{-1/(2σ₀²)} · Vol(B₁) ≤ chain m σsq K 0 ≤ (2πσ₀²)^{n/2}`.
  Both bounds are explicit constants independent of `K`, which is exactly what the
  telescope needs in order to start from a *known* quantity.
* `chain_ratio_eq` — **the deterministic ratio identity**:
  `∫_K coolRatio i x · (coolWeight i x / chain i) = chain (i+1) / chain i`,
  i.e. the phase-`i` ratio is the mean of `coolRatio i` against the phase-`i` density.
  `coolDensity_integral_eq_one` says that density really is normalised, and
  `coolRatio_of_succ_lt` / `coolRatio_of_last` give its closed form.
* `integral_gaussWeight_univ` — `∫_{ℝⁿ} e^{-‖x‖²/(2s)} = (2πs)^{n/2}`, the constant the
  cold endpoint is compared against.
* `chain_eq_G` — the bridge to `Arlib.GaussianCooling.G`: for `i < m`,
  `chain m σsq K i = G (indicator K 1) (σsq i)`, so §5.1's variance machinery applies to
  the chain unchanged.

## What this discharges, and what it does not

Against the hypothesis bundle of the volume algorithm (`Ttc.VolumeAlgorithm.cousinsVempala`
in the downstream development — *not* imported here, this file is `Ttc`-free):

* `hchain_pos` (`0 < chain K ε p i` for all `i`) — **discharged** by `chain_pos`.
* `hchain_end` (`chain K ε p (phases K ε p) = (volume K).toReal`) — **discharged** by
  `chain_end`, by construction: the terminal weight is the constant `1`, so the terminal
  entry is `∫_K 1` and `setIntegral_const` finishes it. No radius hypothesis `K ⊆ R·Bₙ`
  and no relative-error slack are needed; this is the exact equality, not the biased form.
* `hphase_mean` (`∫ W = chain (i+1) / chain i`) — **not touched.** `chain_ratio_eq`
  identifies the *target* of that hypothesis as a deterministic integral, but producing a
  random variable with that mean requires sampling from the phase-`i` density, which is
  out of scope here and is not attempted.
* `hphase_var`, `hphase_indep`, and all measurability / scheduling guards — **not
  touched.**

Nothing in this file is stated as an unproved `Prop`, and no hypothesis class is
introduced: every declaration below is either explicit data or a theorem proved outright.

## Duplication note

`gW_indicator` / `G_indicator_eq` / `integrableOn_const'` / the boundedness argument behind
`integrableOn_gaussWeight` exist in the downstream `Ttc.CV` namespace as well. Since
`Arlib` may not import `Ttc`, the versions needed here are reproved (as
`gW_indicator'`, `chain_eq_G`, `integrableOn_const'`, `integrableOn_coolWeight`). They are
general facts about Gaussian-weighted integrals over sets and belong on this side of the
split; the `Ttc` copies can be deleted in favour of these.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set

variable {n : ℕ}

/-! ## The Gaussian integral over all of `ℝⁿ`

The constant the cold endpoint of the chain is measured against. Mathlib supplies
`GaussianFourier.integral_rexp_neg_mul_sq_norm` for a general finite-dimensional real inner
product space; the only work here is putting it in the `-‖x‖²/(2s)` parametrisation and
reading `finrank ℝ (EuclSpace n) = n`. -/

/-- **The `n`-dimensional Gaussian integral.** `∫_{ℝⁿ} e^{-‖x‖²/(2s)} dx = (2πs)^{n/2}`
for every variance `s > 0`. -/
theorem integral_gaussWeight_univ (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ∫ x : EuclSpace n, Real.exp (-(‖x‖ ^ 2) / (2 * s))
      = (2 * Real.pi * s) ^ ((n : ℝ) / 2) := by
  have hs' : s ≠ 0 := hs.ne'
  have hb : (0 : ℝ) < 1 / (2 * s) := by positivity
  have key := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclSpace n) hb
  have hfun : (fun x : EuclSpace n => Real.exp (-(1 / (2 * s)) * ‖x‖ ^ 2))
      = fun x : EuclSpace n => Real.exp (-(‖x‖ ^ 2) / (2 * s)) := by
    funext x
    congr 1
    field_simp
  rw [hfun] at key
  rw [key, finrank_euclideanSpace_fin,
    show Real.pi / (1 / (2 * s)) = 2 * Real.pi * s by field_simp]

/-- The Gaussian weight is integrable on all of `ℝⁿ`. Read off from
`integral_gaussWeight_univ`: a non-integrable function has Bochner integral `0`, and
`(2πs)^{n/2} ≠ 0`. -/
theorem integrable_gaussWeight_univ (n : ℕ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : EuclSpace n => Real.exp (-(‖x‖ ^ 2) / (2 * s))) volume := by
  by_contra h
  have h0 := integral_undef h
  rw [integral_gaussWeight_univ n hs] at h0
  exact (Real.rpow_pos_of_pos (by positivity) ((n : ℝ) / 2)).ne' h0

/-! ## The cooling weights -/

/-- **The phase-`i` cooling weight** of an `m`-phase schedule with variances `σsq`:
the Gaussian `x ↦ e^{-‖x‖²/(2 σsq i)}` while `i < m`, and the constant `1` from the
terminal phase `i = m` onwards.

Making the terminal weight literally `1` is a deliberate design choice: it is what makes
the hot endpoint of the chain *exactly* `Vol(K)` (`chain_end`) rather than `Vol(K)` up to
a relative bias. -/
noncomputable def coolWeight (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) (x : EuclSpace n) : ℝ :=
  if i < m then Real.exp (-(‖x‖ ^ 2) / (2 * σsq i)) else 1

@[simp] theorem coolWeight_of_lt {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (h : i < m)
    (x : EuclSpace n) :
    coolWeight m σsq i x = Real.exp (-(‖x‖ ^ 2) / (2 * σsq i)) := if_pos h

@[simp] theorem coolWeight_of_ge {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (h : m ≤ i)
    (x : EuclSpace n) :
    coolWeight m σsq i x = 1 := if_neg (not_lt.2 h)

/-- The cooling weight is strictly positive — for *every* index, and with no hypothesis on
the schedule at all (`Real.exp` is positive whatever its argument, and the terminal weight
is `1`). This is what drives `chain_pos`. -/
theorem coolWeight_pos (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) (x : EuclSpace n) :
    0 < coolWeight m σsq i x := by
  unfold coolWeight
  split
  · exact Real.exp_pos _
  · exact one_pos

theorem coolWeight_ne_zero (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) (x : EuclSpace n) :
    coolWeight m σsq i x ≠ 0 := (coolWeight_pos m σsq i x).ne'

/-- The cooling weight is bounded by `1`, provided the phase variance is positive (so the
Gaussian exponent is nonpositive). -/
theorem coolWeight_le_one {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (hσ : 0 < σsq i)
    (x : EuclSpace n) : coolWeight m σsq i x ≤ 1 := by
  unfold coolWeight
  split
  · refine Real.exp_le_one_iff.2 ?_
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * σsq i)]
    nlinarith [sq_nonneg ‖x‖]
  · exact le_rfl

theorem continuous_coolWeight (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) :
    Continuous (coolWeight (n := n) m σsq i) := by
  unfold coolWeight
  split
  · fun_prop
  · exact continuous_const

/-- A constant is integrable on any set of finite volume. (Duplicated from
`Ttc.CV.integrableOn_const'`, which `Arlib` may not import.) -/
theorem integrableOn_const' {S : Set (EuclSpace n)} (hfin : volume S ≠ ⊤) (c : ℝ) :
    IntegrableOn (fun _ : EuclSpace n => c) S volume := by
  refine Measure.integrableOn_of_bounded (M := ‖c‖) hfin aestronglyMeasurable_const ?_
  filter_upwards with x using le_rfl

/-- The cooling weight is integrable on any set of finite volume: it is continuous and
bounded by `1`. -/
theorem integrableOn_coolWeight {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (hσ : 0 < σsq i)
    {S : Set (EuclSpace n)} (hfin : volume S ≠ ⊤) :
    IntegrableOn (coolWeight m σsq i) S volume := by
  refine Measure.integrableOn_of_bounded (M := 1) hfin
    (continuous_coolWeight m σsq i).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (coolWeight_pos m σsq i x)]
  exact coolWeight_le_one hσ x

/-- **The pointwise floor of the phase-`i` weight on the unit ball**: `e^{-1/(2 σsq i)}`
while `i < m`, and `1` afterwards. -/
noncomputable def coolLow (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i < m then Real.exp (-1 / (2 * σsq i)) else 1

theorem coolLow_pos (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) : 0 < coolLow m σsq i := by
  unfold coolLow
  split
  · exact Real.exp_pos _
  · exact one_pos

@[simp] theorem coolLow_of_lt {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (h : i < m) :
    coolLow m σsq i = Real.exp (-1 / (2 * σsq i)) := if_pos h

/-- On the unit ball the phase-`i` weight is at least `coolLow m σsq i`. -/
theorem coolLow_le_coolWeight {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (hσ : 0 < σsq i)
    {x : EuclSpace n} (hx : ‖x‖ ≤ 1) :
    coolLow m σsq i ≤ coolWeight m σsq i x := by
  unfold coolLow coolWeight
  split
  · refine Real.exp_le_exp.2 ?_
    have h2 : (0 : ℝ) < 2 * σsq i := by positivity
    rw [div_le_div_iff_of_pos_right h2]
    nlinarith [norm_nonneg x]
  · exact le_rfl

/-! ## The chain -/

/-- **The Gaussian cooling chain.** `chain m σsq K i` is the phase-`i` annealed integral

  `∫_K e^{-‖x‖²/(2 σsq i)} dx`   for `i < m`,   and   `∫_K 1 = Vol(K)`   for `i ≥ m`.

This is explicit data: an integral, not an assertion. -/
noncomputable def chain (m : ℕ) (σsq : ℕ → ℝ) (K : Set (EuclSpace n)) (i : ℕ) : ℝ :=
  ∫ x in K, coolWeight m σsq i x

theorem chain_def (m : ℕ) (σsq : ℕ → ℝ) (K : Set (EuclSpace n)) (i : ℕ) :
    chain m σsq K i = ∫ x in K, coolWeight m σsq i x := rfl

/-- For `i < m` the chain entry is the Gaussian integral over the body, written out. -/
theorem chain_of_lt {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (h : i < m) (K : Set (EuclSpace n)) :
    chain m σsq K i = ∫ x in K, Real.exp (-(‖x‖ ^ 2) / (2 * σsq i)) := by
  simp only [chain, coolWeight_of_lt h]

/-- **The hot end of the chain, exactly.** From the terminal index onwards the chain entry
*is* the volume: the weight is the constant `1` there, so the entry is `∫_K 1`. -/
theorem chain_of_ge {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (h : m ≤ i) (K : Set (EuclSpace n)) :
    chain m σsq K i = (volume K).toReal := by
  simp only [chain, coolWeight_of_ge h, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def]

/-- **The endpoint hypothesis of the volume algorithm, discharged.**
`chain m σsq K m = Vol(K)`, on the nose and with no side conditions whatsoever. -/
theorem chain_end (m : ℕ) (σsq : ℕ → ℝ) (K : Set (EuclSpace n)) :
    chain m σsq K m = (volume K).toReal :=
  chain_of_ge le_rfl K

/-! ## Positivity

The chain is strictly positive at every index. The two hypotheses used are exactly the two
the volume algorithm supplies and no more: `ball 0 1 ⊆ K` (so `K` has positive volume) and
`volume K ≠ ⊤` (so the weight is integrable on `K`, and so the terminal entry is not
`ENNReal.toReal ⊤ = 0`). Convexity of `K` is never used. -/

theorem volume_unitBall_ne_top : volume (ball (0 : EuclSpace n) 1) ≠ ⊤ :=
  measure_ball_lt_top.ne

theorem volume_unitBall_toReal_pos : 0 < (volume (ball (0 : EuclSpace n) 1)).toReal :=
  ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' volume_unitBall_ne_top

/-- **The quantitative lower bound on the chain.** Every entry dominates the phase floor
times the volume of the inscribed unit ball:

  `coolLow m σsq i · Vol(B₁) ≤ chain m σsq K i`.

The right-hand side of this is a constant that does not depend on `K`. -/
theorem chain_ge_ball {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : ℕ) :
    coolLow m σsq i * (volume (ball (0 : EuclSpace n) 1)).toReal ≤ chain m σsq K i := by
  have hB : volume (ball (0 : EuclSpace n) 1) ≠ ⊤ := volume_unitBall_ne_top
  have h1 : ∫ _x in ball (0 : EuclSpace n) 1, coolLow m σsq i
      ≤ ∫ x in ball (0 : EuclSpace n) 1, coolWeight m σsq i x := by
    refine setIntegral_mono_on (integrableOn_const' hB _)
      (integrableOn_coolWeight (hσ i) hB) measurableSet_ball ?_
    intro x hx
    exact coolLow_le_coolWeight (hσ i) (le_of_lt (mem_ball_zero_iff.1 hx))
  have h2 : ∫ x in ball (0 : EuclSpace n) 1, coolWeight m σsq i x ≤ chain m σsq K i := by
    refine setIntegral_mono_set (integrableOn_coolWeight (hσ i) hfin)
      (Filter.Eventually.of_forall fun x => (coolWeight_pos m σsq i x).le)
      (Filter.Eventually.of_forall fun x hx => hball hx)
  have h3 : ∫ _x in ball (0 : EuclSpace n) 1, coolLow m σsq i
      = coolLow m σsq i * (volume (ball (0 : EuclSpace n) 1)).toReal := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
  linarith [h1, h2, h3.le, h3.ge]

/-- **The positivity hypothesis of the volume algorithm, discharged.**
`0 < chain m σsq K i` for every index `i`, given a positive schedule, an inscribed unit
ball, and finite volume. -/
theorem chain_pos {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : ℕ) :
    0 < chain m σsq K i :=
  lt_of_lt_of_le
    (mul_pos (coolLow_pos m σsq i) volume_unitBall_toReal_pos)
    (chain_ge_ball hσ hball hfin i)

theorem chain_ne_zero {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : ℕ) :
    chain m σsq K i ≠ 0 := (chain_pos hσ hball hfin i).ne'

/-- The trivial upper bound: the weights are `≤ 1`, so every chain entry is at most the
volume. -/
theorem chain_le_volume {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (hσ : 0 < σsq i)
    {K : Set (EuclSpace n)} (hfin : volume K ≠ ⊤) :
    chain m σsq K i ≤ (volume K).toReal := by
  have h : chain m σsq K i ≤ ∫ _x in K, (1 : ℝ) :=
    integral_mono (integrableOn_coolWeight hσ hfin) (integrableOn_const' hfin 1)
      fun x => coolWeight_le_one hσ x
  rwa [setIntegral_const, smul_eq_mul, mul_one, measureReal_def] at h

/-! ## The cold endpoint

The point of the cooling chain is that its *first* entry is a known constant, so that the
telescoping product `chain 0 · ∏ᵢ (chain (i+1)/chain i)` computes `Vol(K)` from data the
algorithm can evaluate. Both bounds below are explicit and independent of `K`. -/

/-- **Cold endpoint, upper bound.** `chain m σsq K 0 ≤ (2π σ₀²)^{n/2}`: the body is
contained in `ℝⁿ` and the Gaussian weight is nonnegative, so the annealed integral is at
most the full Gaussian normalisation. -/
theorem chain_zero_le {m : ℕ} {σsq : ℕ → ℝ} (hm : 0 < m) (hσ : 0 < σsq 0)
    (K : Set (EuclSpace n)) :
    chain m σsq K 0 ≤ (2 * Real.pi * σsq 0) ^ ((n : ℝ) / 2) := by
  rw [chain_of_lt hm K, ← integral_gaussWeight_univ n hσ]
  refine setIntegral_le_integral (integrable_gaussWeight_univ n hσ) ?_
  filter_upwards with x using (Real.exp_pos _).le

/-- **Cold endpoint, lower bound.** `e^{-1/(2σ₀²)} · Vol(B₁) ≤ chain m σsq K 0`: the
inscribed unit ball already carries that much mass, since on it the Gaussian weight is at
least `e^{-1/(2σ₀²)}`.

This is the crude inscribed-ball bound, not the sharp
`(1 − δ)(2πσ₀²)^{n/2}` of the paper (which needs a Gaussian tail estimate for
`σ₀² ≲ 1/n`); it is nevertheless a *known* constant, which is all the telescope requires
of its starting point. -/
theorem chain_zero_ge {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j) (hm : 0 < m)
    {K : Set (EuclSpace n)} (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) :
    Real.exp (-1 / (2 * σsq 0)) * (volume (ball (0 : EuclSpace n) 1)).toReal
      ≤ chain m σsq K 0 := by
  have h := chain_ge_ball (m := m) hσ hball hfin 0
  rwa [coolLow_of_lt hm] at h

/-- **The cold endpoint, two-sided.** The first entry of the cooling chain is pinned
between two explicit constants that do not mention `K`:

  `e^{-1/(2σ₀²)} · Vol(B₁) ≤ chain m σsq K 0 ≤ (2π σ₀²)^{n/2}`. -/
theorem chain_zero_mem_Icc {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j) (hm : 0 < m)
    {K : Set (EuclSpace n)} (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) :
    chain m σsq K 0 ∈
      Icc (Real.exp (-1 / (2 * σsq 0)) * (volume (ball (0 : EuclSpace n) 1)).toReal)
        ((2 * Real.pi * σsq 0) ^ ((n : ℝ) / 2)) :=
  ⟨chain_zero_ge hσ hm hball hfin, chain_zero_le hm (hσ 0) K⟩

/-! ## The deterministic ratio identity

`chain (i+1) / chain i` is the mean of the pointwise ratio `coolRatio i` against the
phase-`i` probability density `coolWeight i / chain i` on `K`. This is the *target* of the
volume algorithm's `hphase_mean`: the number an unbiased per-phase estimator has to have as
its expectation. Producing such an estimator needs a sampler and is **not** done here. -/

/-- The pointwise phase ratio `coolWeight (i+1) x / coolWeight i x`. -/
noncomputable def coolRatio (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) (x : EuclSpace n) : ℝ :=
  coolWeight m σsq (i + 1) x / coolWeight m σsq i x

theorem coolRatio_pos (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) (x : EuclSpace n) :
    0 < coolRatio m σsq i x :=
  div_pos (coolWeight_pos m σsq (i + 1) x) (coolWeight_pos m σsq i x)

theorem coolRatio_mul_coolWeight (m : ℕ) (σsq : ℕ → ℝ) (i : ℕ) (x : EuclSpace n) :
    coolRatio m σsq i x * coolWeight m σsq i x = coolWeight m σsq (i + 1) x :=
  div_mul_cancel₀ _ (coolWeight_ne_zero m σsq i x)

/-- Closed form of the ratio at an interior phase step: it is again a Gaussian weight, with
the (positive) exponent `‖x‖²/2 · (1/σᵢ² − 1/σ²ᵢ₊₁)`. -/
theorem coolRatio_of_succ_lt {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (h : i + 1 < m)
    (x : EuclSpace n) :
    coolRatio m σsq i x
      = Real.exp (‖x‖ ^ 2 / 2 * (1 / σsq i - 1 / σsq (i + 1))) := by
  rw [coolRatio, coolWeight_of_lt h, coolWeight_of_lt (Nat.lt_of_succ_lt h),
    ← Real.exp_sub]
  congr 1
  field_simp
  ring

/-- Closed form of the ratio at the *final* step, where the next weight is the constant
`1`: the ratio is `e^{+‖x‖²/(2σᵢ²)}`, the reciprocal of the phase weight. -/
theorem coolRatio_of_last {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (h : i < m) (h' : m ≤ i + 1)
    (x : EuclSpace n) :
    coolRatio m σsq i x = Real.exp (‖x‖ ^ 2 / (2 * σsq i)) := by
  rw [coolRatio, coolWeight_of_ge h', coolWeight_of_lt h, one_div, ← Real.exp_neg]
  congr 1
  ring

/-- Beyond the terminal phase both weights are `1`, so the ratio is `1`: the telescope has
nothing left to do. -/
theorem coolRatio_of_ge {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (h : m ≤ i) (x : EuclSpace n) :
    coolRatio (n := n) m σsq i x = 1 := by
  rw [coolRatio, coolWeight_of_ge h, coolWeight_of_ge (h.trans (Nat.le_succ i)), div_one]

/-- The phase-`i` density `coolWeight i / chain i` really is a probability density on `K`:
it integrates to `1`. -/
theorem coolDensity_integral_eq_one {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (i : ℕ) :
    ∫ x in K, coolWeight m σsq i x / chain m σsq K i = 1 := by
  rw [integral_div]
  exact div_self (chain_ne_zero hσ hball hfin i)

/-- **The deterministic ratio identity.** The consecutive-phase ratio of the chain is the
mean of the pointwise ratio `coolRatio i` against the phase-`i` density on `K`:

  `∫_K coolRatio i x · (coolWeight i x / chain i) dx = chain (i+1) / chain i`.

This is pure integration — it holds with *no* hypotheses at all, since the identity
`coolRatio i · coolWeight i = coolWeight (i+1)` is pointwise and `chain i` is a constant
that factors out. It identifies the quantity `hphase_mean` asks an estimator to be unbiased
for; it does not supply that estimator. -/
theorem chain_ratio_eq (m : ℕ) (σsq : ℕ → ℝ) (K : Set (EuclSpace n)) (i : ℕ) :
    ∫ x in K, coolRatio m σsq i x * (coolWeight m σsq i x / chain m σsq K i)
      = chain m σsq K (i + 1) / chain m σsq K i := by
  have hpt : ∀ x : EuclSpace n,
      coolRatio m σsq i x * (coolWeight m σsq i x / chain m σsq K i)
        = coolWeight m σsq (i + 1) x / chain m σsq K i := by
    intro x
    rw [mul_div_assoc', coolRatio_mul_coolWeight]
  simp only [hpt]
  rw [integral_div]
  rfl

/-- The same identity with the normalisation left outside the integral. -/
theorem chain_ratio_eq' (m : ℕ) (σsq : ℕ → ℝ) (K : Set (EuclSpace n)) (i : ℕ) :
    chain m σsq K (i + 1) / chain m σsq K i
      = (∫ x in K, coolRatio m σsq i x * coolWeight m σsq i x) / chain m σsq K i := by
  simp only [coolRatio_mul_coolWeight]
  rfl

/-! ## Bridge to `G`

`Arlib.GaussianCooling.G` integrates a Gaussian-weighted density over all of `ℝⁿ`; applied
to the indicator of `K` it is exactly a chain entry. This lets §5.1's second-moment
machinery be read as a statement about the chain. -/

/-- The Gaussian weight against an indicator is the indicator of the Gaussian weight.
(Duplicated from `Ttc.CV.gW_indicator`, which `Arlib` may not import.) -/
theorem gW_indicator' (K : Set (EuclSpace n)) (s : ℝ) (x : EuclSpace n) :
    gW (Set.indicator K (1 : EuclSpace n → ℝ)) s x
      = Set.indicator K (fun y => Real.exp (-(‖y‖ ^ 2) / (2 * s))) x := by
  by_cases hx : x ∈ K <;>
    simp [gW, Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- For an interior phase, the chain entry is `G` of the indicator of `K`.
(Duplicated from `Ttc.CV.G_indicator_eq`, which `Arlib` may not import.) -/
theorem chain_eq_G {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (h : i < m) {K : Set (EuclSpace n)}
    (hKm : MeasurableSet K) :
    chain m σsq K i = G (Set.indicator K (1 : EuclSpace n → ℝ)) (σsq i) := by
  rw [chain_of_lt h K, G]
  rw [show (fun x => gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σsq i) x)
      = Set.indicator K (fun y => Real.exp (-(‖y‖ ^ 2) / (2 * σsq i))) from
    funext (gW_indicator' K (σsq i))]
  exact (integral_indicator hKm).symm

/-! ## A concrete schedule

The results above are stated for an arbitrary positive schedule `σsq : ℕ → ℝ`. Here is a
geometric one, so the family is demonstrably non-empty and the downstream construction has
something to instantiate with. -/

/-- The geometric variance schedule `σᵢ² = σ₀² (1 + α)ⁱ`. -/
noncomputable def geomSchedule (σ₀sq α : ℝ) (i : ℕ) : ℝ := σ₀sq * (1 + α) ^ i

@[simp] theorem geomSchedule_zero (σ₀sq α : ℝ) : geomSchedule σ₀sq α 0 = σ₀sq := by
  simp [geomSchedule]

theorem geomSchedule_pos {σ₀sq α : ℝ} (h0 : 0 < σ₀sq) (hα : 0 < 1 + α) (i : ℕ) :
    0 < geomSchedule σ₀sq α i :=
  mul_pos h0 (pow_pos hα i)

/-- The schedule is increasing: the Gaussians really do flatten out along the chain. -/
theorem geomSchedule_strictMono {σ₀sq α : ℝ} (h0 : 0 < σ₀sq) (hα : 0 < α) :
    StrictMono (geomSchedule σ₀sq α) := by
  intro i j hij
  have h1 : (1 : ℝ) < 1 + α := by linarith
  have h2 : (1 + α) ^ i < (1 + α) ^ j := pow_lt_pow_right₀ h1 hij
  simpa [geomSchedule] using mul_lt_mul_of_pos_left h2 h0

end Arlib.GaussianCooling

