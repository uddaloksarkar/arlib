/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Probability.TV
import Arlib.MarkovChains.Continuous.SpeedyExactOnShrunken

/-!
# Mapping the speedy law to the target: Cousins–Vempala `lem:map-speedy-to-ball` at `δ ≤ 1/(2n)`

Cousins–Vempala's `lem:map-speedy-to-ball` (`1409.6011/vol3_journal.tex:942`) turns a sample
from the speedy walk's stationary law `Q̂ ∝ 1_K·ℓ·f` into a sample from the target `Q ∝ 1_K·f`,
`f(x) = e^{−‖x‖²/(2s)}`, by a rejection routine at shrink factor `c = 1 − 1/(2n)`:

1. condition on the shrunken body `c·K` (draw until the sample lands there);
2. rescale, `v = u/c`;
3. accept `v` with probability `f(v)/f(cv)`, else restart.

In the regime `δ ≤ 1 − c = 1/(2n)` the correction is **exact** on `c·K`
(`Arlib.MarkovChains.condOn_ellGaussianMeasure_shrunken`, proved in
`SpeedyExactOnShrunken.lean`: conditioning `Q̂` and `Q` on `c·K` gives literally the *same*
probability measure), so every remaining loss is bookkeeping about conditioning and
renormalisation.  This file does that bookkeeping and closes the lemma.

## What is proved

**1. Total variation under conditioning.**
* `Arlib.TVLe.condOn` — if `TVLe μ ν ε` and both measures put mass `≥ m > 0` on `A`, then
  `TVLe (condOn μ A) (condOn ν A) (2ε/m)`.
* `Arlib.tvLe_condOn_half` — the case `ν A ≥ 1/2`: the constant is **`8ε`**, with no
  smallness hypothesis on `ε`.

**2. Rescaling.**
* `Arlib.MarkovChains.map_inv_smul_gaussian_restrict` — the pushforward of `1_{c·K}·γ_s`
  under `x ↦ x/c` is `cⁿ · 1_K·γ_{s/c²}`.  So the density `z(v) = f(c·v)` of the paper is
  the Gaussian of *inflated variance* `s/c²`, and the Jacobian `cⁿ` is the constant that
  normalisation removes.
* `Arlib.MarkovChains.map_inv_smul_condOn_shrunken` — hence the rescaled shrunken target is
  exactly the normalised `1_K·γ_{s/c²}`.  Combined with `Arlib.TVLe.map`, rescaling is free.

**3. The acceptance filter.**
* `Arlib.MarkovChains.speedyAcceptReal c s v = exp(−(1−c²)‖v‖²/(2s))` — the acceptance
  probability `f(v)/f(cv)`, with its defining identity proved in
  `Arlib.MarkovChains.gaussianWeightReal_div_mul_speedyAcceptReal`
  (`z(v)·accept(v) = f(v)`), not merely asserted by the name.
* `Arlib.MarkovChains.speedyAcceptReal_le_one` — it is `≤ 1`, hence a probability, whenever
  `c² ≤ 1`.
* `Arlib.MarkovChains.exp_neg_eight_le_speedyAcceptReal` — it is `≥ e^{−8}`, an absolute
  constant, when `‖v‖ ≤ 4√(sn)` (i.e. `K ⊆ R·Bₙ` with `R ≤ 4σ√n`) and `1 − c² ≤ 1/n`; the
  latter holds at `c = 1 − 1/(2n)` by `Arlib.MarkovChains.one_sub_sq_shrink_le_inv`.
* `Arlib.MarkovChains.withDensity_gaussian_mul_speedyAccept` — rejection sampling is
  **exact**: weighting the proposal `1_K·γ_{s/c²}` by the acceptance probability returns
  `1_K·γ_s` on the nose.
* `Arlib.MarkovChains.pow_le_acceptance_ratio` — the *expected* acceptance probability is at
  least `cⁿ ≥ 1/2`, a sharper bound than the pointwise `e^{−8}`; so the expected number of
  rejection rounds in step 3 is at most `2`.  Step 1's expected number of rounds is at most
  `4` by `Arlib.MarkovChains.quarter_le_shrunken_mass`.

**4. The assembly.**
* `Arlib.MarkovChains.tvLe_speedyRejection_target_of` (abstract shrink factor) and
  `Arlib.MarkovChains.tvLe_speedyRejection_target` (at `c = 1 − 1/(2n)`) — the headline.

## The constant achieved: `64·ε`, for `ε ≤ 1/32`

**Not** Cousins–Vempala's `10ε`.  The breakdown is `64 = 2·8·(1/(1/4))`:

| step | cost |
| --- | --- |
| condition on `c·K` | `×8` (`Arlib.tvLe_condOn_half`, since `Q̂(c·K) ≥ 1/2`) |
| rescale by `1/c` | free (`Arlib.TVLe.map`) |
| correct `ℓ` on `c·K` | free — it is an *equality* here, not an estimate |
| apply the acceptance filter | free (`Arlib.TVLe.withDensity`) |
| renormalise after the filter | `×8` (acceptance mass `≥ cⁿ ≥ 1/2`) |

The last row is the interesting one, and it is **a step Cousins–Vempala's proof does not
take**.  Their argument establishes that the rejection routine maps the *idealised* proposal
`Z` exactly to `Q`, and stops there; but the routine is actually run on `P'`, not on `Z`, and
conditioning on acceptance inflates total variation by the reciprocal of the acceptance mass.
Formalisation forces that factor into the open.  It is a constant, so the shape of the lemma
("a constant number of samples, error `O(ε)`") survives; the specific `10ε` does not.

## Scope and hypotheses carried

* **The regime is `δ ≤ 1 − c`**, stronger than Cousins–Vempala's step size; see
  `KLS97Shell.lean`'s module docstring for what that costs (an `n³` rather than `n²` mixing
  bound).  It is what makes the `ℓ`-correction exact.
* The sampler's law `P` enters only as "some probability measure within `ε` of `Q̂`"; nothing
  here proves that a walk reaches such a `P` — that is the mixing theorem, elsewhere.
* `volume K ≠ ⊤` and `B₁ ⊆ K` are carried throughout (finiteness and nondegeneracy of the
  Gaussian masses).  `K ⊆ R·Bₙ` is used only by the pointwise `e^{−8}` bound, which the
  assembly does not need.
* The *expected number of rounds* is delivered as acceptance-mass lower bounds
  (`pow_le_acceptance_ratio`, `quarter_le_shrunken_mass`); the geometric-series expectation
  itself is not formalised, since no loop model is defined in this development.

The generic lemmas in §1 (`Arlib.TVLe.condOn`, `Arlib.TVLe.withDensity`,
`Arlib.condOn_smul`, …) have no project-specific content and are extraction candidates for
`Arlib/Probability/TV.lean` and `Arlib/Probability/Rejection.lean`.

The only `def` here is `Arlib.MarkovChains.speedyAcceptReal`, and its name's semantic promise
is discharged by `Arlib.MarkovChains.gaussianWeightReal_div_mul_speedyAcceptReal`.  There is
no `structure`, `class` or `axiom`.
-/

namespace Arlib

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## 1. Total variation under conditioning -/

/-- `a⁻¹ * a ≤ 1` in `ℝ≥0∞`, including the degenerate cases `a = 0` and `a = ⊤`. -/
theorem inv_mul_self_le_one (a : ℝ≥0∞) : a⁻¹ * a ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | h0
  · simp
  rcases eq_or_ne a ⊤ with rfl | htop
  · simp
  · exact le_of_eq (ENNReal.inv_mul_cancel h0 htop)

/-- **A conditional law never exceeds `1`**, for *any* measure and *any* pair of sets — no
measurability, no finiteness.  The degenerate cases are covered by the `ℝ≥0∞` conventions
`(0)⁻¹ = ⊤`, `(⊤)⁻¹ = 0` and `⊤ * 0 = 0`. -/
theorem condOn_le_one (μ : Measure Ω) (A S : Set Ω) : condOn μ A S ≤ 1 := by
  rw [condOn_def, Measure.smul_apply, smul_eq_mul]
  calc (μ A)⁻¹ * μ.restrict A S ≤ (μ A)⁻¹ * μ.restrict A univ :=
        mul_le_mul_right (measure_mono (subset_univ _)) _
    _ = (μ A)⁻¹ * μ A := by rw [Measure.restrict_apply_univ]
    _ ≤ 1 := inv_mul_self_le_one _

/-- Two conditional laws are always within total variation distance `1`.  Used for the
degenerate branch of `Arlib.tvLe_condOn_half`, where the hypothesis `ε` is already so large
that the conclusion is vacuous. -/
theorem tvLe_condOn_one (μ ν : Measure Ω) (A : Set Ω) :
    TVLe (condOn μ A) (condOn ν A) 1 := fun S _ =>
  ⟨le_add_left (condOn_le_one μ A S), le_add_left (condOn_le_one ν A S)⟩

/-- The real-arithmetic core of `Arlib.TVLe.condOn`.

With `a ≤ b + e` (numerators close), `q ≤ p + e` (denominators close), `b ≤ q`, and both
denominators bounded below by `M > 0`,

    a / p ≤ b / q + 2 * e / M.

The proof is the exact computation
`a/p − b/q = (q(a−b) + b(q−p)) / (pq) ≤ (qe + qe)/(pq) = 2e/p ≤ 2e/M`. -/
theorem div_le_div_add_two_mul_div {a b p q e M : ℝ} (hM : 0 < M) (hMp : M ≤ p)
    (hMq : M ≤ q) (hb : 0 ≤ b) (hbq : b ≤ q) (hab : a ≤ b + e) (hqp : q ≤ p + e)
    (he : 0 ≤ e) : a / p ≤ b / q + 2 * e / M := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le hM hMq
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hM hMp
  set r : ℝ := b / q with hrdef
  have hrq : r * q = b := div_mul_cancel₀ b hq0.ne'
  have hr0 : 0 ≤ r := div_nonneg hb hq0.le
  have hr1 : r ≤ 1 := (div_le_one hq0).2 hbq
  rw [div_le_iff₀ hp0]
  have hexp : (r + 2 * e / M) * p = r * p + 2 * e / M * p := by ring
  rw [hexp]
  have h1 : r * q ≤ r * p + r * e := by nlinarith [mul_nonneg hr0 (by linarith : (0:ℝ) ≤ p + e - q)]
  have h2 : r * e ≤ e := by nlinarith
  have h3 : 2 * e / M * M = 2 * e := div_mul_cancel₀ _ hM.ne'
  have hcoef : (0 : ℝ) ≤ 2 * e / M := by positivity
  have h4 : 2 * e / M * M ≤ 2 * e / M * p := by nlinarith
  linarith

/-- One direction of `Arlib.TVLe.condOn`, isolated so that the symmetric statement can apply
it twice with the roles of the two measures exchanged. -/
theorem condOn_le_condOn_add {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A S : Set Ω} (hA : MeasurableSet A) (hS : MeasurableSet S) {ε m : ℝ≥0∞}
    (hεtop : ε ≠ ⊤) (hm : 0 < m) (hmtop : m ≠ ⊤) (hμA : m ≤ μ A) (hνA : m ≤ ν A)
    (h1 : μ (S ∩ A) ≤ ν (S ∩ A) + ε) (h2 : ν A ≤ μ A + ε) :
    condOn μ A S ≤ condOn ν A S + 2 * ε / m := by
  rw [condOn_apply μ hA hS, condOn_apply ν hA hS]
  have hpne : μ A ≠ ⊤ := measure_ne_top μ A
  have hqne : ν A ≠ ⊤ := measure_ne_top ν A
  have hane : μ (S ∩ A) ≠ ⊤ := measure_ne_top μ _
  have hbne : ν (S ∩ A) ≠ ⊤ := measure_ne_top ν _
  have hp0 : μ A ≠ 0 := (lt_of_lt_of_le hm hμA).ne'
  have hq0 : ν A ≠ 0 := (lt_of_lt_of_le hm hνA).ne'
  have hL : μ (S ∩ A) / μ A ≠ ⊤ := ENNReal.div_ne_top hane hp0
  have hquot : ν (S ∩ A) / ν A ≠ ⊤ := ENNReal.div_ne_top hbne hq0
  have hslack : 2 * ε / m ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) hεtop) hm.ne'
  have hR : ν (S ∩ A) / ν A + 2 * ε / m ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hquot, hslack⟩
  rw [← ENNReal.toReal_le_toReal hL hR, ENNReal.toReal_add hquot hslack,
    ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_mul]
  refine div_le_div_add_two_mul_div (M := m.toReal) (ENNReal.toReal_pos hm.ne' hmtop)
    (ENNReal.toReal_mono hpne hμA) (ENNReal.toReal_mono hqne hνA) ENNReal.toReal_nonneg
    (ENNReal.toReal_mono hqne (measure_mono inter_subset_right)) ?_ ?_ ENNReal.toReal_nonneg
  · have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hbne, hεtop⟩) h1
    rwa [ENNReal.toReal_add hbne hεtop] at this
  · have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hpne, hεtop⟩) h2
    rwa [ENNReal.toReal_add hpne hεtop] at this

/-- **Total variation under conditioning.**

If `μ` and `ν` are within total variation distance `ε` and both put mass at least `m > 0`
on the event `A`, then the conditional laws `condOn μ A` and `condOn ν A` are within
`2ε/m`.

The constant is sharp for this argument: the numerator error contributes `ε/m` and the
denominator error contributes another `ε/m`. -/
theorem TVLe.condOn {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ε : ℝ≥0∞}
    (h : TVLe μ ν ε) {A : Set Ω} (hA : MeasurableSet A) {m : ℝ≥0∞} (hm : 0 < m)
    (hμA : m ≤ μ A) (hνA : m ≤ ν A) :
    TVLe (Arlib.condOn μ A) (Arlib.condOn ν A) (2 * ε / m) := by
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top μ A) hμA
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · have : 2 * (⊤ : ℝ≥0∞) / m = ⊤ := by
      rw [ENNReal.mul_top (by simp), ENNReal.top_div_of_ne_top hmtop]
    rw [this]
    exact tvLe_top _ _
  intro S hS
  exact ⟨condOn_le_condOn_add hA hS hεtop hm hmtop hμA hνA
      (h.left (hS.inter hA)) (h.right hA),
    condOn_le_condOn_add hA hS hεtop hm hmtop hνA hμA
      (h.right (hS.inter hA)) (h.left hA)⟩

/-- **Total variation under conditioning on a `1/2`-mass event: the constant is `8ε`.**

This is step 1 of Cousins–Vempala's `lem:map-speedy-to-ball`.  If the sampler's law `μ` is
within `ε` of the target `ν` and `ν` puts at least half its mass on `A`, then conditioning
both on `A` costs a factor `8`:

    TVLe (condOn μ A) (condOn ν A) (8 * ε).

No smallness hypothesis on `ε` is needed: for `ε > 1/4` the bound `8ε > 1` is already
vacuous (`Arlib.tvLe_condOn_one`), and for `ε ≤ 1/4` the hypothesis forces
`μ A ≥ 1/2 − ε ≥ 1/4`, so `Arlib.TVLe.condOn` applies with `m = 1/4` and `2ε/(1/4) = 8ε`. -/
theorem tvLe_condOn_half {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ≥0∞} (h : TVLe μ ν ε) {A : Set Ω} (hA : MeasurableSet A)
    (hνA : ENNReal.ofReal (1 / 2) ≤ ν A) :
    TVLe (condOn μ A) (condOn ν A) (8 * ε) := by
  have hofReal4 : ENNReal.ofReal (1 / 4) = (4 : ℝ≥0∞)⁻¹ := by
    rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      show ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) by simp]
  have hofReal8 : ENNReal.ofReal (1 / 8) = (8 : ℝ≥0∞)⁻¹ := by
    rw [show (1 : ℝ) / 8 = (8 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      show ENNReal.ofReal (8 : ℝ) = (8 : ℝ≥0∞) by simp]
  have hq : ENNReal.ofReal (1 / 4) ≤ ν A :=
    le_trans (ENNReal.ofReal_le_ofReal (by norm_num)) hνA
  rcases le_or_gt ε (ENNReal.ofReal (1 / 4)) with hε | hε
  · have hp : ENNReal.ofReal (1 / 4) ≤ μ A := by
      refine ENNReal.le_of_add_le_add_right
        (show ENNReal.ofReal (1 / 4) ≠ (⊤ : ℝ≥0∞) from ENNReal.ofReal_ne_top) ?_
      calc ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4)
          = ENNReal.ofReal (1 / 2) := by
            rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
        _ ≤ ν A := hνA
        _ ≤ μ A + ε := h.right hA
        _ ≤ μ A + ENNReal.ofReal (1 / 4) := by gcongr
    have key := h.condOn hA (m := ENNReal.ofReal (1 / 4))
      (ENNReal.ofReal_pos.2 (by norm_num)) hp hq
    have hconst : 2 * ε / ENNReal.ofReal (1 / 4) = 8 * ε := by
      rw [hofReal4, ENNReal.div_eq_inv_mul, inv_inv]
      ring
    rwa [hconst] at key
  · refine (tvLe_condOn_one μ ν A).mono ?_
    calc (1 : ℝ≥0∞) = 8 * ENNReal.ofReal (1 / 8) := by
          rw [hofReal8, ENNReal.mul_inv_cancel (by simp) (by simp)]
      _ ≤ 8 * ε := by
          gcongr
          exact le_of_lt (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by norm_num)) hε)

/-! ## 1b. `condOn` versus rescaling and pushforward

Three bookkeeping lemmas about `Arlib.condOn` that the rescaling step of
`lem:map-speedy-to-ball` needs.  All three are generic; none mentions a Gaussian. -/

/-- **Conditioning is insensitive to a positive finite rescaling of the measure.**  This is
why the Jacobian `cⁿ` of the rescaling `x ↦ x/c` cancels: it multiplies the unnormalised
measure by a constant, which normalisation removes. -/
theorem condOn_smul {a : ℝ≥0∞} (ha0 : a ≠ 0) (hatop : a ≠ ⊤) (μ : Measure Ω) (S : Set Ω) :
    condOn (a • μ) S = condOn μ S := by
  rw [condOn_def, condOn_def, Measure.smul_apply, smul_eq_mul, Measure.restrict_smul,
    smul_smul, ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop), mul_right_comm,
    ENNReal.inv_mul_cancel ha0 hatop, one_mul]

/-- **Conditioning on `S` is exactly normalising the restriction to `S`.** -/
theorem condOn_restrict_univ (μ : Measure Ω) (S : Set Ω) :
    condOn (μ.restrict S) univ = condOn μ S := by
  rw [condOn_def, condOn_def, Measure.restrict_apply_univ, Measure.restrict_univ]

/-- **Pushforward commutes with normalisation**: normalising and then mapping is the same as
mapping and then normalising, because a measurable map preserves total mass. -/
theorem map_condOn_univ {Ω' : Type*} [MeasurableSpace Ω'] {T : Ω → Ω'} (hT : Measurable T)
    (μ : Measure Ω) :
    Measure.map T (condOn μ univ) = condOn (Measure.map T μ) univ := by
  rw [condOn_def, condOn_def, Measure.restrict_univ, Measure.restrict_univ,
    Measure.map_smul, Measure.map_apply hT MeasurableSet.univ, preimage_univ]

/-! ## 1c. Total variation under an acceptance filter

Reweighting two measures by the *same* `[0,1]`-valued acceptance probability cannot increase
the total variation distance between them.  This is the step that carries the sampler's error
through the rejection test; it is the step Cousins–Vempala's proof omits (see the module
docstring). -/

/-- A `[0,1]`-valued density evaluated on a measurable set, as a Bochner integral. -/
theorem withDensity_ofReal_apply {μ : Measure Ω} [IsFiniteMeasure μ] {w : Ω → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) {S : Set Ω}
    (hS : MeasurableSet S) :
    (μ.withDensity fun x => ENNReal.ofReal (w x)) S
      = ENNReal.ofReal (∫ x, S.indicator w x ∂μ) := by
  have hind : Measurable (S.indicator w) := hw.indicator hS
  have hind0 : ∀ x, 0 ≤ S.indicator w x := fun x =>
    Set.indicator_nonneg (fun y _ => hw0 y) x
  have hind1 : ∀ x, S.indicator w x ≤ 1 := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]; exact hw1 x
    · rw [Set.indicator_of_notMem hx]; norm_num
  rw [withDensity_apply _ hS, ← lintegral_indicator hS,
    ofReal_integral_eq_lintegral_ofReal (integrable_of_forall_mem_Icc hind hind0 hind1)
      (Filter.Eventually.of_forall hind0)]
  congr 1
  funext x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]

/-- **A `1/2`-mass event under `ν` still has mass `1/4` under an `ε`-close `μ`**, provided
`ε ≤ 1/4`.  Used both to start the conditioning step and to bound the acceptance mass of the
sampler's own law. -/
theorem quarter_le_of_tvLe {μ ν : Measure Ω} {ε : ℝ≥0∞} (h : TVLe μ ν ε) {A : Set Ω}
    (hA : MeasurableSet A) (hνA : ENNReal.ofReal (1 / 2) ≤ ν A)
    (hε : ε ≤ ENNReal.ofReal (1 / 4)) : ENNReal.ofReal (1 / 4) ≤ μ A := by
  refine ENNReal.le_of_add_le_add_right
    (show ENNReal.ofReal (1 / 4) ≠ (⊤ : ℝ≥0∞) from ENNReal.ofReal_ne_top) ?_
  calc ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4)
      = ENNReal.ofReal (1 / 2) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    _ ≤ ν A := hνA
    _ ≤ μ A + ε := h.right hA
    _ ≤ μ A + ENNReal.ofReal (1 / 4) := by gcongr

/-- **Conditioning a normalised measure is conditioning the measure.** -/
theorem condOn_condOn_univ (μ : Measure Ω) (S : Set Ω) (h0 : μ univ ≠ 0) (htop : μ univ ≠ ⊤) :
    condOn (condOn μ univ) S = condOn μ S := by
  rw [condOn_def μ univ, Measure.restrict_univ]
  exact condOn_smul (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0) μ S

/-- Weighting a finite measure by a density bounded by `1` keeps it finite. -/
theorem isFiniteMeasure_withDensity_le_one {μ : Measure Ω} [IsFiniteMeasure μ] {g : Ω → ℝ≥0∞}
    (hg : ∀ x, g x ≤ 1) : IsFiniteMeasure (μ.withDensity g) := by
  constructor
  calc (μ.withDensity g) univ = ∫⁻ x in univ, g x ∂μ := withDensity_apply _ MeasurableSet.univ
    _ ≤ ∫⁻ _ in univ, (1 : ℝ≥0∞) ∂μ := lintegral_mono hg
    _ = μ univ := by rw [Measure.restrict_univ, lintegral_one]
    _ < ⊤ := measure_lt_top _ _

/-- Rescaling a measure commutes with taking a density. -/
theorem withDensity_smul_measure (a : ℝ≥0∞) (μ : Measure Ω) (g : Ω → ℝ≥0∞) :
    (a • μ).withDensity g = a • μ.withDensity g := by
  ext S hS
  rw [withDensity_apply _ hS, Measure.restrict_smul, lintegral_smul_measure,
    Measure.smul_apply, withDensity_apply _ hS, smul_eq_mul]

/-- **The acceptance filter does not increase total variation distance.**

If `μ` and `ν` are within `ε` and every point is accepted with the *same* probability
`w x ∈ [0,1]`, the two accepted (sub-probability) laws `μ.withDensity w` and
`ν.withDensity w` are still within `ε`.

Proved from `Arlib.TVLe.integral_le` applied to the `[0,1]`-valued observable
`1_S · w`. -/
theorem TVLe.withDensity {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ≥0∞} (h : TVLe μ ν ε) (hε : ε ≠ ⊤) {w : Ω → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    TVLe (μ.withDensity fun x => ENNReal.ofReal (w x))
      (ν.withDensity fun x => ENNReal.ofReal (w x)) ε := by
  intro S hS
  have hind : Measurable (S.indicator w) := hw.indicator hS
  have hind0 : ∀ x, 0 ≤ S.indicator w x := fun x =>
    Set.indicator_nonneg (fun y _ => hw0 y) x
  have hind1 : ∀ x, S.indicator w x ≤ 1 := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]; exact hw1 x
    · rw [Set.indicator_of_notMem hx]; norm_num
  have habs := h.integral_le hε hind hind0 hind1
  rw [abs_sub_le_iff] at habs
  have hμ0 : (0 : ℝ) ≤ ∫ x, S.indicator w x ∂μ := integral_nonneg hind0
  have hν0 : (0 : ℝ) ≤ ∫ x, S.indicator w x ∂ν := integral_nonneg hind0
  rw [withDensity_ofReal_apply hw hw0 hw1 hS, withDensity_ofReal_apply hw hw0 hw1 hS,
    ← ENNReal.ofReal_toReal hε]
  refine ⟨?_, ?_⟩
  · rw [← ENNReal.ofReal_add hν0 ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal (by linarith [habs.1])
  · rw [← ENNReal.ofReal_add hμ0 ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal (by linarith [habs.2])

end Arlib

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 2. The acceptance filter `f(v)/f(cv)` -/

/-- **The acceptance probability of Cousins–Vempala's rejection step**, as a real number:

    accept `v` with probability  `f(v)/f(cv) = exp(−(1−c²)‖v‖²/(2s))`.

Here `f = gaussianWeightReal s` is the unnormalised Gaussian weight `e^{−‖x‖²/(2s)}` and `v`
is the rescaled point `u/c`.  The name is justified by
`Arlib.MarkovChains.gaussianWeightReal_div_mul_speedyAcceptReal`, which proves the defining
identity `f(cv)·accept(v) = f(v)` rather than merely asserting it. -/
noncomputable def speedyAcceptReal (c s : ℝ) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-((1 - c ^ 2) * ‖v‖ ^ 2) / (2 * s))

/-- The acceptance probability is strictly positive, so the rejection loop terminates almost
surely for any body. -/
theorem speedyAcceptReal_pos (c s : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    0 < speedyAcceptReal c s v := Real.exp_pos _

/-- **The defining identity of the acceptance filter.**  The proposal density at `v` is
`z(v) = f(cv) = gaussianWeightReal (s/c²) v`, and multiplying it by the acceptance
probability returns exactly the target density `f(v)`:

    gaussianWeightReal (s/c²) v · speedyAcceptReal c s v = gaussianWeightReal s v.

This is what makes the rejection routine *exact*, and it is the reason `speedyAcceptReal`
may be named "the acceptance probability" at all. -/
theorem gaussianWeightReal_div_mul_speedyAcceptReal {c s : ℝ} (hc : c ≠ 0) (hs : s ≠ 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    gaussianWeightReal (s / c ^ 2) v * speedyAcceptReal c s v = gaussianWeightReal s v := by
  rw [gaussianWeightReal, speedyAcceptReal, ← Real.exp_add, gaussianWeightReal]
  congr 1
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  field_simp
  ring

/-- **The acceptance probability is at most `1`**, hence a genuine probability, as soon as
the shrink factor satisfies `c² ≤ 1`.  The exponent `−(1−c²)‖v‖²/(2s)` is then nonpositive. -/
theorem speedyAcceptReal_le_one {c s : ℝ} (hs : 0 < s) (hc : c ^ 2 ≤ 1)
    (v : EuclideanSpace ℝ (Fin n)) : speedyAcceptReal c s v ≤ 1 := by
  rw [speedyAcceptReal, Real.exp_le_one_iff, neg_div]
  refine neg_nonpos.2 (div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith))

/-- **At `c = 1 − 1/(2n)` the shrink factor costs at most `1/n` in the exponent**:
`1 − c² = 1/n − 1/(4n²) ≤ 1/n`. -/
theorem one_sub_sq_shrink_le_inv {n : ℕ} (hn : 1 ≤ n) :
    1 - (1 - 1 / (2 * (n : ℝ))) ^ 2 ≤ 1 / (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have h2 : 2 * (1 / (2 * (n : ℝ))) = 1 / (n : ℝ) := by field_simp
  nlinarith [sq_nonneg (1 / (2 * (n : ℝ)))]

/-- **The shrink factor `c = 1 − 1/(2n)` satisfies `c² ≤ 1`** for `n ≥ 1`. -/
theorem sq_shrink_le_one {n : ℕ} (hn : 1 ≤ n) : (1 - 1 / (2 * (n : ℝ))) ^ 2 ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have h0 : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
  have h1 : 1 / (2 * (n : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  nlinarith

/-- **The acceptance probability is bounded below by the absolute constant `e^{−8}`.**

This is the quantitative half of Cousins–Vempala's "which is at least a constant since
`‖x‖ ≤ 4σ√n`".  On a body contained in the ball of radius `R ≤ 4σ√n = 4√(sn)`, and at a
shrink factor with `1 − c² ≤ 1/n` (which `Arlib.MarkovChains.one_sub_sq_shrink_le_inv` gives
for `c = 1 − 1/(2n)`), the exponent obeys

    (1 − c²)‖v‖²/(2s) ≤ (1/n)·16sn/(2s) = 8,

so the acceptance probability is at least `e^{−8}` — **independent of `n`**. -/
theorem exp_neg_eight_le_speedyAcceptReal {n : ℕ} {c s : ℝ} (hn : 1 ≤ n) (hs : 0 < s)
    (hc1 : c ^ 2 ≤ 1) (hc2 : 1 - c ^ 2 ≤ 1 / (n : ℝ)) {v : EuclideanSpace ℝ (Fin n)}
    (hv : ‖v‖ ≤ 4 * Real.sqrt (s * (n : ℝ))) :
    Real.exp (-8) ≤ speedyAcceptReal c s v := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsn : (0 : ℝ) ≤ s * (n : ℝ) := by positivity
  -- `‖v‖² ≤ 16·s·n`
  have hsq : ‖v‖ ^ 2 ≤ 16 * (s * (n : ℝ)) := by
    have h := Real.sq_sqrt hsn
    nlinarith [norm_nonneg v, Real.sqrt_nonneg (s * (n : ℝ))]
  -- the exponent is at most `8`
  have hexp : (1 - c ^ 2) * ‖v‖ ^ 2 / (2 * s) ≤ 8 := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : (0 : ℝ) ≤ 1 - c ^ 2 := by linarith
    have h2 : (1 - c ^ 2) * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * (16 * (s * (n : ℝ))) := by
      have := mul_le_mul hc2 hsq (sq_nonneg _) (by positivity)
      linarith [this]
    have h3 : (1 / (n : ℝ)) * (16 * (s * (n : ℝ))) = 16 * s := by field_simp
    linarith [h2, h3]
  rw [speedyAcceptReal, Real.exp_le_exp, neg_div]
  linarith

/-! ## 3. Rescaling: pushing the shrunken target forward by `x ↦ x/c` -/

/-- **The target restricted to the shrunken body is the Gaussian on the shrunken body.**
Immediate from `c·K ⊆ K`, which needs only convexity and `0 ∈ K`. -/
theorem target_restrict_shrunken {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1) (s : ℝ) :
    ((volume.restrict K).withDensity (gaussianWeight s)).restrict (c • K)
      = (volume.restrict (c • K)).withDensity (gaussianWeight s) := by
  have hcKm : MeasurableSet (c • K) := measurableSet_smul_set hK hc0.ne'
  rw [restrict_withDensity hcKm, Measure.restrict_restrict hcKm,
    Set.inter_eq_left.2 (smul_subset_of_convex hKc h0K hc0.le hc1)]

/-- **The pushforward of the shrunken Gaussian under `x ↦ x/c`.**

Rescaling the shrunken body `c·K` back to `K` turns the Gaussian of variance `s` into the
Gaussian of variance `s/c²` — that is, into the density `z(v) = f(c·v)` of Cousins–Vempala's
proof — times the constant Jacobian `cⁿ`:

    map (x ↦ x/c) [1_{c·K}·γ_s]  =  cⁿ · [1_K·γ_{s/c²}].

An **equality of measures**, with the Jacobian explicit; the constant is removed by
normalisation in `Arlib.MarkovChains.map_inv_smul_condOn_shrunken`. -/
theorem map_inv_smul_gaussian_restrict {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {c : ℝ} (hc : 0 < c) (s : ℝ) :
    Measure.map (fun x : EuclideanSpace ℝ (Fin n) => c⁻¹ • x)
        ((volume.restrict (c • K)).withDensity (gaussianWeight s))
      = ENNReal.ofReal (c ^ n)
          • (volume.restrict K).withDensity (gaussianWeight (s / c ^ 2)) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => c⁻¹ • x) :=
    (continuous_const_smul _).measurable
  ext S hS
  have hcS : MeasurableSet (c • S) := measurableSet_smul_set hS hc0
  rw [Measure.map_apply hmeas hS, Set.preimage_smul_inv₀ hc0, withDensity_apply _ hcS,
    Measure.restrict_restrict hcS, ← Set.smul_set_inter₀ hc0,
    lintegral_gaussianWeight_smul_set (hS.inter hK) hc, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ hS, Measure.restrict_restrict hS]

/-- **The rescaled shrunken target is the `z`-law of Cousins–Vempala's proof.**

Conditioning the target `∝ 1_K·γ_s` on the shrunken body `c·K` and then rescaling by
`x ↦ x/c` gives *exactly* the probability measure with density `∝ 1_K(v)·f(c·v)`, i.e. the
Gaussian of inflated variance `s/c²` restricted to `K`.  The Jacobian `cⁿ` has cancelled
(`Arlib.condOn_smul`). -/
theorem map_inv_smul_condOn_shrunken {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (s : ℝ) :
    Measure.map (fun x : EuclideanSpace ℝ (Fin n) => c⁻¹ • x)
        (Arlib.condOn ((volume.restrict K).withDensity (gaussianWeight s)) (c • K))
      = Arlib.condOn ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2)))
          Set.univ := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => c⁻¹ • x) :=
    (continuous_const_smul _).measurable
  rw [← Arlib.condOn_restrict_univ, target_restrict_shrunken hK hKc h0K hc0 hc1 s,
    Arlib.map_condOn_univ hmeas, map_inv_smul_gaussian_restrict hK hc0 s,
    Arlib.condOn_smul (ENNReal.ofReal_pos.2 (pow_pos hc0 n)).ne' ENNReal.ofReal_ne_top]

/-! ## 4. The rejection step, its acceptance mass, and the assembly -/

/-- The acceptance probability is measurable, so it is a legitimate density. -/
theorem measurable_speedyAcceptReal (c s : ℝ) :
    Measurable fun v : EuclideanSpace ℝ (Fin n) => speedyAcceptReal c s v :=
  (Real.continuous_exp.comp
    (((continuous_const.mul (continuous_norm.pow 2)).neg).div_const _)).measurable

/-- **Rejection sampling is exact.**  Weighting the proposal law `∝ 1_K·γ_{s/c²}` — that is,
`z(v) = f(c·v)` — by the acceptance probability `f(v)/f(cv)` returns *exactly* the
unnormalised target `1_K·γ_s`.  An equality of measures, with no error term. -/
theorem withDensity_gaussian_mul_speedyAccept {K : Set (EuclideanSpace ℝ (Fin n))} {c s : ℝ}
    (hc : c ≠ 0) (hs : s ≠ 0) :
    ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))).withDensity
        (fun v => ENNReal.ofReal (speedyAcceptReal c s v))
      = (volume.restrict K).withDensity (gaussianWeight s) := by
  rw [← withDensity_mul _ (measurable_gaussianWeight _)
    (measurable_speedyAcceptReal c s).ennreal_ofReal]
  congr 1
  funext v
  rw [Pi.mul_apply, gaussianWeight, gaussianWeight,
    ← ENNReal.ofReal_mul (gaussianWeightReal_pos _ v).le,
    gaussianWeightReal_div_mul_speedyAcceptReal hc hs]

/-- Total mass of the unnormalised Gaussian on `K`. -/
theorem gaussianRestrict_univ (K : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    ((volume.restrict K).withDensity (gaussianWeight t)) Set.univ
      = ∫⁻ x in K, gaussianWeight t x := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- **The Gaussian mass of a set containing a ball is positive.** -/
theorem lintegral_gaussianWeight_pos {s : ℝ} (hs : 0 < s) {r : ℝ} (hr : 0 < r)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hsub : ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ A) :
    0 < ∫⁻ x in A, gaussianWeight s x := by
  have hlb : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
      ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * s))) ≤ gaussianWeight s x := by
    intro x hx
    rw [mem_ball, dist_zero_right] at hx
    exact ENNReal.ofReal_le_ofReal (exp_le_gaussianWeightReal hs hx.le)
  have hstep : (0 : ℝ≥0∞) < ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) r, gaussianWeight s x := by
    refine lt_of_lt_of_le ?_
      (lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2
        (Filter.Eventually.of_forall hlb)))
    rw [setLIntegral_const]
    exact ENNReal.mul_pos (by simp [Real.exp_pos]) (measure_ball_pos volume _ hr).ne'
  exact lt_of_lt_of_le hstep (lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl)

/-- **The Gaussian mass of a set of finite volume is finite.** -/
theorem lintegral_gaussianWeight_ne_top {s : ℝ} (hs : 0 < s)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : volume A ≠ ⊤) :
    (∫⁻ x in A, gaussianWeight s x) ≠ ⊤ := by
  refine ne_top_of_le_ne_top hA ?_
  calc ∫⁻ x in A, gaussianWeight s x ≤ ∫⁻ _ in A, (1 : ℝ≥0∞) :=
        lintegral_mono fun x => gaussianWeight_le_one hs x
    _ = volume A := setLIntegral_one _

/-- **The acceptance mass of the proposal law is at least `cⁿ`.**

The expected acceptance probability under the proposal `∝ 1_K·γ_{s/c²}` is the ratio of
unnormalised masses `(∫_K γ_s)/(∫_K γ_{s/c²})`, and the dilation identity
`Arlib.MarkovChains.lintegral_gaussianWeight_smul_set` turns the denominator into
`c^{-n}·∫_{c·K} γ_s ≤ c^{-n}·∫_K γ_s`.  So the rejection loop accepts with probability at
least `cⁿ`, which at `c = 1 − 1/(2n)` is at least `1/2`
(`Arlib.MarkovChains.half_le_one_sub_inv_two_mul_pow`) — the expected number of rounds is at
most `2`, independent of `n`.  Note this is a *sharper* route than the pointwise bound
`e^{−8}` of `Arlib.MarkovChains.exp_neg_eight_le_speedyAcceptReal`. -/
theorem pow_le_acceptance_ratio {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) {c s : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1) (hs : 0 < s) (hKvol : volume K ≠ ⊤)
    (hKpos : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) :
    ENNReal.ofReal (c ^ n)
      ≤ (∫⁻ x in K, gaussianWeight (s / c ^ 2) x)⁻¹ * ∫⁻ x in K, gaussianWeight s x := by
  have hs' : 0 < s / c ^ 2 := by positivity
  set M := ∫⁻ x in K, gaussianWeight (s / c ^ 2) x with hM
  have hM0 : M ≠ 0 := (lintegral_gaussianWeight_pos hs' one_pos hKpos).ne'
  have hMtop : M ≠ ⊤ := lintegral_gaussianWeight_ne_top hs' hKvol
  have hkey : ENNReal.ofReal (c ^ n) * M ≤ ∫⁻ x in K, gaussianWeight s x := by
    rw [hM, ← lintegral_gaussianWeight_smul_set hK hc0 s]
    exact lintegral_mono' (Measure.restrict_mono
      (smul_subset_of_convex hKc h0K hc0.le hc1) le_rfl) le_rfl
  calc ENNReal.ofReal (c ^ n) = ENNReal.ofReal (c ^ n) * (M * M⁻¹) := by
        rw [ENNReal.mul_inv_cancel hM0 hMtop, mul_one]
    _ = ENNReal.ofReal (c ^ n) * M * M⁻¹ := (mul_assoc _ _ _).symm
    _ ≤ (∫⁻ x in K, gaussianWeight s x) * M⁻¹ := by gcongr
    _ = M⁻¹ * ∫⁻ x in K, gaussianWeight s x := mul_comm _ _

/-- `ball 0 c ⊆ c·K` whenever `ball 0 1 ⊆ K`. -/
theorem ball_subset_smul_set {K : Set (EuclideanSpace ℝ (Fin n))}
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {c : ℝ} (hc : 0 < c) :
    ball (0 : EuclideanSpace ℝ (Fin n)) c ⊆ c • K := by
  intro z hz
  rw [mem_ball, dist_zero_right] at hz
  refine ⟨c⁻¹ • z, hball ?_, ?_⟩
  · rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
    have hlt : c⁻¹ * ‖z‖ < c⁻¹ * c := mul_lt_mul_of_pos_left hz (inv_pos.2 hc)
    rwa [inv_mul_cancel₀ hc.ne'] at hlt
  · show c • c⁻¹ • z = z
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- The total `ℓ·γ`-mass is finite. -/
theorem ellGaussianMeasure_univ_ne_top {s : ℝ} (hs : 0 < s)
    (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) (hKvol : volume K ≠ ⊤) :
    ellGaussianMeasure K δ s Set.univ ≠ ⊤ :=
  ne_top_of_le_ne_top hKvol (ellGaussianMeasure_univ_le hs K δ)

/-- The total `ℓ·γ`-mass is nonzero: on `c·K` the local conductance is `1` and the Gaussian
weight is positive, and `c·K` contains `ball 0 c`. -/
theorem ellGaussianMeasure_univ_ne_zero_of_ball {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {c δ s : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) (hδ : 0 < δ) (hδc : δ ≤ 1 - c) (hs : 0 < s) :
    ellGaussianMeasure K δ s Set.univ ≠ 0 := by
  rw [ellGaussianMeasure_univ]
  have h1 : ∫⁻ x in c • K, ell K δ x * gaussianWeight s x
      = ∫⁻ x in c • K, gaussianWeight s x :=
    setLIntegral_congr_fun (measurableSet_smul_set hK hc0.ne') fun x hx => by
      rw [ell_eq_one_on_shrunken hKc hball hc0 hc1 hδ hδc hx, one_mul]
  have h2 : 0 < ∫⁻ x in c • K, ell K δ x * gaussianWeight s x := by
    rw [h1]
    exact lintegral_gaussianWeight_pos hs hc0 (ball_subset_smul_set hball hc0)
  have h3 : ∫⁻ x in c • K, ell K δ x * gaussianWeight s x
      ≤ ∫⁻ x in K, ell K δ x * gaussianWeight s x :=
    lintegral_mono' (Measure.restrict_mono
      (smul_subset_of_convex hKc (hball (mem_ball_self one_pos)) hc0.le hc1.le) le_rfl) le_rfl
  exact (lt_of_lt_of_le h2 h3).ne'

/-- The `ℓ·γ`-mass of the shrunken body, as a set integral. -/
theorem ellGaussianMeasure_smul_set {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (δ s : ℝ) :
    ellGaussianMeasure K δ s (c • K) = ∫⁻ x in c • K, ell K δ x * gaussianWeight s x := by
  have hcKm : MeasurableSet (c • K) := measurableSet_smul_set hK hc0.ne'
  rw [ellGaussianMeasure, withDensity_apply _ hcKm, Measure.restrict_restrict hcKm,
    Set.inter_eq_left.2 (smul_subset_of_convex hKc h0K hc0.le hc1)]

/-- **`Q̂(c·K) ≥ 1/2` for the speedy walk's stationary *probability* measure.**

`Arlib.MarkovChains.half_le_speedy_shrunken` states this for the unnormalised `ℓ·γ`-measure;
this is the same fact after normalisation, which is the form the rejection analysis uses. -/
theorem half_le_speedyProb_shrunken {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKvol : volume K ≠ ⊤) {δ s : ℝ}
    (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) (hs : 0 < s) :
    ENNReal.ofReal (1 / 2)
      ≤ Arlib.condOn (ellGaussianMeasure K δ s) Set.univ ((1 - 1 / (2 * (n : ℝ))) • K) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
  have hhalf : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hc0 : (0 : ℝ) < 1 - 1 / (2 * (n : ℝ)) := by linarith
  have hc1 : 1 - 1 / (2 * (n : ℝ)) < 1 := by linarith
  have hδc : δ ≤ 1 - (1 - 1 / (2 * (n : ℝ))) := by linarith
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (mem_ball_self one_pos)
  have hM0 : ellGaussianMeasure K δ s Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hK hKc hball hc0 hc1 hδ hδc hs
  have hMtop : ellGaussianMeasure K δ s Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hs K δ hKvol
  have hkey : ENNReal.ofReal (1 / 2) * ellGaussianMeasure K δ s Set.univ
      ≤ ellGaussianMeasure K δ s ((1 - 1 / (2 * (n : ℝ))) • K) := by
    rw [ellGaussianMeasure_univ, ellGaussianMeasure_smul_set hK hKc h0K hc0 hc1.le δ s]
    exact half_le_speedy_shrunken hn hK hKc hball hδ hδn hs
  rw [Arlib.condOn_def, Measure.smul_apply, Measure.restrict_univ, smul_eq_mul]
  calc ENNReal.ofReal (1 / 2)
      = ENNReal.ofReal (1 / 2) *
          (ellGaussianMeasure K δ s Set.univ * (ellGaussianMeasure K δ s Set.univ)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hM0 hMtop, mul_one]
    _ = ENNReal.ofReal (1 / 2) * ellGaussianMeasure K δ s Set.univ *
          (ellGaussianMeasure K δ s Set.univ)⁻¹ := (mul_assoc _ _ _).symm
    _ ≤ ellGaussianMeasure K δ s ((1 - 1 / (2 * (n : ℝ))) • K) *
          (ellGaussianMeasure K δ s Set.univ)⁻¹ := by gcongr
    _ = (ellGaussianMeasure K δ s Set.univ)⁻¹ *
          ellGaussianMeasure K δ s ((1 - 1 / (2 * (n : ℝ))) • K) := mul_comm _ _

/-! ### The assembly -/

/-- **`lem:map-speedy-to-ball`, abstract shrink factor.**

Let `K` be a convex body with `B₁ ⊆ K` and `vol(K) < ∞`, let the step satisfy `δ ≤ 1 − c`,
and let `cⁿ ≥ 1/2`.  Let `P` be the law actually produced by the speedy sampler, within total
variation `ε ≤ 1/32` of the speedy stationary law `Q̂ ∝ 1_K·ℓ·γ_s`.  Run

1. condition on `c·K`  (reject until the draw lands there),
2. rescale `u ↦ u/c`,
3. accept `v` with probability `f(v)/f(cv) = speedyAcceptReal c s v`, else restart.

Then the output law is within total variation **`64·ε`** of the target `∝ 1_K·γ_s`.

The constant is `64 = 2·(2·8)/(1/4)`: `8` for the conditioning step
(`Arlib.tvLe_condOn_half`), nothing for the rescaling (`Arlib.TVLe.map`), nothing for the
acceptance filter itself (`Arlib.TVLe.withDensity`), and a further `8` for renormalising after
the filter, whose acceptance mass is at least `cⁿ ≥ 1/2`
(`Arlib.MarkovChains.pow_le_acceptance_ratio`). -/
theorem tvLe_speedyRejection_target_of {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKvol : volume K ≠ ⊤)
    {c δ s : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hδ : 0 < δ) (hδc : δ ≤ 1 - c) (hs : 0 < s)
    (hcn : (1 : ℝ) / 2 ≤ c ^ n) {P : Measure (EuclideanSpace ℝ (Fin n))}
    [IsProbabilityMeasure P] {ε : ℝ≥0∞}
    (hQhalf : ENNReal.ofReal (1 / 2)
      ≤ Arlib.condOn (ellGaussianMeasure K δ s) Set.univ (c • K))
    (hP : Arlib.TVLe P (Arlib.condOn (ellGaussianMeasure K δ s) Set.univ) ε)
    (hε : ε ≤ ENNReal.ofReal (1 / 32)) :
    Arlib.TVLe
      (Arlib.condOn
        ((Measure.map (fun x : EuclideanSpace ℝ (Fin n) => c⁻¹ • x)
            (Arlib.condOn P (c • K))).withDensity
          fun v => ENNReal.ofReal (speedyAcceptReal c s v))
        Set.univ)
      (Arlib.condOn ((volume.restrict K).withDensity (gaussianWeight s)) Set.univ)
      (64 * ε) := by
  have hofReal4 : ENNReal.ofReal (1 / 4) = (4 : ℝ≥0∞)⁻¹ := by
    rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      show ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) by simp]
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (mem_ball_self one_pos)
  have hcKm : MeasurableSet (c • K) := measurableSet_smul_set hK hc0.ne'
  have hTmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => c⁻¹ • x) :=
    (continuous_const_smul _).measurable
  have hs' : (0 : ℝ) < s / c ^ 2 := by positivity
  have hεtop : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hε
  have hεq : ε ≤ ENNReal.ofReal (1 / 4) := le_trans hε (ENNReal.ofReal_le_ofReal (by norm_num))
  have hMtop : ellGaussianMeasure K δ s Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hs K δ hKvol
  have hM0 : ellGaussianMeasure K δ s Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hK hKc hball hc0 hc1 hδ hδc hs
  haveI : IsProbabilityMeasure (Arlib.condOn (ellGaussianMeasure K δ s) Set.univ) :=
    Arlib.isProbabilityMeasure_condOn _ hM0 hMtop
  -- Step 1: conditioning on the shrunken body costs a factor 8.
  have hstep1 := Arlib.tvLe_condOn_half hP hcKm hQhalf
  have hcond : Arlib.condOn (Arlib.condOn (ellGaussianMeasure K δ s) Set.univ) (c • K)
      = Arlib.condOn ((volume.restrict K).withDensity (gaussianWeight s)) (c • K) := by
    rw [Arlib.condOn_condOn_univ _ _ hM0 hMtop]
    exact condOn_ellGaussianMeasure_shrunken hK hKc hball hc0 hc1 hδ hδc
  rw [hcond] at hstep1
  -- Step 2: rescaling is free.
  have hstep2 := hstep1.map hTmeas
  rw [map_inv_smul_condOn_shrunken hK hKc h0K hc0 hc1.le s] at hstep2
  -- Probability-measure instances.
  have hPq : ENNReal.ofReal (1 / 4) ≤ P (c • K) := Arlib.quarter_le_of_tvLe hP hcKm hQhalf hεq
  have hPcK0 : P (c • K) ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num : (0 : ℝ) < 1 / 4)) hPq).ne'
  haveI : IsProbabilityMeasure (Arlib.condOn P (c • K)) :=
    Arlib.isProbabilityMeasure_condOn _ hPcK0 (measure_ne_top P _)
  haveI : IsProbabilityMeasure (Measure.map (fun x : EuclideanSpace ℝ (Fin n) => c⁻¹ • x)
      (Arlib.condOn P (c • K))) := Measure.isProbabilityMeasure_map hTmeas.aemeasurable
  have hZu0 : ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) Set.univ ≠ 0 := by
    rw [gaussianRestrict_univ]
    exact (lintegral_gaussianWeight_pos hs' one_pos hball).ne'
  have hZutop : ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) Set.univ ≠ ⊤ := by
    rw [gaussianRestrict_univ]
    exact lintegral_gaussianWeight_ne_top hs' hKvol
  haveI : IsProbabilityMeasure (Arlib.condOn
      ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) Set.univ) :=
    Arlib.isProbabilityMeasure_condOn _ hZu0 hZutop
  -- Step 3: the acceptance filter is free.
  have hacc0 : ∀ v : EuclideanSpace ℝ (Fin n), 0 ≤ speedyAcceptReal c s v :=
    fun v => (speedyAcceptReal_pos c s v).le
  have hacc1 : ∀ v : EuclideanSpace ℝ (Fin n), speedyAcceptReal c s v ≤ 1 :=
    fun v => speedyAcceptReal_le_one hs (by nlinarith) v
  have h8top : 8 * ε ≠ ⊤ := ENNReal.mul_ne_top (by simp) hεtop
  have hstep3 := hstep2.withDensity h8top (measurable_speedyAcceptReal c s) hacc0 hacc1
  have hZw : (Arlib.condOn ((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2)))
        Set.univ).withDensity (fun v => ENNReal.ofReal (speedyAcceptReal c s v))
      = (((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) Set.univ)⁻¹
        • ((volume.restrict K).withDensity (gaussianWeight s)) := by
    rw [Arlib.condOn_def, Measure.restrict_univ, Arlib.withDensity_smul_measure,
      withDensity_gaussian_mul_speedyAccept hc0.ne' hs.ne']
  rw [hZw] at hstep3
  -- Step 4: renormalising after the filter costs another factor 8.
  have hmassZ : ENNReal.ofReal (1 / 2)
      ≤ ((((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2))) Set.univ)⁻¹
          • ((volume.restrict K).withDensity (gaussianWeight s))) Set.univ := by
    rw [Measure.smul_apply, smul_eq_mul, gaussianRestrict_univ, gaussianRestrict_univ]
    exact le_trans (ENNReal.ofReal_le_ofReal hcn)
      (pow_le_acceptance_ratio hK hKc h0K hc0 hc1.le hs hKvol hball)
  have h8q : 8 * ε ≤ ENNReal.ofReal (1 / 4) := by
    have h1 : (8 : ℝ≥0∞) * ε ≤ 8 * ENNReal.ofReal (1 / 32) := by gcongr
    have h2 : (8 : ℝ≥0∞) * ENNReal.ofReal (1 / 32) = ENNReal.ofReal (1 / 4) := by
      rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    exact h2 ▸ h1
  have hmassP := Arlib.quarter_le_of_tvLe hstep3 MeasurableSet.univ hmassZ h8q
  haveI : IsFiniteMeasure ((Measure.map (fun x : EuclideanSpace ℝ (Fin n) => c⁻¹ • x)
      (Arlib.condOn P (c • K))).withDensity
        fun v => ENNReal.ofReal (speedyAcceptReal c s v)) :=
    Arlib.isFiniteMeasure_withDensity_le_one fun x => by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hacc1 x)
  haveI : IsFiniteMeasure ((((volume.restrict K).withDensity (gaussianWeight (s / c ^ 2)))
      Set.univ)⁻¹ • ((volume.restrict K).withDensity (gaussianWeight s))) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul]
    refine ENNReal.mul_lt_top (ENNReal.inv_ne_top.2 hZu0).lt_top ?_
    rw [gaussianRestrict_univ]
    exact (lintegral_gaussianWeight_ne_top hs hKvol).lt_top
  have hfinal := Arlib.TVLe.condOn hstep3 MeasurableSet.univ
    (m := ENNReal.ofReal (1 / 4)) (ENNReal.ofReal_pos.2 (by norm_num)) hmassP
    (le_trans (ENNReal.ofReal_le_ofReal (by norm_num)) hmassZ)
  rw [Arlib.condOn_smul (ENNReal.inv_ne_zero.2 hZutop) (ENNReal.inv_ne_top.2 hZu0),
    show 2 * (8 * ε) / ENNReal.ofReal (1 / 4) = 64 * ε by
      rw [hofReal4, ENNReal.div_eq_inv_mul, inv_inv]; ring] at hfinal
  exact hfinal

/-- **`lem:map-speedy-to-ball` at Cousins–Vempala's shrink factor `c = 1 − 1/(2n)`.**

The instance of `Arlib.MarkovChains.tvLe_speedyRejection_target_of` at `c = 1 − 1/(2n)` and
step size `δ ≤ 1/(2n)`.  Both remaining hypotheses are discharged:
`cⁿ ≥ 1/2` by `Arlib.MarkovChains.half_le_one_sub_inv_two_mul_pow`, and `Q̂(c·K) ≥ 1/2` by
`Arlib.MarkovChains.half_le_speedyProb_shrunken`.

**Constant: `64·ε`, valid for `ε ≤ 1/32`** — not Cousins–Vempala's `10ε`; see the module
docstring. -/
theorem tvLe_speedyRejection_target {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKvol : volume K ≠ ⊤) {δ s : ℝ}
    (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) (hs : 0 < s)
    {P : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure P] {ε : ℝ≥0∞}
    (hP : Arlib.TVLe P (Arlib.condOn (ellGaussianMeasure K δ s) Set.univ) ε)
    (hε : ε ≤ ENNReal.ofReal (1 / 32)) :
    Arlib.TVLe
      (Arlib.condOn
        ((Measure.map (fun x : EuclideanSpace ℝ (Fin n) => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
            (Arlib.condOn P ((1 - 1 / (2 * (n : ℝ))) • K))).withDensity
          fun v => ENNReal.ofReal (speedyAcceptReal (1 - 1 / (2 * (n : ℝ))) s v))
        Set.univ)
      (Arlib.condOn ((volume.restrict K).withDensity (gaussianWeight s)) Set.univ)
      (64 * ε) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
  have hhalf : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  exact tvLe_speedyRejection_target_of hK hKc hball hKvol (by linarith) (by linarith) hδ
    (by linarith) hs (half_le_one_sub_inv_two_mul_pow hn)
    (half_le_speedyProb_shrunken hn hK hKc hball hKvol hδ hδn hs) hP hε

/-- **The first rejection loop terminates in `O(1)` rounds.**  The sampler's own law puts at
least `1/4` of its mass on the shrunken body, so step 1 ("draw until the sample lands in
`c·K`") needs at most `4` draws in expectation. -/
theorem quarter_le_shrunken_mass {n : ℕ} (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKvol : volume K ≠ ⊤) {δ s : ℝ}
    (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) (hs : 0 < s)
    {P : Measure (EuclideanSpace ℝ (Fin n))} {ε : ℝ≥0∞}
    (hP : Arlib.TVLe P (Arlib.condOn (ellGaussianMeasure K δ s) Set.univ) ε)
    (hε : ε ≤ ENNReal.ofReal (1 / 4)) :
    ENNReal.ofReal (1 / 4) ≤ P ((1 - 1 / (2 * (n : ℝ))) • K) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
  have hhalf : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  exact Arlib.quarter_le_of_tvLe hP (measurableSet_smul_set hK (by linarith : (0:ℝ) < 1 - 1 / (2 * (n : ℝ))).ne')
    (half_le_speedyProb_shrunken hn hK hKc hball hKvol hδ hδn hs) hε

/-! ### Non-vacuity witnesses

Every theorem above with a nontrivial binder bundle is exhibited as satisfiable here, so that
none of them is vacuously true. -/

/-- **Non-vacuity witness for the capstone.**  Every hypothesis of
`Arlib.MarkovChains.tvLe_speedyRejection_target` holds simultaneously at `n = 1`,
`K = B₁ ⊆ ℝ¹`, `δ = 1/2`, `s = 1`, `P = Q̂` (the exact sampler) and `ε = 0`. -/
theorem exists_speedyRejection_witness :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 1))) (δ s : ℝ) (P : Measure (EuclideanSpace ℝ (Fin 1)))
      (ε : ℝ≥0∞),
      IsProbabilityMeasure P ∧ MeasurableSet K ∧ Convex ℝ K ∧
        ball (0 : EuclideanSpace ℝ (Fin 1)) 1 ⊆ K ∧ volume K ≠ ⊤ ∧ 0 < δ ∧
        δ ≤ 1 / (2 * ((1 : ℕ) : ℝ)) ∧ 0 < s ∧
        Arlib.TVLe P (Arlib.condOn (ellGaussianMeasure K δ s) Set.univ) ε ∧
        ε ≤ ENNReal.ofReal (1 / 32) := by
  refine ⟨ball (0 : EuclideanSpace ℝ (Fin 1)) 1, 1 / 2, 1,
    Arlib.condOn (ellGaussianMeasure (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) (1 / 2) 1)
      Set.univ, 0, ?_, measurableSet_ball, convex_ball _ _, subset_rfl,
    measure_ball_lt_top.ne, by norm_num, by norm_num, by norm_num,
    Arlib.TVLe.refl _, (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 32))⟩
  refine Arlib.isProbabilityMeasure_condOn _ ?_ ?_
  · exact ellGaussianMeasure_univ_ne_zero_of_ball measurableSet_ball (convex_ball _ _) subset_rfl
      (c := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact ellGaussianMeasure_univ_ne_top (by norm_num) _ _ measure_ball_lt_top.ne

/-- **Non-vacuity witness for the `e^{−8}` acceptance bound**: `n = 1`, `s = 1`, `c = 1/2`,
`v = 0` satisfies every hypothesis of
`Arlib.MarkovChains.exp_neg_eight_le_speedyAcceptReal`. -/
theorem exp_neg_eight_le_speedyAcceptReal_witness :
    (1 : ℕ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ ((1 : ℝ) / 2) ^ 2 ≤ 1 ∧
      1 - ((1 : ℝ) / 2) ^ 2 ≤ 1 / ((1 : ℕ) : ℝ) ∧
      ‖(0 : EuclideanSpace ℝ (Fin 1))‖ ≤ 4 * Real.sqrt (1 * ((1 : ℕ) : ℝ)) := by
  refine ⟨le_rfl, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [norm_zero]
  positivity

/-- **Non-vacuity witness for `Arlib.TVLe.condOn` / `Arlib.tvLe_condOn_half`.**  Both bundles
are satisfied by the exact sampler `μ = ν` (any probability measure), `A = univ`, `ε = 0`,
`m = 1`. -/
theorem tvLe_condOn_witness {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    Arlib.TVLe μ μ 0 ∧ MeasurableSet (Set.univ : Set Ω) ∧ (0 : ℝ≥0∞) < 1 ∧
      (1 : ℝ≥0∞) ≤ μ Set.univ ∧ ENNReal.ofReal (1 / 2) ≤ μ Set.univ :=
  ⟨Arlib.TVLe.refl _, MeasurableSet.univ, one_pos, by simp,
    by rw [measure_univ]; exact ENNReal.ofReal_le_one.2 (by norm_num)⟩

section AxiomCheck

#print axioms Arlib.inv_mul_self_le_one
#print axioms Arlib.condOn_le_one
#print axioms Arlib.tvLe_condOn_one
#print axioms Arlib.div_le_div_add_two_mul_div
#print axioms Arlib.condOn_le_condOn_add
#print axioms Arlib.TVLe.condOn
#print axioms Arlib.tvLe_condOn_half
#print axioms Arlib.condOn_smul
#print axioms Arlib.condOn_restrict_univ
#print axioms Arlib.map_condOn_univ
#print axioms Arlib.quarter_le_of_tvLe
#print axioms Arlib.condOn_condOn_univ
#print axioms Arlib.isFiniteMeasure_withDensity_le_one
#print axioms Arlib.withDensity_smul_measure
#print axioms Arlib.withDensity_ofReal_apply
#print axioms Arlib.TVLe.withDensity
#print axioms Arlib.MarkovChains.speedyAcceptReal_pos
#print axioms Arlib.MarkovChains.gaussianWeightReal_div_mul_speedyAcceptReal
#print axioms Arlib.MarkovChains.speedyAcceptReal_le_one
#print axioms Arlib.MarkovChains.one_sub_sq_shrink_le_inv
#print axioms Arlib.MarkovChains.sq_shrink_le_one
#print axioms Arlib.MarkovChains.exp_neg_eight_le_speedyAcceptReal
#print axioms Arlib.MarkovChains.target_restrict_shrunken
#print axioms Arlib.MarkovChains.map_inv_smul_gaussian_restrict
#print axioms Arlib.MarkovChains.map_inv_smul_condOn_shrunken
#print axioms Arlib.MarkovChains.measurable_speedyAcceptReal
#print axioms Arlib.MarkovChains.withDensity_gaussian_mul_speedyAccept
#print axioms Arlib.MarkovChains.gaussianRestrict_univ
#print axioms Arlib.MarkovChains.lintegral_gaussianWeight_pos
#print axioms Arlib.MarkovChains.lintegral_gaussianWeight_ne_top
#print axioms Arlib.MarkovChains.pow_le_acceptance_ratio
#print axioms Arlib.MarkovChains.ball_subset_smul_set
#print axioms Arlib.MarkovChains.ellGaussianMeasure_univ_ne_top
#print axioms Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero_of_ball
#print axioms Arlib.MarkovChains.ellGaussianMeasure_smul_set
#print axioms Arlib.MarkovChains.half_le_speedyProb_shrunken
#print axioms Arlib.MarkovChains.tvLe_speedyRejection_target_of
#print axioms Arlib.MarkovChains.tvLe_speedyRejection_target
#print axioms Arlib.MarkovChains.quarter_le_shrunken_mass
#print axioms Arlib.MarkovChains.exists_speedyRejection_witness
#print axioms Arlib.MarkovChains.exp_neg_eight_le_speedyAcceptReal_witness
#print axioms Arlib.MarkovChains.tvLe_condOn_witness

end AxiomCheck

end Arlib.MarkovChains
