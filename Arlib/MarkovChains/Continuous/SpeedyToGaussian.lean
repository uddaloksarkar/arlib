/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.SpeedyGaussian
import Arlib.MarkovChains.Continuous.SpeedyToUniform

/-!
# From the speedy walk's stationary measure to the Gaussian-restricted measure on `K`

The Gaussian analogue of `Arlib/MarkovChains/Continuous/SpeedyToUniform.lean`, i.e.
Cousins-Vempala `lem:map-speedy-to-ball` (`1409.6011/vol3_journal.tex:942`) for the Gaussian
target.

`Arlib.MarkovChains.speedyMetropolisGaussian K δ σ²` is reversible for
`Arlib.MarkovChains.ellGaussianProb K δ σ²`, the law with density `∝ 1_K·ℓ·γ`
(`isReversible_speedyMetropolisGaussian_prob`), but the sampler is supposed to produce the
Cousins-Vempala phase law `∝ 1_K·γ`, which in this repository is spelled
`Arlib.uniformOn (volume.withDensity (Arlib.MarkovChains.gaussianWeight σ²)) K` — the target of
`Arlib.MarkovChains.mixesWithin_metropolisGaussian` and friends.  This file closes that gap.

## The arithmetic, in one line

It is *the same* arithmetic as the uniform case, with the Gaussian measure
`ν := volume.withDensity (gaussianWeight σ²)` in place of Lebesgue measure.  Write `V = ν(K)`,
`L = ∫_K ℓ·γ`, and for measurable `S`, `a = ∫_{S∩K} ℓ·γ` and `b = ν(S ∩ K)`.  Then
`ellGaussianProb K δ σ² S = a/L` and `uniformOn ν K S = b/V`, and

    a/L ≤ b/L ≤ b/((1-s)V) = (b/V)·(1-s)⁻¹ ≤ b/V + s/(1-s),

using only `ℓ ≤ 1` on `S ∩ K` (`Arlib.MarkovChains.ell_le_one`, through
`ellGaussianMeasure_le_withDensity_inter` below) and the Gaussian smoothness hypothesis
`(1-s)·ν(K) ≤ ∫_K ℓ·γ`.  The five-line `ℝ≥0∞` comparison is **not restated**: it is
`Arlib.MarkovChains.inv_mul_le_div_add_div` (`SpeedyToUniform.lean:144`), imported and reused
verbatim.  Nothing in it mentions Lebesgue measure, so the Gaussian instance is free.

## `IsSmooth` is NOT reusable here, and no replacement predicate is introduced

`Arlib.MarkovChains.IsSmooth K δ s` (`BallWalk.lean:476`) is

    (1 - s) * volume K ≤ ∫⁻ x in K, ell K δ x,

with **Lebesgue measure and the bare `ℓ` hard-coded**: it takes no measure argument and no
density argument, so there is no way to instantiate it at `ν` and `ℓ·γ`.  Rather than
generalise a definition another eight files depend on (this file is under a
"create exactly one new file, edit nothing else" mandate), the Gaussian-weighted smoothness

    (1 - s) * ν K ≤ ∫⁻ x in K, ell K δ x * gaussianWeight σ² x

is carried as an **explicit inline hypothesis** of every theorem that needs it.  No `def`,
`structure`, `class` or named `Prop` is introduced anywhere in this file — every declaration
below is a `theorem` (`CLAUDE.md` §11: no semantic `def`s to audit).

## What is proved here, and what is assumed

* **Proved**: the bridge, `tvLe_ellGaussianProb_uniformOn`, from the smoothness hypothesis.
* **Assumed (hypothesis, never asserted)**: the smoothness hypothesis itself.  Its sharp form is
  Cousins-Vempala `lem:lambda-bound`, which is *not* proved here.  What *is* proved is a crude
  witness on the unit ball (`gaussianSmooth_unitBall`), enough to show the bridge is not vacuous
  and no more.  See §3.

## Main results

* `Arlib.MarkovChains.ellGaussianMeasure_le_withDensity_inter` — `ℓ ≤ 1`, in measure form:
  `ellGaussianMeasure K δ σ² S ≤ ν (S ∩ K)`.  The Gaussian analogue of
  `Arlib.MarkovChains.ellMeasure_le_volume_inter`.
* `Arlib.MarkovChains.tvLe_ellGaussianProb_uniformOn` — **the bridge**:
  `TVLe (ellGaussianProb K δ σ²) (uniformOn ν K) (s/(1-s))` under Gaussian smoothness.
* `Arlib.MarkovChains.gaussianSmooth_unitBall`, `Arlib.MarkovChains.exists_ell_unitBall_lt_one`,
  `Arlib.MarkovChains.exists_speedyToGaussian_witness` — the non-vacuity witness: a body where
  the hypothesis holds with a **finite** bound and on which `ℓ` is provably **non-constant**.
* `Arlib.MarkovChains.exists_speedyToGaussian_witness_lt_one` — the witness sharpened at
  `n = 1, δ = 1/4, σ² = 1` to a bound **strictly below `1`**, which a finite bound alone does
  not give (`TVLe μ ν 1` is free for probability measures).

## Honest accounting

`s` is not free, and the witness of §3 is quantitatively terrible: it certifies only

    1 - s  =  e^{-(1-δ)²/(2σ²)} · (1-δ)ⁿ,

obtained by throwing away all Gaussian concentration (`γ ≤ 1` upstairs, `γ ≥ e^{-r²/(2σ²)}`
downstairs).  For `σ² = Θ(1/n)` — the Cousins-Vempala cooling regime — that is exponentially
small in `n`, so `s/(1-s)` is exponentially *large*: **finite, hence non-vacuous, and useless**.
An informative constant is exactly `lem:lambda-bound` and is deliberately out of scope here.

As in the uniform case, the bias `s/(1-s)` is a property of the fixed law `ellGaussianProb`,
not of the chain: running longer does not shrink it, only shrinking `δ` does, and `δ` appears
in the conductance bound (`Arlib.MarkovChains.conductance_speedyGaussian_unconditional`) as a
multiplicative factor, hence in the step count as `δ⁻²`.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. `ℓ ≤ 1`, in measure form

The only property of `ℓ` the bridge uses.  Note that neither `0 < δ` nor `0 < σ²` is needed:
the bound is pointwise `ℓ(x)·γ(x) ≤ γ(x)`. -/

/-- **The `ℓ·γ`-weight of a set never exceeds its Gaussian weight**, since `ℓ ≤ 1`:

    ellGaussianMeasure K δ σ² S  ≤  (volume.withDensity (gaussianWeight σ²)) (S ∩ K).

The Gaussian analogue of `Arlib.MarkovChains.ellMeasure_le_volume_inter`
(`SpeedyWalk.lean:1381`), proved the same way.  Taking `S = Set.univ` also gives finiteness of
the normaliser, which is why no separate finiteness lemma appears below. -/
theorem ellGaussianMeasure_le_withDensity_inter (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (δ sq : ℝ) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) :
    ellGaussianMeasure K δ sq S
      ≤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq)) (S ∩ K) := by
  rw [ellGaussianMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS,
    withDensity_apply _ (hS.inter hK)]
  refine lintegral_mono fun x => ?_
  calc ell K δ x * gaussianWeight sq x ≤ 1 * gaussianWeight sq x :=
        mul_le_mul' (ell_le_one K δ x) le_rfl
    _ = gaussianWeight sq x := one_mul _

/-- **The Gaussian-restricted measure never exceeds Lebesgue measure**, for `σ² > 0`, since
`γ ≤ 1`.  Used only by the witness of §3. -/
theorem withDensity_gaussianWeight_le_volume {sq : ℝ} (hsq : 0 < sq)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq)) S
      ≤ volume S := by
  rw [withDensity_apply _ hS]
  calc ∫⁻ x in S, gaussianWeight sq x ≤ ∫⁻ _ in S, (1 : ℝ≥0∞) :=
        lintegral_mono fun x => gaussianWeight_le_one hsq x
    _ = volume S := by rw [setLIntegral_one]

/-! ## 2. The bridge -/

/-- **The stationary measure of the speedy Metropolis-Gaussian walk is within `s/(1-s)` of the
Gaussian-restricted measure on `K`**:

    TVLe (ellGaussianProb K δ σ²) (uniformOn (volume.withDensity (gaussianWeight σ²)) K)
      (s / (1 - s))

under the Gaussian smoothness hypothesis `hsmooth : (1-s)·ν(K) ≤ ∫_K ℓ·γ`.  This is
Cousins-Vempala `lem:map-speedy-to-ball` (`vol3_journal.tex:942`) for the Gaussian target, and
the exact analogue of `Arlib.MarkovChains.tvLe_ellProb_uniformOn`.

Hypotheses, in full: `K` measurable; `ν K ≠ 0`; `ν K ≠ ⊤`; `hsmooth`.  There is **no** `0 < δ`
and **no** `0 < σ²`: the walk's step size and temperature are irrelevant to a statement about
two fixed measures, and the probability-measure guard on `ellGaussianProb` is derived from
`hsmooth` itself (when `s < 1`) rather than from convexity/boundedness of `K` as in
`ellGaussianMeasure_univ_ne_zero`.

At `s ≥ 1` the conclusion is `TVLe _ _ ⊤`, which is free; the content is at `s < 1`. -/
theorem tvLe_ellGaussianProb_uniformOn {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ sq : ℝ}
    (hK0 : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq)) K ≠ 0)
    (hKtop : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq)) K ≠ ⊤)
    {s : ℝ≥0∞}
    (hsmooth : (1 - s) *
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq)) K
      ≤ ∫⁻ x in K, ell K δ x * gaussianWeight sq x) :
    TVLe (ellGaussianProb K δ sq)
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight sq)) K) (s / (1 - s)) := by
  rcases le_or_gt 1 s with hs1 | hs1
  · -- `1 - s = 0` and `s ≠ 0`, so the slack is `⊤` and there is nothing to prove.
    have hs0 : s ≠ 0 := (lt_of_lt_of_le zero_lt_one hs1).ne'
    rw [tsub_eq_zero_of_le hs1, ENNReal.div_zero hs0]
    exact Arlib.tvLe_top _ _
  · have hc0 : (1 : ℝ≥0∞) - s ≠ 0 := (tsub_pos_of_lt hs1).ne'
    -- The normaliser is positive: `hsmooth` bounds it below by `(1-s)·ν(K) > 0`.
    have hLpos : 0 < ∫⁻ x in K, ell K δ x * gaussianWeight sq x :=
      lt_of_lt_of_le (ENNReal.mul_pos hc0 hK0) hsmooth
    -- and finite, by `ℓ ≤ 1` at `S = univ`.
    have hLtop : (∫⁻ x in K, ell K δ x * gaussianWeight sq x) ≠ ⊤ := by
      have h := ellGaussianMeasure_le_withDensity_inter K hK δ sq
        (MeasurableSet.univ (α := EuclideanSpace ℝ (Fin n)))
      rw [Set.univ_inter, ellGaussianMeasure_univ] at h
      exact ne_top_of_le_ne_top hKtop h
    haveI : IsProbabilityMeasure (ellGaussianProb K δ sq) :=
      isProbabilityMeasure_ellGaussianProb
        (by rw [ellGaussianMeasure_univ]; exact hLpos.ne')
        (by rw [ellGaussianMeasure_univ]; exact hLtop)
    haveI : IsProbabilityMeasure (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq)) K) :=
      Arlib.isProbabilityMeasure_uniformOn _ hK0 hKtop
    refine Arlib.tvLe_of_forall_le fun S hS => ?_
    rw [ellGaussianProb, Measure.smul_apply, smul_eq_mul, Arlib.uniformOn_apply _ hK hS,
      ellGaussianMeasure_univ]
    exact inv_mul_le_div_add_div (ellGaussianMeasure_le_withDensity_inter K hK δ sq hS)
      (measure_mono Set.inter_subset_right) hsmooth

/-! ## 3. Non-vacuity: the bridge on the unit ball, with `ℓ` provably non-constant

`CLAUDE.md` §11.  Two things have to be checked by hand, because a green build sees neither:

1. the hypothesis `hsmooth` is satisfiable with `s < 1`, so that the conclusion is not the
   free statement `TVLe _ _ ⊤` (`Arlib.tvLe_top`);
2. it is satisfiable on a body where `ℓ` is **not** constant — otherwise `hsmooth` would hold
   for a reason having nothing to do with local conductance, and the bridge would be a
   statement about `ellGaussianProb = uniformOn ν K`.

The unit ball with `0 < δ ≤ 1` discharges both. -/

/-- **A crude Gaussian smoothness bound for the unit ball**:

    e^{-(1-δ)²/(2σ²)}·(1-δ)ⁿ · ν(B(0,1))  ≤  ∫_{B(0,1)} ℓ·γ,     ν = volume.withDensity γ,

i.e. the hypothesis of `tvLe_ellGaussianProb_uniformOn` at
`s = 1 - e^{-(1-δ)²/(2σ²)}·(1-δ)ⁿ`.

The proof throws away every ounce of Gaussian concentration: `γ ≤ 1` upstairs
(`withDensity_gaussianWeight_le_volume`), `γ ≥ e^{-r²/(2σ²)}` on `rBₙ` downstairs
(`mul_volume_ball_le_withDensity_gaussianWeight`), and `ℓ = 1` on `(1-δ)Bₙ`
(`ell_unitBall_eq_one_of_mem`); the volume ratio `(1-δ)ⁿ` is the homothety
`MeasureTheory.Measure.addHaar_ball`, exactly as in `Arlib.MarkovChains.isSmooth_unitBall`.

**This is not `lem:lambda-bound`.**  For `σ² = Θ(1/n)` the constant is exponentially small in
`n`, so the total-variation bound it feeds into `tvLe_ellGaussianProb_uniformOn` is
exponentially large: finite (hence non-vacuous), and quantitatively worthless.  The sharp
bound, which is what a Cousins-Vempala phase actually needs, is proved elsewhere. -/
theorem gaussianSmooth_unitBall [NeZero n] {δ sq : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsq : 0 < sq) :
    ENNReal.ofReal (Real.exp (-(1 - δ) ^ 2 / (2 * sq))) * ENNReal.ofReal ((1 - δ) ^ n) *
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq))
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x * gaussianWeight sq x := by
  have hr0 : (0 : ℝ) ≤ 1 - δ := by linarith
  have hvol : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ))
      = ENNReal.ofReal ((1 - δ) ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [Measure.addHaar_ball volume 0 hr0, finrank_euclideanSpace_fin]
  calc ENNReal.ofReal (Real.exp (-(1 - δ) ^ 2 / (2 * sq))) * ENNReal.ofReal ((1 - δ) ^ n) *
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq))
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      ≤ ENNReal.ofReal (Real.exp (-(1 - δ) ^ 2 / (2 * sq))) * ENNReal.ofReal ((1 - δ) ^ n) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
        mul_le_mul' le_rfl (withDensity_gaussianWeight_le_volume hsq measurableSet_ball)
    _ = ENNReal.ofReal (Real.exp (-(1 - δ) ^ 2 / (2 * sq))) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ)) := by
        rw [hvol, mul_assoc]
    _ ≤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq))
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ)) :=
        mul_volume_ball_le_withDensity_gaussianWeight hsq (1 - δ)
    _ = ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ), gaussianWeight sq x :=
        withDensity_apply _ measurableSet_ball
    _ ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ),
          ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x * gaussianWeight sq x :=
        setLIntegral_mono' measurableSet_ball fun x hx => by
          rw [ell_unitBall_eq_one_of_mem hδ hx, one_mul]
    _ ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x * gaussianWeight sq x :=
        lintegral_mono' (Measure.restrict_mono
          (Metric.ball_subset_ball (by linarith)) le_rfl) le_rfl

/-- **`ℓ` is not constant on the unit ball**: there is a point of the ball whose local
conductance is *strictly* below `1`.  Together with
`Arlib.MarkovChains.ell_unitBall_zero` (`ℓ(0) = 1`) this says the body of the witness is
genuinely one on which the speedy walk's stationary law differs from the plain
Gaussian-restricted law, so `tvLe_ellGaussianProb_uniformOn` is not being applied to two
equal measures.

The point is `x = (1 - δ/2)·e₀`, at distance `δ/2` from the boundary: the open set
`B(x,δ) \ closedBall(0,1)` is non-empty (it contains `(1 + δ/4)·e₀`), hence of positive
Lebesgue measure, so `vol(B(x,δ) ∩ K) < vol(B(x,δ))`. -/
theorem exists_ell_unitBall_lt_one [NeZero n] {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x < 1 := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set i : Fin n := ⟨0, hn0⟩ with hi
  set x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 - δ / 2) with hxdef
  set y : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 + δ / 4) with hydef
  have hxnorm : ‖x‖ = 1 - δ / 2 := by
    rw [hxdef]
    simp [abs_of_pos, show (0:ℝ) < 1 - δ / 2 by linarith]
  have hynorm : ‖y‖ = 1 + δ / 4 := by
    rw [hydef]
    simp [abs_of_pos, show (0:ℝ) < 1 + δ / 4 by linarith]
  have hxy : dist y x = δ / 4 + δ / 2 := by
    rw [hxdef, hydef]
    rw [PiLp.dist_single_same]
    rw [Real.dist_eq]
    rw [show (1 + δ / 4) - (1 - δ / 2) = δ / 4 + δ / 2 by ring, abs_of_pos (by linarith)]
  refine ⟨x, Metric.mem_ball.2 (by rw [dist_zero_right, hxnorm]; linarith), ?_⟩
  -- the escaping open set
  have hUopen : IsOpen (Metric.ball x δ \ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  have hyU : y ∈ Metric.ball x δ \ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    refine ⟨Metric.mem_ball.2 (by rw [hxy]; linarith), ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right, hynorm, not_le]
    linarith
  have hUpos : 0 < volume (Metric.ball x δ \
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    hUopen.measure_pos volume ⟨y, hyU⟩
  have hdiffpos : 0 < volume (Metric.ball x δ \ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    lt_of_lt_of_le hUpos
      (measure_mono (Set.sdiff_subset_sdiff_right Metric.ball_subset_closedBall))
  have hballtop : volume (Metric.ball x δ) ≠ ⊤ := measure_ball_lt_top.ne
  have hball0 : volume (Metric.ball x δ) ≠ 0 := (Metric.measure_ball_pos volume x hδ).ne'
  have hsplit : volume (Metric.ball x δ ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      + volume (Metric.ball x δ \ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      = volume (Metric.ball x δ) := measure_inter_add_sdiff _ measurableSet_ball
  have hlt : volume (Metric.ball x δ ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      < volume (Metric.ball x δ) := by
    rw [← hsplit]
    exact ENNReal.lt_add_right
      (ne_top_of_le_ne_top hballtop (measure_mono Set.inter_subset_left)) hdiffpos.ne'
  rw [ell_apply, ENNReal.div_lt_iff (Or.inl hball0) (Or.inl hballtop), one_mul]
  exact hlt

/-- **The non-vacuity witness, packaged** (`CLAUDE.md` §11).  For every dimension `n ≥ 1`,
every step `0 < δ < 1` and every temperature `σ² > 0` there is a body `K` — the unit ball —
and a constant `c ∈ (0, 1]` such that

* `K` is measurable and its Gaussian mass `ν K` is neither `0` nor `⊤`, so
  `Arlib.uniformOn ν K` is a genuine probability measure;
* the Gaussian smoothness hypothesis of `tvLe_ellGaussianProb_uniformOn` holds at `s = 1 - c`;
* `ℓ` is **not constant** on `K`: it is `1` at the centre and `< 1` somewhere;
* the bridge fires, with a bound `(1-c)/c` that is **finite** — so the conclusion is not the
  vacuous `TVLe _ _ ⊤`.

The explicit `c = e^{-(1-δ)²/(2σ²)}·(1-δ)ⁿ` of `gaussianSmooth_unitBall` is exponentially
small in `n` for `σ² = Θ(1/n)`; this witness certifies inhabitation, not usefulness.  For an
instance where the bound is additionally `< 1` — i.e. better than the free bound
`Arlib.tvLe_one` — see `exists_speedyToGaussian_witness_lt_one`. -/
theorem exists_speedyToGaussian_witness [NeZero n] {δ sq : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsq : 0 < sq) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (c : ℝ≥0∞),
      MeasurableSet K ∧ 0 < c ∧ c ≤ 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq)) K ≠ 0 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq)) K ≠ ⊤ ∧
      (1 - (1 - c)) *
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq)) K
        ≤ ∫⁻ x in K, ell K δ x * gaussianWeight sq x ∧
      (∃ x ∈ K, ell K δ x = 1) ∧ (∃ x ∈ K, ell K δ x < 1) ∧
      (1 - c) / c ≠ ⊤ ∧
      TVLe (ellGaussianProb K δ sq)
        (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight sq)) K) ((1 - c) / c) := by
  have hr0 : (0 : ℝ) ≤ 1 - δ := by linarith
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(1 - δ) ^ 2 / (2 * sq))) *
    ENNReal.ofReal ((1 - δ) ^ n) with hcdef
  have hc1 : c ≤ 1 := by
    rw [hcdef, ← one_mul (1 : ℝ≥0∞)]
    refine mul_le_mul' (ENNReal.ofReal_le_one.2 ?_) (ENNReal.ofReal_le_one.2 ?_)
    · exact Real.exp_le_one_iff.2 (by
        rw [neg_div]
        exact neg_nonpos.2 (div_nonneg (sq_nonneg _) (by linarith)))
    · exact pow_le_one₀ hr0 (by linarith)
  have hcpos : 0 < c := by
    rw [hcdef]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hsub : (1 : ℝ≥0∞) - (1 - c) = c := ENNReal.sub_sub_cancel ENNReal.one_ne_top hc1
  have hsmooth : (1 - (1 - c)) *
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight sq))
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x * gaussianWeight sq x := by
    rw [hsub, hcdef]
    exact gaussianSmooth_unitBall hδ (by linarith) hsq
  have hbridge : TVLe (ellGaussianProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ sq)
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight sq)) (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ((1 - c) / c) := by
    have h := tvLe_ellGaussianProb_uniformOn measurableSet_ball
      (withDensity_gaussianWeight_unitBall_ne_zero hsq)
      (withDensity_gaussianWeight_unitBall_ne_top hsq) hsmooth
    rwa [hsub] at h
  exact ⟨Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, c, measurableSet_ball, hcpos, hc1,
    withDensity_gaussianWeight_unitBall_ne_zero hsq,
    withDensity_gaussianWeight_unitBall_ne_top hsq, hsmooth,
    ⟨0, Metric.mem_ball_self one_pos, ell_unitBall_zero hδ (by linarith)⟩,
    exists_ell_unitBall_lt_one hδ (by linarith),
    -- the bound is finite: `1 - c ≤ 1 < ⊤` and `c > 0`
    (ENNReal.div_lt_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) hcpos.ne').ne,
    hbridge⟩

/-- **The witness beats the trivial bound**, in dimension one.

`TVLe μ ν 1` holds for *any* two probability measures (`Arlib.tvLe_one`), so a witness whose
bound is merely finite does not yet prove that `tvLe_ellGaussianProb_uniformOn` has content.
This one does: at `n = 1`, `δ = 1/4`, `σ² = 1` the constant of `gaussianSmooth_unitBall` is

    c = e^{-9/32}·(3/4) ≥ (23/32)·(3/4) = 69/128 > 1/2,

so the bound `(1-c)/c` is **strictly below `1`** — the speedy walk's stationary law is
provably closer to the Gaussian-restricted law than two arbitrary probability measures are.

`Real.add_one_le_exp` is the only numeric input (`e^{-x} ≥ 1 - x`).  The restriction to `n = 1`
is a restriction of *this* crude constant, not of the bridge. -/
theorem exists_speedyToGaussian_witness_lt_one :
    ∃ c : ℝ≥0∞, (1 - c) / c < 1 ∧
      TVLe (ellGaussianProb (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) (1 / 4) 1)
        (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin 1))).withDensity
          (gaussianWeight 1)) (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1)) ((1 - c) / c) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(1 - 1 / 4 : ℝ) ^ 2 / (2 * 1))) *
    ENNReal.ofReal ((1 - 1 / 4 : ℝ) ^ (1 : ℕ)) with hcdef
  -- `e^{-9/32} ≥ 23/32`, hence `c ≥ 69/128 > 1/2`
  have hexp : (23 / 32 : ℝ) ≤ Real.exp (-(1 - 1 / 4 : ℝ) ^ 2 / (2 * 1)) := by
    have h := Real.add_one_le_exp (-(1 - 1 / 4 : ℝ) ^ 2 / (2 * 1))
    norm_num at h ⊢
    linarith
  have hcge : ENNReal.ofReal (69 / 128 : ℝ) ≤ c := by
    rw [hcdef, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    norm_num
    linarith
  have hc1 : c ≤ 1 := by
    rw [hcdef, ← one_mul (1 : ℝ≥0∞)]
    refine mul_le_mul' (ENNReal.ofReal_le_one.2 ?_) (ENNReal.ofReal_le_one.2 (by norm_num))
    exact Real.exp_le_one_iff.2 (by norm_num)
  have hcpos : 0 < c :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num)) hcge
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
  have hsub : (1 : ℝ≥0∞) - (1 - c) = c := ENNReal.sub_sub_cancel ENNReal.one_ne_top hc1
  have hsmooth : (1 - (1 - c)) *
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))).withDensity (gaussianWeight 1))
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1)
      ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
          ell (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) (1 / 4) x * gaussianWeight 1 x := by
    rw [hsub, hcdef]
    exact gaussianSmooth_unitBall (by norm_num) (by norm_num) (by norm_num)
  refine ⟨c, ?_, ?_⟩
  · -- `(1-c)/c < 1` because `1 - c ≤ 59/128 < 69/128 ≤ c`
    rw [ENNReal.div_lt_iff (Or.inl hcpos.ne') (Or.inl hctop), one_mul]
    calc (1 : ℝ≥0∞) - c ≤ 1 - ENNReal.ofReal (69 / 128 : ℝ) := tsub_le_tsub_left hcge 1
      _ = ENNReal.ofReal (59 / 128 : ℝ) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
          norm_num
      _ < ENNReal.ofReal (69 / 128 : ℝ) :=
          (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
      _ ≤ c := hcge
  · have h := tvLe_ellGaussianProb_uniformOn (K := Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1)
      measurableSet_ball (withDensity_gaussianWeight_unitBall_ne_zero one_pos)
      (withDensity_gaussianWeight_unitBall_ne_top one_pos) hsmooth
    rwa [hsub] at h

/-! ## Axiom check -/

#print axioms ellGaussianMeasure_le_withDensity_inter
#print axioms withDensity_gaussianWeight_le_volume
#print axioms tvLe_ellGaussianProb_uniformOn
#print axioms gaussianSmooth_unitBall
#print axioms exists_ell_unitBall_lt_one
#print axioms exists_speedyToGaussian_witness
#print axioms exists_speedyToGaussian_witness_lt_one

end Arlib.MarkovChains
