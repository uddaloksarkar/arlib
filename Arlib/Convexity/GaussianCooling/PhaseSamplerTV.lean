/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.SpeedyGaussianMixing
import Arlib.MarkovChains.Continuous.MapSpeedyToTarget
import Arlib.Convexity.GaussianCooling.PhaseMeanRoute

/-!
# The per-phase sampler guarantee `hTV`, composed

`Ttc/Volume/CVAmended.lean`'s `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmended`
derives the volume algorithm's last two hypotheses from a single sampler assumption,

    Arlib.TVLe ((ν j i).map (X K ε p j i))
      (Arlib.GaussianCooling.coolLaw (phases K ε p) (σsq K ε p) K i) (tvErr K ε p j i)

**This file discharges that assumption**, in `Arlib` terms (`Arlib` cannot import `Ttc`), by
composing the three pieces that were already in the tree:

| step | supplier |
| --- | --- |
| mixing of the lazy speedy Metropolis–Gaussian walk to `ellGaussianProb K δ σ²` | `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit` |
| the rejection routine turning the speedy law into the Gaussian target | `Arlib.MarkovChains.tvLe_speedyRejection_target` |
| the identification of that target with `coolLaw` | §1 below, **proved here** |

## 1.  The identification, which is where a silent mismatch could have hidden

    coolLaw m σsq K i
      = Arlib.condOn ((volume.restrict K).withDensity (gaussianWeight (σsq i))) Set.univ

(`coolLaw_eq_condOn_gaussianRestrict`).  The right-hand side is the target of
`tvLe_speedyRejection_target` **character for character**.  They *are* the same measure — but
only under guards that must be carried, and are:

* **`i < m` is essential.**  At `i ≥ m` the cooling weight is the constant `1`
  (`coolWeight_of_ge`, which is what makes `chain_end` exact) and `coolLaw` is the *uniform*
  law on `K`, not the Gaussian one.  The identification is FALSE there.  `hTV` quantifies `i`
  over `Fin (phases K ε p)`, so `(i : ℕ) < m` is exactly what the consumer supplies.
* **`MeasurableSet K` is essential** and is *not* among `hTV`'s binders in `CVAmended.lean`
  (they are `0 < ε`, `0 < p`, `p < 1`, `Convex ℝ K`, `ball 0 1 ⊆ K`, `volume K ≠ ⊤`).  The
  `Ttc`-side wiring must supply it; convexity does not give it in general.
* `ball 0 1 ⊆ K`, `volume K ≠ ⊤` and `∀ j, 0 < σsq j` are needed for `chain m σsq K i > 0`,
  i.e. for `coolLaw` to be normalised at all.  All three are already `hTV` binders.

Neither measure is over `interior K`, neither carries an extra normalisation, and the
variance index matches: `coolLaw … i` uses `σsq i`, the rejection target uses `s = σsq i`.
There is **no** discrepancy beyond the `i < m` guard.

## 2.  What is proved

| name | content |
| --- | --- |
| `condOn_restrict_withDensity_univ` | `condOn ((volume.restrict K).withDensity g) univ = uniformOn (volume.withDensity g) K` |
| `coolLaw_eq_condOn_gaussianRestrict` | **the identification**, for `i < m` |
| `ellGaussianProb_eq_condOn` | `ellGaussianProb K δ s = condOn (ellGaussianMeasure K δ s) univ` |
| `tvLe_speedyRejection_coolLaw` | any law within `ε ≤ 1/32` of the speedy law post-processes to within `64·ε` of `coolLaw` |
| `tvLe_speedyRejection_coolLaw_of_mixing` | the end-to-end per-phase guarantee, from geometry + warm start + step count |
| `tvLe_speedyRejection_coolLaw_of_mixing_witness` | non-vacuity, with a non-trivial `1/2` conclusion |

## 3.  The resulting `tvErr`

    tvErr = 64 * ENNReal.ofReal eps

where `eps` is the mixing tolerance, subject to `eps ≤ 1/32` (the rejection lemma's binder,
strictly stronger than the mixing theorem's `eps ≤ 1`).  For the bound to be non-trivial one
needs `eps < 1/64`; the witness uses `eps = 1/128`, giving `tvErr = ofReal (1/2)`.

The `64` is `Arlib.MarkovChains.tvLe_speedyRejection_target`'s constant, not
Cousins–Vempala's `10`; see that file's docstring for the breakdown and for the
renormalisation factor their proof omits.

## 4.  The regime, and the hypotheses carried unproved

`n ≥ 21` (the conductance bound's) and **two independent step-size constraints**, neither
implying the other:

* `δ ≤ σ/(8√n)` — the speedy conductance bound;
* `δ ≤ 1/(2n)` — the rejection routine, where `1 − c = 1/(2n)` is the shrink slack.

Carried as hypotheses, not proved here:

* **the warm start** `Arlib.IsWarm (ENNReal.ofReal M) mu0 (ellGaussianProb K δ σ²)`, and
* the geometric data `R` with `K ⊆ R·Bₙ` and `R ≤ 2σ√n`.

**The warm start is a genuine residual gap, and it is not the one `WarmChain.lean` closes.**
`Arlib.GaussianCooling.isWarm_coolLaw_succ_exp` warms `coolLaw i` against `coolLaw (i+1)` —
both Gaussian laws.  The chain here must be started warm against `ellGaussianProb K δ σ²`,
which carries the extra local-conductance factor `ell K δ`, and the sup-ratio
`coolLaw / ellGaussianProb` is controlled only by a pointwise floor on `ell`.
`Arlib/MarkovChains/Continuous/EllFloor.lean` shows no uniform such floor exists on this
consumer's class (`ell ≤ 2⁻ⁿ` at a cube corner, at every `δ`), so the bridge cannot be built
that way.  Closing it needs either a warm-start statement about the speedy law directly or
an `ell`-free variant of the chain.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1.  The load-bearing identification -/

/-- **Conditioning a density-on-`K` measure on `Set.univ` is the same as normalising the
ambient density measure on `K`.**  Pure bookkeeping: `Measure.restrict_withDensity` moves the
restriction across the density, and `Measure.restrict_apply_univ` identifies the two
normalising constants. -/
theorem condOn_restrict_withDensity_univ {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (g : EuclSpace n → ℝ≥0∞) :
    Arlib.condOn ((volume.restrict K).withDensity g) Set.univ
      = Arlib.uniformOn ((volume : Measure (EuclSpace n)).withDensity g) K := by
  rw [Arlib.condOn_def, Arlib.uniformOn_def, Measure.restrict_univ,
    ← restrict_withDensity hKm, Measure.restrict_apply_univ]

/-- **The phase law is the rejection routine's target measure.**

    coolLaw m σsq K i = Arlib.condOn ((volume.restrict K).withDensity (gaussianWeight (σsq i)))
                          Set.univ

for every *interior* phase `i < m`.  The right-hand side is, character for character, the
target of `Arlib.MarkovChains.tvLe_speedyRejection_target`.

The hypothesis `i < m` is **not** cosmetic: at `i ≥ m` the cooling weight is the constant `1`
(`coolWeight_of_ge`) and `coolLaw` is the *uniform* law on `K`, which is not the Gaussian one.
`MeasurableSet K` is likewise needed and is not implied by convexity. -/
theorem coolLaw_eq_condOn_gaussianRestrict {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) {i : ℕ} (hi : i < m) :
    coolLaw m σsq K i
      = Arlib.condOn ((volume.restrict K).withDensity
          (MarkovChains.gaussianWeight (σsq i))) Set.univ := by
  rw [condOn_restrict_withDensity_univ hKm,
    coolLaw_eq_uniformOn_gaussianWeight hσ hKm hball hfin hi]

/-- **The speedy walk's stationary probability measure is its unnormalised measure conditioned
on `Set.univ`.**  This is the bridge between the mixing theorem's target
(`ellGaussianProb`) and the rejection lemma's source hypothesis. -/
theorem ellGaussianProb_eq_condOn (K : Set (EuclSpace n)) (δ s : ℝ) :
    MarkovChains.ellGaussianProb K δ s
      = Arlib.condOn (MarkovChains.ellGaussianMeasure K δ s) Set.univ := by
  rw [MarkovChains.ellGaussianProb, Arlib.condOn_def, Measure.restrict_univ]

/-! ## 2.  The link: any law close to the speedy stationary law post-processes onto `coolLaw` -/

/-- **The rejection routine lands on the phase law.**

If `P` — the law of whatever the sampler actually produces — is within total variation `ε`
of the speedy walk's stationary law `ellGaussianProb K δ (σsq i)`, and `ε ≤ 1/32`, then the
Cousins–Vempala post-processing at shrink factor `c = 1 − 1/(2n)`

1. condition on `c·K`,
2. rescale `u ↦ u/c`,
3. filter by `speedyAcceptReal c (σsq i)`,
4. renormalise,

produces a law within total variation `64·ε` of `Arlib.GaussianCooling.coolLaw m σsq K i`.

This is `Arlib.MarkovChains.tvLe_speedyRejection_target` composed with
`coolLaw_eq_condOn_gaussianRestrict`; nothing is assumed beyond the two theorems' own
binders. -/
theorem tvLe_speedyRejection_coolLaw (hn : 1 ≤ n) {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) {i : ℕ} (hi : i < m)
    {P : Measure (EuclSpace n)} [IsProbabilityMeasure P] {ε : ℝ≥0∞}
    (hP : Arlib.TVLe P (MarkovChains.ellGaussianProb K δ (σsq i)) ε)
    (hε : ε ≤ ENNReal.ofReal (1 / 32)) :
    Arlib.TVLe
      (Arlib.condOn
        ((Measure.map (fun x : EuclSpace n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
            (Arlib.condOn P ((1 - 1 / (2 * (n : ℝ))) • K))).withDensity
          fun v => ENNReal.ofReal
            (MarkovChains.speedyAcceptReal (1 - 1 / (2 * (n : ℝ))) (σsq i) v))
        Set.univ)
      (coolLaw m σsq K i) (64 * ε) := by
  rw [coolLaw_eq_condOn_gaussianRestrict hσ hKm hball hfin hi]
  refine MarkovChains.tvLe_speedyRejection_target hn hKm hKc hball hfin hδ hδn (hσ i) ?_ hε
  rwa [← ellGaussianProb_eq_condOn]

/-! ## 3.  The end-to-end per-phase guarantee -/

/-- **`hTV` for one phase, from geometry, a warm start and a step count.**

Run the lazy speedy Metropolis–Gaussian walk at variance `σsq i = σ²` and step `δ` from an
`M`-warm start `mu0` for `t` steps, then post-process by the Cousins–Vempala rejection
routine at `c = 1 − 1/(2n)`.  The resulting law is within total variation
`64·ENNReal.ofReal eps` of the phase law `Arlib.GaussianCooling.coolLaw m σsq K i`.

Both step-size regimes are carried and neither implies the other:
`hδσ : δ ≤ σ/(8√n)` is the conductance bound's, `hδn : δ ≤ 1/(2n)` is the rejection
routine's.  The accuracy binder is `eps ≤ 1/32`, the rejection lemma's, which is strictly
stronger than the mixing theorem's `eps ≤ 1`.

`volume K ≠ 0` is not a binder — it follows from `ball 0 1 ⊆ K`. -/
theorem tvLe_speedyRejection_coolLaw_of_mixing (hn : 21 ≤ n) {m : ℕ} {σsq : ℕ → ℝ}
    (hσ : ∀ j, 0 < σsq j) {σ δ R : ℝ} (hσpos : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hδn : δ ≤ 1 / (2 * (n : ℝ)))
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hRσ : R ≤ 2 * σ * Real.sqrt n)
    {i : ℕ} (hi : i < m) (hσsq : σsq i = σ ^ 2)
    {mu0 : Measure (EuclSpace n)} [IsProbabilityMeasure mu0] {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (MarkovChains.ellGaussianProb K δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    {t : ℕ} (ht : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2) ^ 2 + 1 ≤ (t : ℝ)) :
    Arlib.TVLe
      (Arlib.condOn
        ((Measure.map (fun x : EuclSpace n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
            (Arlib.condOn
              (MarkovChains.iterate
                (MarkovChains.lazy (MarkovChains.speedyMetropolisGaussian K δ (σsq i))) mu0 t)
              ((1 - 1 / (2 * (n : ℝ))) • K))).withDensity
          fun v => ENNReal.ofReal
            (MarkovChains.speedyAcceptReal (1 - 1 / (2 * (n : ℝ))) (σsq i) v))
        Set.univ)
      (coolLaw m σsq K i) (64 * ENNReal.ofReal eps) := by
  have hK0 : volume K ≠ 0 := by
    have hpos : 0 < volume (ball (0 : EuclSpace n) 1) :=
      Metric.measure_ball_pos volume 0 (by norm_num)
    exact (lt_of_lt_of_le hpos (measure_mono hball)).ne'
  have heps1 : eps ≤ 1 := le_trans heps32 (by norm_num)
  have hmix := Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit hn hσpos hδ hδσ
    hKm hKc hK0 hR hKR hRσ hM hwarm heps0 heps1 ht
  rw [Arlib.MarkovChains.mixesWithin_iff] at hmix
  rw [← hσsq] at hmix
  exact tvLe_speedyRejection_coolLaw (by omega) hσ hKm hKc hball hfin hδ hδn hi hmix
    (ENNReal.ofReal_le_ofReal heps32)

/-! ## 4.  Non-vacuity (`CLAUDE.md` §11)

Every binder of §3 discharged simultaneously at

    n = 21,  K = B̄(0,1) ⊆ ℝ²¹,  σ = 100,  δ = 1/42,  R = 1,
    m = 1,  σsq ≡ 100²,  i = 0,  mu0 = ellGaussianProb K δ σ²,  M = 1,
    eps = 1/128,  t = 2·10¹⁶.

`δ = 1/42 = 1/(2·21)` meets `hδn` with equality — the tightest legal step — and `hδσ` with
room, since `√21 ≤ 5` gives `100/(8√21) ≥ 5/2`.  The accuracy is `1/128`, **not** the largest
legal `1/32`: at `eps = 1/32` the conclusion's error is `64/32 = 2 ≥ 1` and the `TVLe`
statement is vacuous for probability measures.  At `eps = 1/128` the error is
`64/128 = 1/2`, a genuine bound, and that identity is carried as a conjunct.

The step count clears the deadline

    4·640²·100²·21·(log 1 + 2·log 128)/((1/42)·log 2)² + 1
      = 8497004544000000/log 2 + 1  ≈  1.226·10¹⁶

because `log 2 > 0.6931471803` (`Real.log_two_gt_d9`).

**Degeneracy, stated plainly**: `m = 1` means a one-phase schedule, so `i = 0` is the only
phase and there is no cooling.  The witness certifies that §3's binder bundle is
satisfiable and that its conclusion is non-trivial; it does not exhibit a cooling schedule. -/
theorem tvLe_speedyRejection_coolLaw_of_mixing_witness :
    ∃ (nn m : ℕ) (K : Set (EuclSpace nn)) (σsq : ℕ → ℝ) (σ δ R : ℝ) (i : ℕ)
      (mu0 : Measure (EuclSpace nn)) (M eps : ℝ) (t : ℕ),
      21 ≤ nn ∧ (∀ j, 0 < σsq j) ∧ 0 < σ ∧ 0 < δ ∧
      δ ≤ σ / (8 * Real.sqrt nn) ∧ δ ≤ 1 / (2 * (nn : ℝ)) ∧
      MeasurableSet K ∧ Convex ℝ K ∧ ball (0 : EuclSpace nn) 1 ⊆ K ∧ volume K ≠ ⊤ ∧
      0 ≤ R ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧ R ≤ 2 * σ * Real.sqrt nn ∧
      i < m ∧ σsq i = σ ^ 2 ∧
      IsProbabilityMeasure mu0 ∧ 1 ≤ M ∧
      Arlib.IsWarm (ENNReal.ofReal M) mu0 (MarkovChains.ellGaussianProb K δ (σ ^ 2)) ∧
      0 < eps ∧ eps ≤ 1 / 32 ∧
      4 * 640 ^ 2 * σ ^ 2 * (nn : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
        / (δ * Real.log 2) ^ 2 + 1 ≤ (t : ℝ) ∧
      (64 : ℝ≥0∞) * ENNReal.ofReal eps = ENNReal.ofReal (1 / 2) ∧
      Arlib.TVLe
        (Arlib.condOn
          ((Measure.map (fun x : EuclSpace nn => (1 - 1 / (2 * (nn : ℝ)))⁻¹ • x)
              (Arlib.condOn
                (MarkovChains.iterate
                  (MarkovChains.lazy (MarkovChains.speedyMetropolisGaussian K δ (σsq i)))
                  mu0 t)
                ((1 - 1 / (2 * (nn : ℝ))) • K))).withDensity
            fun v => ENNReal.ofReal
              (MarkovChains.speedyAcceptReal (1 - 1 / (2 * (nn : ℝ))) (σsq i) v))
          Set.univ)
        (coolLaw m σsq K i) (64 * ENNReal.ofReal eps) := by
  classical
  have hcast : Real.sqrt ((21 : ℕ) : ℝ) = Real.sqrt (21 : ℝ) := by norm_num
  have hsq : Real.sqrt (21 : ℝ) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt (21 : ℝ) := Real.sqrt_nonneg _
  have h5 : Real.sqrt (21 : ℝ) ≤ 5 := by nlinarith
  have h4 : (4 : ℝ) ≤ Real.sqrt (21 : ℝ) := by nlinarith
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogne : Real.log 2 ≠ 0 := ne_of_gt hlogpos
  have hlog9 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  set K : Set (EuclSpace 21) := Metric.closedBall 0 1 with hKdef
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hKc : Convex ℝ K := convex_closedBall _ _
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall
  have hfin : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  have hball : ball (0 : EuclSpace 21) 1 ⊆ K := Metric.ball_subset_closedBall
  have hK0 : volume K ≠ 0 := by
    have : 0 < volume K :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume 0 (by norm_num : (0 : ℝ) < 1))
        (measure_mono Metric.ball_subset_closedBall)
    exact this.ne'
  have hKR : ∀ x ∈ K, ‖x‖ ≤ 1 := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  have hs : (0 : ℝ) < (100 : ℝ) ^ 2 := by norm_num
  haveI hprob : IsProbabilityMeasure
      (MarkovChains.ellGaussianProb K ((1 : ℝ) / 42) ((100 : ℝ) ^ 2)) :=
    MarkovChains.isProbabilityMeasure_ellGaussianProb
      (MarkovChains.ellGaussianMeasure_univ_ne_zero hKm hKc hKb hK0 (by norm_num)
        ((100 : ℝ) ^ 2))
      (ne_top_of_le_ne_top hfin (MarkovChains.ellGaussianMeasure_univ_le hs K ((1 : ℝ) / 42)))
  -- the deadline at `M = 1`, `eps = 1/128`, `δ = 1/42`, `σ = 100`, `n = 21`
  have hlog128 : Real.log (1 / ((1 : ℝ) / 128)) = 7 * Real.log 2 := by
    have h : (1 : ℝ) / ((1 : ℝ) / 128) = 2 ^ (7 : ℕ) := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have hdead : 4 * 640 ^ 2 * (100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ))
        * (Real.log 1 + 2 * Real.log (1 / ((1 : ℝ) / 128)))
        / (((1 : ℝ) / 42) * Real.log 2) ^ 2 + 1
      ≤ ((20000000000000000 : ℕ) : ℝ) := by
    have hkey : 4 * 640 ^ 2 * (100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ))
          * (Real.log 1 + 2 * Real.log (1 / ((1 : ℝ) / 128)))
          / (((1 : ℝ) / 42) * Real.log 2) ^ 2
        = 8497004544000000 / Real.log 2 := by
      rw [Real.log_one, hlog128]
      field_simp
      ring
    rw [hkey]
    have hbound : (8497004544000000 : ℝ) / Real.log 2 ≤ 19999999999999999 := by
      rw [div_le_iff₀ hlogpos]
      nlinarith
    push_cast
    linarith
  refine ⟨21, 1, K, fun _ => (100 : ℝ) ^ 2, 100, 1 / 42, 1, 0,
    MarkovChains.ellGaussianProb K ((1 : ℝ) / 42) ((100 : ℝ) ^ 2), 1, 1 / 128,
    20000000000000000, le_refl _, fun _ => hs, by norm_num, by norm_num, ?_, ?_, hKm, hKc,
    hball, hfin, by norm_num, hKR, ?_, by norm_num, rfl, hprob, le_refl _, ?_, by norm_num,
    by norm_num, ?_, ?_, ?_⟩
  · rw [hcast, le_div_iff₀ (by positivity)]
    nlinarith
  · norm_num
  · rw [hcast]; nlinarith
  · intro S _
    exact le_of_eq (by rw [ENNReal.ofReal_one, one_mul])
  · exact hdead
  · rw [show (64 : ℝ≥0∞) = ENNReal.ofReal 64 by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
    norm_num
  · exact tvLe_speedyRejection_coolLaw_of_mixing (n := 21) le_rfl (fun _ => hs) (by norm_num)
      (by norm_num) (by rw [hcast, le_div_iff₀ (by positivity)]; nlinarith) (by norm_num)
      hKm hKc hball hfin (by norm_num) hKR (by rw [hcast]; nlinarith) Nat.zero_lt_one rfl
      le_rfl (fun S _ => le_of_eq (by rw [ENNReal.ofReal_one, one_mul])) (by norm_num)
      (by norm_num) hdead

/-! ## 5.  Axiom check (`CLAUDE.md` §4) -/

section AxiomCheck

#print axioms Arlib.GaussianCooling.condOn_restrict_withDensity_univ
#print axioms Arlib.GaussianCooling.coolLaw_eq_condOn_gaussianRestrict
#print axioms Arlib.GaussianCooling.ellGaussianProb_eq_condOn
#print axioms Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw
#print axioms Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing
#print axioms Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing_witness

end AxiomCheck

end Arlib.GaussianCooling
