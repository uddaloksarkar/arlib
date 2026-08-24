/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.GaussianCooling.PhaseSamplerTV
import Arlib.Convexity.GaussianCooling.WarmChain

/-!
# The warm start for the speedy walk, from a start supported on the shrunken body

`Arlib/Convexity/GaussianCooling/PhaseSamplerTV.lean` chains the speedy Metropolis–Gaussian
mixing bound to the per-phase `hTV` guarantee, but carries one hypothesis unproved:

    Arlib.IsWarm (ENNReal.ofReal M) mu0 (MarkovChains.ellGaussianProb K δ (σ²))

`WarmChain.lean` supplies warmness of `coolLaw i` against `coolLaw (i+1)` — both *Gaussian*
laws — while the speedy stationary law `ellGaussianProb` carries the extra local-conductance
factor `ell K δ`, and `Arlib/MarkovChains/Continuous/EllFloor.lean` shows that no uniform
pointwise floor on `ell` exists on this class.  This file closes the gap on the shrunken
body instead of by a floor.

## The mechanism

At `c = 1 − 1/(2n)` and `δ ≤ 1 − c` the local conductance is **identically `1`** on `c·K`
(`Arlib.MarkovChains.ell_eq_one_on_shrunken`).  So for a start `μ` that lives on `c·K`,

    μ S = μ (S ∩ cK) ≤ M · (∫_{S∩cK} γ)/(∫_K γ)          (warmness against the Gaussian law)
        ≤ M · (∫_{S∩cK} γ)/(∫_K ℓ·γ)                      (ℓ ≤ 1 shrinks the normaliser)
        = M · (∫_{S∩cK} ℓ·γ)/(∫_K ℓ·γ)                    (ℓ ≡ 1 on cK)
        ≤ M · (ellGaussianProb K δ s) S.

Note what does **not** happen: the `ℓ`-deficit only *shrinks* the speedy law's normaliser, so
it *helps*, and the crux costs a factor of `1`, not `2`.  The factor `2` enters exactly once,
at the *conditioning* step, through `coolLaw i (c·K) ≥ 1/2`
(`half_le_lintegral_gaussianWeight_smul_set`, the `ℓ`-free twin of
`Arlib.MarkovChains.half_le_speedy_shrunken`).

## The hypothesis that cannot be dropped, and the proof that it cannot

Support on `c·K` **alone does not suffice**, and the naive statement

> `μ` a probability measure with `μ ((c•K)ᶜ) = 0` ⟹ `IsWarm 2 μ (ellGaussianProb K δ s)`

is **FALSE**, for every constant `M : ℝ≥0∞` whatsoever — finite or `⊤` — not just for `2`.
`Arlib.IsWarm` is a supremum of ratios over *all* measurable sets, while
`ellGaussianProb` is absolutely continuous
(`MarkovChains.ellGaussianProb_absolutelyContinuous`); a Dirac mass at a point of `c·K` is
supported on `c·K` and gives ratio `1/0` at a singleton.  This is
`exists_supported_on_shrunken_not_isWarm` below — machine-checked, not asserted.  The repair
is to carry the warmness of `μ` against the *Gaussian* law on `K` as a hypothesis; that is
precisely what the cooling chain supplies.

## What is proved

| name | content |
| --- | --- |
| `exists_supported_on_shrunken_not_isWarm` | support on `c·K` alone gives **no** warmness |
| `isWarm_ellGaussianProb_of_supported_on_shrunken` | **the crux**: warm vs. the Gaussian law + supported on `c·K` ⟹ warm vs. the speedy law, *with the same constant* |
| `isWarm_condOn` | conditioning inflates warmness by `(μ A)⁻¹` |
| `half_le_lintegral_gaussianWeight_smul_set` | `∫_{cK} γ ≥ ½ ∫_K γ` |
| `half_le_coolLaw_smul_set` | `coolLaw i (c·K) ≥ ½` |
| `isWarm_condOn_coolLaw_ellGaussianProb` | **the phase-to-phase warm start**, constant `2e` |
| `tvLe_speedyRejection_coolLaw_of_mixing_warmStart` | `PhaseSamplerTV`'s per-phase guarantee with the warm start **discharged** |
| `tvLe_speedyRejection_coolLaw_of_mixing_warmStart_witness` | non-vacuity, at a two-phase schedule on a genuine body |

## Scope, stated plainly

The chain of phase `i+1` is started from `condOn (coolLaw i) (c·K)` — the previous phase's
*exact* law, *conditioned on the shrunken body*.  That conditioning is a genuine modification
of the algorithm's start (it costs at most `2` expected redraws, by
`half_le_coolLaw_smul_set`), and it is not optional: without it the sup-ratio against the
speedy law is unbounded on this class, by `EllFloor.lean`.  Composing across phases —
starting from a law only `TVLe`-close to `coolLaw i` rather than from `coolLaw i` itself — is
not done here.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1.  Support on the shrunken body is not enough

Before proving the crux, the refutation of the statement it *replaces*.  This is the
statement one would like — support on `c·K` alone forcing warmness — and it is false. -/

/-- **Support on `c·K` alone gives no warmness at all, for any constant whatsoever.**

In dimension `1`, on `K = B̄(0,1)` at `c = δ = 1/2` and `s = 1`, the Dirac mass at the origin
is a probability measure supported on `c·K`, and it is not `M`-warm against
`MarkovChains.ellGaussianProb K δ s` for any `M : ℝ≥0∞`, `⊤` included: at the singleton
`{0}` the left side is `1` and the right side is `M · 0 = 0`, because the speedy law is
absolutely continuous for Lebesgue measure.

This is why `isWarm_ellGaussianProb_of_supported_on_shrunken` carries a warmness hypothesis
against the Gaussian law: it is not removable. -/
theorem exists_supported_on_shrunken_not_isWarm :
    ∃ (K : Set (EuclSpace 1)) (c δ s : ℝ) (μ : Measure (EuclSpace 1)),
      MeasurableSet K ∧ Convex ℝ K ∧ ball (0 : EuclSpace 1) 1 ⊆ K ∧ volume K ≠ ⊤ ∧
        0 < c ∧ c < 1 ∧ 0 < δ ∧ δ ≤ 1 - c ∧ 0 < s ∧
        IsProbabilityMeasure μ ∧ μ ((c • K)ᶜ) = 0 ∧
        ∀ M : ℝ≥0∞, ¬ Arlib.IsWarm M μ (MarkovChains.ellGaussianProb K δ s) := by
  classical
  refine ⟨closedBall (0 : EuclSpace 1) 1, 1 / 2, 1 / 2, 1, Measure.dirac 0,
    measurableSet_closedBall, convex_closedBall _ _, ball_subset_closedBall,
    measure_closedBall_lt_top.ne, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, Measure.dirac.isProbabilityMeasure, ?_, ?_⟩
  · -- the origin lies in the shrunken ball, so the complement is `dirac`-null
    have h0 : (0 : EuclSpace 1) ∈ (1 / 2 : ℝ) • closedBall (0 : EuclSpace 1) 1 :=
      ⟨0, mem_closedBall_self zero_le_one, smul_zero _⟩
    have hm : MeasurableSet (((1 / 2 : ℝ) • closedBall (0 : EuclSpace 1) 1)ᶜ) :=
      (MarkovChains.measurableSet_smul_set measurableSet_closedBall (by norm_num)).compl
    rw [Measure.dirac_apply' _ hm, Set.indicator_of_notMem (by simpa using h0)]
  · intro M hM
    have hsing : MarkovChains.ellGaussianProb (closedBall (0 : EuclSpace 1) 1) (1 / 2) 1
        ({0} : Set (EuclSpace 1)) = 0 :=
      MarkovChains.ellGaussianProb_absolutelyContinuous _ _ _ (measure_singleton _)
    have hle := hM ({0} : Set (EuclSpace 1)) (measurableSet_singleton _)
    rw [hsing, mul_zero, Measure.dirac_apply_of_mem (mem_singleton _)] at hle
    exact absurd hle (by simp)

/-! ## 2.  The crux -/

/-- **The crux: a start supported on the shrunken body transfers its Gaussian warmness to the
speedy law, with the same constant.**

If `μ` lives on `c·K` and is `M`-warm for the Gaussian law
`uniformOn (volume.withDensity (gaussianWeight s)) K`, then it is `M`-warm for the speedy
walk's stationary law `ellGaussianProb K δ s`, provided the step does not exceed the shrink
slack, `δ ≤ 1 − c`.

Two facts do the work, and neither costs anything:

* `ell ≡ 1` on `c·K` (`Arlib.MarkovChains.ell_eq_one_on_shrunken`), so on the set where `μ`
  actually lives the speedy density *is* the Gaussian density;
* `∫_K ℓ·γ ≤ ∫_K γ`, so the speedy law's normaliser is the *smaller* one and the ratio
  `μ/π` is if anything better than `μ/ν`.

Hence the constant is `M`, not `2M`: the `1/2` of the Kannan–Lovász–Simonovits shell bound is
**not** used here.  No finiteness of any of the three normalisers is needed — the argument is
an `ℝ≥0∞` chain that degrades gracefully at `∫_K ℓ·γ = 0`.

The warmness hypothesis is not removable: see `exists_supported_on_shrunken_not_isWarm`. -/
theorem isWarm_ellGaussianProb_of_supported_on_shrunken {K : Set (EuclSpace n)}
    (hKm : MeasurableSet K) (hKc : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    {c δ s : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hδ : 0 < δ) (hδc : δ ≤ 1 - c)
    {M : ℝ≥0∞} {μ : Measure (EuclSpace n)} (hsupp : μ ((c • K)ᶜ) = 0)
    (hwarm : Arlib.IsWarm M μ
      (Arlib.uniformOn ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight s)) K)) :
    Arlib.IsWarm M μ (MarkovChains.ellGaussianProb K δ s) := by
  have h0K : (0 : EuclSpace n) ∈ K := hball (mem_ball_self one_pos)
  have hcKm : MeasurableSet (c • K) := MarkovChains.measurableSet_smul_set hKm hc0.ne'
  have hcK : c • K ⊆ K := MarkovChains.smul_subset_of_convex hKc h0K hc0.le hc1.le
  intro S hS
  have hSc : MeasurableSet (S ∩ c • K) := hS.inter hcKm
  -- (1) `μ` is carried by `c·K`
  have hnull : μ (S \ c • K) = 0 := by
    refine measure_mono_null ?_ hsupp
    rw [Set.sdiff_eq]
    exact Set.inter_subset_right
  have hμS : μ S = μ (S ∩ c • K) := by
    rw [← measure_inter_add_sdiff S hcKm, hnull, add_zero]
  -- (2) the Gaussian law, evaluated on `S ∩ c·K`
  have hGapply : ∀ T : Set (EuclSpace n), MeasurableSet T →
      ((volume : Measure (EuclSpace n)).withDensity (MarkovChains.gaussianWeight s)) T
        = ∫⁻ x in T, MarkovChains.gaussianWeight s x := fun T hT => withDensity_apply _ hT
  have hνval : Arlib.uniformOn ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight s)) K (S ∩ c • K)
      = (∫⁻ x in S ∩ c • K, MarkovChains.gaussianWeight s x)
          / ∫⁻ x in K, MarkovChains.gaussianWeight s x := by
    rw [Arlib.uniformOn_apply _ hKm hSc,
      Set.inter_eq_left.2 (subset_trans Set.inter_subset_right hcK), hGapply _ hSc,
      hGapply _ hKm]
  -- (3) the speedy law, evaluated on `S`
  have hπval : MarkovChains.ellGaussianProb K δ s S
      = (∫⁻ x in K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x)⁻¹
          * ∫⁻ x in S ∩ K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x := by
    rw [MarkovChains.ellGaussianProb, Measure.smul_apply, smul_eq_mul,
      MarkovChains.ellGaussianMeasure_univ, MarkovChains.ellGaussianMeasure,
      withDensity_apply _ hS, Measure.restrict_restrict hS]
  -- (4) `ℓ ≡ 1` on the shrunken body
  have hell : (∫⁻ x in S ∩ c • K, MarkovChains.gaussianWeight s x)
      = ∫⁻ x in S ∩ c • K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x := by
    refine setLIntegral_congr_fun hSc (fun x hx => ?_)
    rw [MarkovChains.ell_eq_one_on_shrunken hKc hball hc0 hc1 hδ hδc hx.2, one_mul]
  -- (5) the numerator only grows, the denominator only shrinks
  have hAC : (∫⁻ x in S ∩ c • K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x)
      ≤ ∫⁻ x in S ∩ K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x :=
    lintegral_mono' (Measure.restrict_mono
      (Set.inter_subset_inter_right S hcK) le_rfl) le_rfl
  have hZB : (∫⁻ x in K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x)
      ≤ ∫⁻ x in K, MarkovChains.gaussianWeight s x := by
    refine lintegral_mono fun x => ?_
    calc MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x
        ≤ 1 * MarkovChains.gaussianWeight s x :=
          mul_le_mul_right' (MarkovChains.ell_le_one K δ x) _
      _ = MarkovChains.gaussianWeight s x := one_mul _
  rw [hπval]
  calc μ S = μ (S ∩ c • K) := hμS
    _ ≤ M * ((∫⁻ x in S ∩ c • K, MarkovChains.gaussianWeight s x)
          / ∫⁻ x in K, MarkovChains.gaussianWeight s x) := by
        rw [← hνval]; exact hwarm _ hSc
    _ = M * ((∫⁻ x in S ∩ c • K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x)
          * (∫⁻ x in K, MarkovChains.gaussianWeight s x)⁻¹) := by
        rw [div_eq_mul_inv, hell]
    _ ≤ M * ((∫⁻ x in S ∩ K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x)
          * (∫⁻ x in K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x)⁻¹) :=
        mul_le_mul_left' (mul_le_mul' hAC (ENNReal.inv_le_inv.2 hZB)) M
    _ = M * ((∫⁻ x in K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x)⁻¹
          * ∫⁻ x in S ∩ K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x) := by
        rw [mul_comm (∫⁻ x in S ∩ K, MarkovChains.ell K δ x * MarkovChains.gaussianWeight s x)]

/-! ## 3.  Conditioning, and where the factor `2` comes from -/

/-- **Conditioning inflates the warmness constant by exactly `(μ A)⁻¹`.**

`condOn μ A S = μ(S ∩ A)/μ A ≤ M·ν(S)/μ A`.  No hypothesis on `μ A` is needed: at
`μ A = 0` the right-hand constant is `⊤` and at `μ A = ⊤` the conditioned measure is `0`. -/
theorem isWarm_condOn {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} {M : ℝ≥0∞}
    (h : Arlib.IsWarm M μ ν) {A : Set Ω} (hA : MeasurableSet A) :
    Arlib.IsWarm (M * (μ A)⁻¹) (Arlib.condOn μ A) ν := by
  intro S hS
  rw [Arlib.condOn_apply μ hA hS]
  calc μ (S ∩ A) / μ A = μ (S ∩ A) * (μ A)⁻¹ := div_eq_mul_inv _ _
    _ ≤ M * ν S * (μ A)⁻¹ := by
        gcongr
        exact le_trans (h (S ∩ A) (hS.inter hA))
          (mul_le_mul_left' (measure_mono Set.inter_subset_left) M)
    _ = M * (μ A)⁻¹ * ν S := by ring

/-- **The `ℓ`-free twin of `Arlib.MarkovChains.half_le_speedy_shrunken`**: at
`c = 1 − 1/(2n)` the shrunken body carries at least half the Gaussian mass of `K`.

The proof is the one of `half_le_speedy_shrunken` with `ell` deleted: the dilation identity
`lintegral_gaussianWeight_smul_set` turns `∫_{cK} γ_s` into `cⁿ·∫_K γ_{s/c²}`, the widened
Gaussian dominates (`gaussianWeight_mono_variance`, which is where `0 < s` is used), and
`cⁿ ≥ 1/2` is `half_le_one_sub_inv_two_mul_pow`.  Neither convexity of `K` nor `ball 0 1 ⊆ K`
is needed. -/
theorem half_le_lintegral_gaussianWeight_smul_set (hn : 1 ≤ n) {K : Set (EuclSpace n)}
    (hK : MeasurableSet K) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (1 / 2) * (∫⁻ x in K, MarkovChains.gaussianWeight s x)
      ≤ ∫⁻ x in (1 - 1 / (2 * (n : ℝ))) • K, MarkovChains.gaussianWeight s x := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hhalf : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set c : ℝ := 1 - 1 / (2 * (n : ℝ)) with hcdef
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hscale : (∫⁻ x in c • K, MarkovChains.gaussianWeight s x)
      = ENNReal.ofReal (c ^ n) * ∫⁻ x in K, MarkovChains.gaussianWeight (s / c ^ 2) x :=
    MarkovChains.lintegral_gaussianWeight_smul_set hK hc0 s
  have hmono : (∫⁻ x in K, MarkovChains.gaussianWeight s x)
      ≤ ∫⁻ x in K, MarkovChains.gaussianWeight (s / c ^ 2) x := by
    refine lintegral_mono fun x => ?_
    refine MarkovChains.gaussianWeight_mono_variance hs ?_ x
    rw [le_div_iff₀ (by positivity)]
    have hcsq : c ^ 2 ≤ 1 := by nlinarith
    nlinarith [hs.le]
  rw [hscale]
  calc ENNReal.ofReal (1 / 2) * ∫⁻ x in K, MarkovChains.gaussianWeight s x
      ≤ ENNReal.ofReal (c ^ n) * ∫⁻ x in K, MarkovChains.gaussianWeight s x := by
        have hcn : ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (c ^ n) :=
          ENNReal.ofReal_le_ofReal
            (by rw [hcdef]; exact MarkovChains.half_le_one_sub_inv_two_mul_pow hn)
        exact mul_le_mul_right' hcn _
    _ ≤ ENNReal.ofReal (c ^ n) * ∫⁻ x in K, MarkovChains.gaussianWeight (s / c ^ 2) x := by
        gcongr

/-- **The phase law keeps at least half its mass on the shrunken body.**

This is the Gaussian-law form of Kannan–Lovász–Simonovits fact 1, and it is the *only* place
the factor `2` of the final warm-start constant comes from: conditioning phase `i`'s law on
`c·K` costs `(coolLaw i (c·K))⁻¹ ≤ 2`. -/
theorem half_le_coolLaw_smul_set (hn : 1 ≤ n) {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) {i : ℕ} (hi : i < m) :
    ENNReal.ofReal (1 / 2) ≤ coolLaw m σsq K i ((1 - 1 / (2 * (n : ℝ))) • K) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hhalf : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set c : ℝ := 1 - 1 / (2 * (n : ℝ)) with hcdef
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hcKm : MeasurableSet (c • K) := MarkovChains.measurableSet_smul_set hKm hc0.ne'
  have hcK : c • K ⊆ K :=
    MarkovChains.smul_subset_of_convex hKc (hball (mem_ball_self one_pos)) hc0.le hc1.le
  have h0 : (∫⁻ x in K, MarkovChains.gaussianWeight (σsq i) x) ≠ 0 :=
    (MarkovChains.lintegral_gaussianWeight_pos (hσ i) one_pos hball).ne'
  have htop : (∫⁻ x in K, MarkovChains.gaussianWeight (σsq i) x) ≠ ⊤ :=
    MarkovChains.lintegral_gaussianWeight_ne_top (hσ i) hfin
  rw [coolLaw_eq_uniformOn_gaussianWeight hσ hKm hball hfin hi,
    Arlib.uniformOn_apply _ hKm hcKm, Set.inter_eq_left.2 hcK,
    withDensity_apply _ hcKm, withDensity_apply _ hKm,
    ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop)]
  exact half_le_lintegral_gaussianWeight_smul_set hn hKm (hσ i)

/-! ## 4.  The phase-to-phase warm start -/

/-- **The warm start `PhaseSamplerTV.lean` was missing.**

Phase `i`'s law, *conditioned on the shrunken body* `c·K` — which is exactly the first step of
the Cousins–Vempala rejection routine, and therefore a law the algorithm already has in hand —
is `2e`-warm for the speedy walk's stationary law at phase `i+1`.

The constant factorises as

    2e  =  2                         (conditioning on `c·K`, via `half_le_coolLaw_smul_set`)
         × e                         (`WarmChain.isWarm_coolLaw_succ_exp`, the `n`-free
                                      consecutive-phase constant at `cc ≤ 1 + 2/n`)
         × 1                         (the crux: passing from the Gaussian law to the speedy
                                      law is free)

and it is free of `n`, of `K`, of the variance and of the phase index — which is what the
`log M` in the mixing time needs. -/
theorem isWarm_condOn_coolLaw_ellGaussianProb (hn : 1 ≤ n) {m : ℕ} {σsq : ℕ → ℝ}
    (hσ : ∀ j, 0 < σsq j) {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) {i : ℕ} (hi : i + 1 < m)
    {cc : ℝ} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : ℝ)) (hs : σsq (i + 1) = cc * σsq i)
    {δ : ℝ} (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) :
    Arlib.IsWarm (ENNReal.ofReal (2 * Real.exp 1))
      (Arlib.condOn (coolLaw m σsq K i) ((1 - 1 / (2 * (n : ℝ))) • K))
      (MarkovChains.ellGaussianProb K δ (σsq (i + 1))) := by
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
  have hcKm : MeasurableSet (c • K) := MarkovChains.measurableSet_smul_set hKm hc0.ne'
  -- the two-phase Gaussian warmness, conditioned on `c·K`
  have hstep : Arlib.IsWarm (ENNReal.ofReal (Real.exp 1)) (coolLaw m σsq K i)
      (coolLaw m σsq K (i + 1)) :=
    isWarm_coolLaw_succ_exp hi hKm hfin hKc hball hσ hcc1 hcc hs
  have hcond := isWarm_condOn hstep hcKm
  -- the conditioning cost is at most `2`
  have hmass : ENNReal.ofReal (1 / 2) ≤ coolLaw m σsq K i (c • K) :=
    half_le_coolLaw_smul_set hn hσ hKm hKc hball hfin (Nat.lt_of_succ_lt hi)
  have hinv2 : (coolLaw m σsq K i (c • K))⁻¹ ≤ 2 := by
    refine le_trans (ENNReal.inv_le_inv.2 hmass) (le_of_eq ?_)
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), inv_inv]
    simp
  have hconst : ENNReal.ofReal (Real.exp 1) * (coolLaw m σsq K i (c • K))⁻¹
      ≤ ENNReal.ofReal (2 * Real.exp 1) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (ENNReal.ofReal 2)]
    gcongr
    simpa using hinv2
  -- transport to the Gaussian law on `K`, then across the crux
  refine isWarm_ellGaussianProb_of_supported_on_shrunken hKm hKc hball hc0 hc1 hδ hδc
    (Arlib.condOn_compl_eq_zero _ hcKm) ?_
  rw [← coolLaw_eq_uniformOn_gaussianWeight hσ hKm hball hfin hi]
  exact hcond.mono hconst

/-! ## 5.  The per-phase guarantee, with the warm start discharged -/

/-- **`hTV` for one phase, with no warm-start hypothesis left.**

This is `Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing` with its `hwarm`
binder *discharged*: the chain of phase `i+1` is started from phase `i`'s law conditioned on
the shrunken body `c·K`, and `isWarm_condOn_coolLaw_ellGaussianProb` supplies the warmness
against `ellGaussianProb K δ σ²` with the explicit `n`-free constant `M = 2e`.

What is carried, and what is not:

* **carried**: the two independent step-size regimes `δ ≤ σ/(8√n)` (conductance) and
  `δ ≤ 1/(2n)` (rejection routine, `= 1 − c`), the dimension bound `n ≥ 21`, the geometric
  data `R` with `K ⊆ R·Bₙ` and `R ≤ 2σ√n`, and the schedule condition `cc ≤ 1 + 2/n`;
* **no longer carried**: the warm start, and the *existence* of a warm `mu0` — the start is
  now a named measure built from the previous phase.

The step count is the mixing theorem's deadline at `M = 2e`, i.e. with
`log M = log 2 + 1`.

**What the start is, stated plainly.**  The start is `condOn (coolLaw m σsq K i) (c·K)`: the
*exact* phase-`i` law, **conditioned on the shrunken body**.  Two honest caveats:

1. *The conditioning is a modification of the algorithm's start.*  Cousins–Vempala's
   rejection routine returns a point distributed as `coolLaw i` on all of `K`; running the
   next phase from that law *unconditioned* is **not** covered here, and cannot be: outside
   `c·K` the local conductance can be exponentially small
   (`Arlib/MarkovChains/Continuous/EllFloor.lean`), so the sup-ratio
   `coolLaw i / ellGaussianProb` is unbounded on this class.  Restarting until the sample
   lands in `c·K` is the fix, and it is cheap: by `half_le_coolLaw_smul_set` it succeeds with
   probability at least `1/2`, i.e. in at most `2` expected draws, independent of `n`.
2. *The start is the exact phase-`i` law, not the previous phase's sampler output.*
   Composing across phases — replacing `coolLaw i` by a law only `TVLe`-close to it — is a
   separate (additive) bookkeeping step and is not done here. -/
theorem tvLe_speedyRejection_coolLaw_of_mixing_warmStart (hn : 21 ≤ n) {m : ℕ} {σsq : ℕ → ℝ}
    (hσ : ∀ j, 0 < σsq j) {σ δ R : ℝ} (hσpos : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hδn : δ ≤ 1 / (2 * (n : ℝ)))
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hRσ : R ≤ 2 * σ * Real.sqrt n)
    {i : ℕ} (hi : i + 1 < m) (hσsq : σsq (i + 1) = σ ^ 2)
    {cc : ℝ} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : ℝ)) (hsched : σsq (i + 1) = cc * σsq i)
    {eps : ℝ} (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    {t : ℕ} (ht : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ)
        * (Real.log (2 * Real.exp 1) + 2 * Real.log (1 / eps)) / (δ * Real.log 2) ^ 2 + 1
      ≤ (t : ℝ)) :
    Arlib.TVLe
      (Arlib.condOn
        ((Measure.map (fun x : EuclSpace n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
            (Arlib.condOn
              (MarkovChains.iterate
                (MarkovChains.lazy
                  (MarkovChains.speedyMetropolisGaussian K δ (σsq (i + 1))))
                (Arlib.condOn (coolLaw m σsq K i) ((1 - 1 / (2 * (n : ℝ))) • K)) t)
              ((1 - 1 / (2 * (n : ℝ))) • K))).withDensity
          fun v => ENNReal.ofReal
            (MarkovChains.speedyAcceptReal (1 - 1 / (2 * (n : ℝ))) (σsq (i + 1)) v))
        Set.univ)
      (coolLaw m σsq K (i + 1)) (64 * ENNReal.ofReal eps) := by
  have hn1 : 1 ≤ n := by omega
  haveI hprob : IsProbabilityMeasure (coolLaw m σsq K i) :=
    coolLaw_isProbabilityMeasure hσ hball hfin i
  have hmass : ENNReal.ofReal (1 / 2) ≤ coolLaw m σsq K i ((1 - 1 / (2 * (n : ℝ))) • K) :=
    half_le_coolLaw_smul_set hn1 hσ hKm hKc hball hfin (Nat.lt_of_succ_lt hi)
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2) := by simp
  haveI hmu0 : IsProbabilityMeasure
      (Arlib.condOn (coolLaw m σsq K i) ((1 - 1 / (2 * (n : ℝ))) • K)) :=
    Arlib.isProbabilityMeasure_condOn _ (lt_of_lt_of_le hpos hmass).ne' (measure_ne_top _ _)
  have hwarm := isWarm_condOn_coolLaw_ellGaussianProb hn1 hσ hKm hKc hball hfin hi hcc1 hcc
    hsched hδ hδn
  rw [hσsq] at hwarm
  have hM : (1 : ℝ) ≤ 2 * Real.exp 1 := by
    have := Real.one_le_exp (le_refl (0 : ℝ))
    simp only [Real.exp_zero] at this
    nlinarith [Real.one_le_exp (zero_le_one : (0 : ℝ) ≤ 1)]
  exact tvLe_speedyRejection_coolLaw_of_mixing hn hσ hσpos hδ hδσ hδn hKm hKc hball hfin
    hR hKR hRσ hi hσsq hM hwarm heps0 heps32 ht

/-! ## 6.  Non-vacuity (`CLAUDE.md` §11)

Every binder of §5 discharged simultaneously at

    n = 21,  K = B̄(0,1) ⊆ ℝ²¹,  σ = 100,  δ = 1/42,  R = 1,
    m = 2,  σsq 0 = 100²·21/23,  σsq 1 = 100²,  cc = 23/21,  i = 0,
    eps = 1/128,  t = 2·10¹⁶.

Unlike `PhaseSamplerTV.tvLe_speedyRejection_coolLaw_of_mixing_witness` — whose `m = 1`
schedule has a single phase and therefore *no cooling* — this witness has **two distinct
variances** (`σsq 0 ≠ σsq 1`, carried as a conjunct), so the warm start is genuinely a
transfer from one phase to the next.  The ratio `cc = 23/21` sits *exactly* at the schedule
boundary `1 + 2/n` for `n = 21`.

The body is non-degenerate: `B̄(0,1) ⊆ ℝ²¹` is convex, bounded, contains the unit ball, has
positive finite volume and non-empty interior.  `δ = 1/42 = 1/(2·21)` meets `hδn` with
equality (the tightest legal step) and `hδσ` with room since `√21 ≤ 5`.  `eps = 1/128` makes
the conclusion `ofReal (1/2)`, a genuine bound, not the vacuous `≥ 1` that `eps = 1/32` would
give.

The deadline at `M = 2e` reads `log M + 2 log 128 = 15·log 2 + 1`, so it is

    606928896000000 · (15·log 2 + 1)/(log 2)² + 1  ≈  1.566·10¹⁶  ≤  2·10¹⁶,

using `0.6931471803 < log 2 < 0.6931471808` (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`). -/
theorem tvLe_speedyRejection_coolLaw_of_mixing_warmStart_witness :
    ∃ (nn m : ℕ) (K : Set (EuclSpace nn)) (σsq : ℕ → ℝ) (σ δ R cc : ℝ) (i : ℕ) (eps : ℝ)
      (t : ℕ),
      21 ≤ nn ∧ (∀ j, 0 < σsq j) ∧ 0 < σ ∧ 0 < δ ∧
        δ ≤ σ / (8 * Real.sqrt nn) ∧ δ ≤ 1 / (2 * (nn : ℝ)) ∧
        MeasurableSet K ∧ Convex ℝ K ∧ ball (0 : EuclSpace nn) 1 ⊆ K ∧ volume K ≠ ⊤ ∧
        0 ≤ R ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧ R ≤ 2 * σ * Real.sqrt nn ∧
        i + 1 < m ∧ σsq (i + 1) = σ ^ 2 ∧
        1 ≤ cc ∧ cc ≤ 1 + 2 / (nn : ℝ) ∧ σsq (i + 1) = cc * σsq i ∧ σsq i ≠ σsq (i + 1) ∧
        0 < eps ∧ eps ≤ 1 / 32 ∧
        4 * 640 ^ 2 * σ ^ 2 * (nn : ℝ)
            * (Real.log (2 * Real.exp 1) + 2 * Real.log (1 / eps)) / (δ * Real.log 2) ^ 2 + 1
          ≤ (t : ℝ) ∧
        (64 : ℝ≥0∞) * ENNReal.ofReal eps = ENNReal.ofReal (1 / 2) ∧
        Arlib.TVLe
          (Arlib.condOn
            ((Measure.map (fun x : EuclSpace nn => (1 - 1 / (2 * (nn : ℝ)))⁻¹ • x)
                (Arlib.condOn
                  (MarkovChains.iterate
                    (MarkovChains.lazy
                      (MarkovChains.speedyMetropolisGaussian K δ (σsq (i + 1))))
                    (Arlib.condOn (coolLaw m σsq K i) ((1 - 1 / (2 * (nn : ℝ))) • K)) t)
                  ((1 - 1 / (2 * (nn : ℝ))) • K))).withDensity
              fun v => ENNReal.ofReal
                (MarkovChains.speedyAcceptReal (1 - 1 / (2 * (nn : ℝ))) (σsq (i + 1)) v))
            Set.univ)
          (coolLaw m σsq K (i + 1)) (64 * ENNReal.ofReal eps) := by
  classical
  have hcast : Real.sqrt ((21 : ℕ) : ℝ) = Real.sqrt (21 : ℝ) := by norm_num
  have hsq : Real.sqrt (21 : ℝ) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt (21 : ℝ) := Real.sqrt_nonneg _
  have h5 : Real.sqrt (21 : ℝ) ≤ 5 := by nlinarith
  have h4 : (4 : ℝ) ≤ Real.sqrt (21 : ℝ) := by nlinarith
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogne : Real.log 2 ≠ 0 := ne_of_gt hlogpos
  have hlogL : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogU : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  set K : Set (EuclSpace 21) := Metric.closedBall 0 1 with hKdef
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hKc : Convex ℝ K := convex_closedBall _ _
  have hfin : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  have hball : ball (0 : EuclSpace 21) 1 ⊆ K := Metric.ball_subset_closedBall
  have hKR : ∀ x ∈ K, ‖x‖ ≤ 1 := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  set σsq : ℕ → ℝ := fun j => if j = 0 then (100 : ℝ) ^ 2 * 21 / 23 else (100 : ℝ) ^ 2
    with hσsqdef
  have hσ : ∀ j, 0 < σsq j := by
    intro j
    rw [hσsqdef]
    by_cases hj : j = 0 <;> simp [hj] <;> norm_num
  have hs1 : σsq 1 = (100 : ℝ) ^ 2 := by rw [hσsqdef]; norm_num
  have hs0 : σsq 0 = (100 : ℝ) ^ 2 * 21 / 23 := by rw [hσsqdef]; norm_num
  -- the deadline at `M = 2e`, `eps = 1/128`, `δ = 1/42`, `σ = 100`, `n = 21`
  have hlogM : Real.log (2 * Real.exp 1) = Real.log 2 + 1 := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero 1), Real.log_exp]
  have hlog128 : Real.log (1 / ((1 : ℝ) / 128)) = 7 * Real.log 2 := by
    have h : (1 : ℝ) / ((1 : ℝ) / 128) = 2 ^ (7 : ℕ) := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have hdead : 4 * 640 ^ 2 * (100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ))
        * (Real.log (2 * Real.exp 1) + 2 * Real.log (1 / ((1 : ℝ) / 128)))
        / (((1 : ℝ) / 42) * Real.log 2) ^ 2 + 1
      ≤ ((20000000000000000 : ℕ) : ℝ) := by
    have hkey : 4 * 640 ^ 2 * (100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ))
          * (Real.log (2 * Real.exp 1) + 2 * Real.log (1 / ((1 : ℝ) / 128)))
          / (((1 : ℝ) / 42) * Real.log 2) ^ 2
        = 606928896000000 * (15 * Real.log 2 + 1) / Real.log 2 ^ 2 := by
      rw [hlogM, hlog128]
      field_simp
      ring
    rw [hkey]
    have hbound : (606928896000000 : ℝ) * (15 * Real.log 2 + 1) / Real.log 2 ^ 2
        ≤ 19999999999999999 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hlogL, hlogU, hlogpos]
    push_cast
    linarith
  refine ⟨21, 2, K, σsq, 100, 1 / 42, 1, 23 / 21, 0, 1 / 128, 20000000000000000,
    le_refl _, hσ, by norm_num, by norm_num, ?_, by norm_num, hKm, hKc, hball, hfin,
    by norm_num, hKR, ?_, by norm_num, hs1, by norm_num, by norm_num, ?_, ?_,
    by norm_num, by norm_num, ?_, ?_, ?_⟩
  · rw [hcast, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [hcast]; nlinarith
  · rw [hs1, hs0]; norm_num
  · rw [hs1, hs0]; norm_num
  · exact hdead
  · rw [show (64 : ℝ≥0∞) = ENNReal.ofReal 64 by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
    norm_num
  · exact tvLe_speedyRejection_coolLaw_of_mixing_warmStart (n := 21) (cc := 23 / 21) le_rfl hσ
      (by norm_num) (by norm_num)
      (by rw [hcast, le_div_iff₀ (by positivity)]; nlinarith) (by norm_num)
      hKm hKc hball hfin (by norm_num) hKR (by rw [hcast]; nlinarith)
      (by norm_num) hs1 (by norm_num) (by norm_num) (by rw [hs1, hs0]; norm_num)
      (by norm_num) (by norm_num) hdead

section AxiomCheck

#print axioms Arlib.GaussianCooling.exists_supported_on_shrunken_not_isWarm
#print axioms Arlib.GaussianCooling.isWarm_ellGaussianProb_of_supported_on_shrunken
#print axioms Arlib.GaussianCooling.isWarm_condOn
#print axioms Arlib.GaussianCooling.half_le_lintegral_gaussianWeight_smul_set
#print axioms Arlib.GaussianCooling.half_le_coolLaw_smul_set
#print axioms Arlib.GaussianCooling.isWarm_condOn_coolLaw_ellGaussianProb
#print axioms Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing_warmStart
#print axioms Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing_warmStart_witness

end AxiomCheck

end Arlib.GaussianCooling
