/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Probability.TV
import Arlib.Convexity.GaussianCooling.PhaseVar
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The annealing warm-start chain: each Gaussian phase is `O(1)`-warm for the next

The Gaussian-cooling volume algorithm runs a ball walk once per phase, at variances
`σ²₀ < σ²₁ < ⋯`.  Its cost accounting is only valid because the *stationary law of phase
`i`* is an `M`-warm start for the chain of phase `i+1`, with an `M` that does **not** grow
with the dimension: the per-phase mixing time carries a `log M` factor, so an `M` of size
`e^{Θ(n)}` would cost a factor `n` per phase and destroy the bound.

This file proves that fact, in the `L∞` (sup-ratio) sense that the repository's
`Arlib.IsWarm` uses, with an explicit `n`-free constant.

## The mechanism, in one line

Write `Z(i) = ∫_K e^{-‖x‖²/(2σ²ᵢ)}` (`Arlib.GaussianCooling.chain`) and `λ = σᵢ₊₁/σᵢ ≥ 1`.
The phase densities are `wᵢ/Z(i)`, so

  `sup_x (density i x) / (density (i+1) x) = (Z(i+1)/Z(i)) · sup_x (wᵢ x / wᵢ₊₁ x) ≤ Z(i+1)/Z(i)`,

because a *wider* Gaussian is pointwise larger (`coolWeight_le_coolWeight`).  The whole
content is therefore the partition-function ratio, and that is bounded by rescaling:
substituting `x = λ·y` turns `∫_K wᵢ₊₁` into `λⁿ ∫_{λ⁻¹K} wᵢ`, and `λ⁻¹K ⊆ K` whenever `K`
is convex with `0 ∈ K`, so

  `Z(i+1) ≤ λⁿ · Z(i)`   (`chain_succ_le_pow_mul`).

Hence `M = λⁿ = (σ²ᵢ₊₁/σ²ᵢ)^{n/2}`, and the schedule condition `σ²ᵢ₊₁ ≤ (1 + c/n)σ²ᵢ` makes
that `≤ e^{c/2}` — free of `n`.  This is exactly why the repository's cooling-ratio binder
`cc ≤ 1 + 2/n` (`Ttc.ttc_runtime_mn4`, binder #33) has the shape it has: it is the largest
schedule for which the warm-start constant stays `O(1)`, and at `c = 2` the constant is `e`.

## Main results

* `Arlib.GaussianCooling.isWarm_withDensity_of_le` — the generic bridge: a pointwise bound
  on densities against a common base measure is `IsWarm`.
* `Arlib.GaussianCooling.coolWeight_le_coolWeight` — a wider Gaussian is pointwise larger.
* `Arlib.GaussianCooling.isWarm_coolLaw_of_le` — the assembly step: a pointwise weight
  bound plus a partition-function bound give `IsWarm`.
* `Arlib.GaussianCooling.chain_succ_le_pow_mul` — **the crux**: `Z(i+1) ≤ λⁿ Z(i)` for
  `σ²ᵢ₊₁ = λ²σ²ᵢ`, `λ ≥ 1`, on a convex `K ∋ 0`.  Proved by the rescaling `x ↦ λ·x`, which
  is strictly shorter and slightly more general (star-shapedness about `0` is all that is
  used) than the polar/cone argument of Cousins–Vempala.
* `Arlib.GaussianCooling.isWarm_coolLaw_succ` — **the two-phase warmness step**:
  `IsWarm (ofReal (λⁿ)) (coolLaw i) (coolLaw (i+1))`.
* `Arlib.GaussianCooling.isWarm_coolLaw_succ_exp` — the `n`-free form: under the schedule
  condition `σ²ᵢ₊₁ ≤ (1 + 2/n)σ²ᵢ` the constant is `e`, and under Cousins–Vempala's own
  `(1 + 1/n)` it is `√e` (`isWarm_coolLaw_succ_sqrt_exp`).
* `Arlib.GaussianCooling.isWarm_coolLaw_chain` — **the chain**: every consecutive pair on a
  schedule obeying the ratio condition is `e`-warm, with **one and the same `e`**.
* `Arlib.GaussianCooling.isWarm_coolLaw_add` — the composite `IsWarm (e^k)` from phase
  `i` to phase `i+k`.  Stated, and flagged: this is *not* the quantity the algorithm uses.
  Warmness does **not** telescope to `O(1)` across the whole schedule; what makes annealing
  work is that phase `i+1` restarts from phase `i`'s samples, so only the *consecutive*
  constant ever enters a mixing time.
* `Arlib.GaussianCooling.isWarm_coolLaw_terminal` — the terminal jump `σ²ₘ₋₁ → uniform`,
  which the rescaling argument does *not* cover (the terminal weight is `1`, not a
  Gaussian).  It is `e^{R²/(2σ²ₘ₋₁)}`-warm for `K ⊆ R·Bₙ`, hence `e`-warm once
  `σ²ₘ₋₁ ≥ R²/2` — no convexity needed.
* `Arlib.GaussianCooling.isWarm_coolLaw_of_subset_ball` — the radius route (Cousins–Vempala
  Lemma "sigma-large"): with `K ⊆ R·Bₙ` and no convexity at all, the constant is
  `e^{R²(cc−1)/(2·cc·σ²ᵢ)}`.
* `Arlib.GaussianCooling.exists_isWarm_coolLaw_succ` — the non-vacuity witness
  (`CLAUDE.md` §11): a concrete `n`, `K`, schedule and a concrete finite `M`.

## What this is measured against

Cousins–Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian Volume*
(arXiv:1409.6011), `vol3_journal.tex`:

* their warm-start parameter `M(P,Q) = sup_{S ⊆ K} P(S)/Q(S)` (`:303-306`) is **exactly**
  `Arlib.IsWarm`, so the comparison is literal, not analogical;
* Lemma `sigma-small-warmness` (`:751-757`) is `isWarm_coolLaw_succ_sqrt_exp` here;
* Lemma `sigma-large-warmness` (`:760-766`) is `isWarm_coolLaw_of_subset_ball` here.

Yin Tat Lee's book states the annealing warm start (`annealing.tex`, `thm:L2_warm_start`) in
the **`L²`/`χ²`** form `E_{pᵢ}(pᵢ/pᵢ₊₁) = O(1)` at the Lovász–Vempala power schedule
`aᵢ₊₁/aᵢ = 1 + 1/√n`.  That is a *weaker* conclusion than the `L∞` bound proved here (an
`L∞` bound implies the `L²` one; the converse fails), and it is about a different schedule
family.  The `L∞` statement matched to Gaussian cooling is Cousins–Vempala's.

## Scope

Nothing here is a Markov chain statement.  This file bounds the warmness *of the phase laws
against one another*; converting that into a mixing time is
`Arlib.MarkovChains.isWarm_iterate` plus a conductance bound, neither of which is touched.
No hypothesis class is introduced and no `Prop` is asserted without proof: every declaration
below is a theorem.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal

variable {n : ℕ}

/-! ## The generic bridge: a pointwise density bound is warmness

`Arlib.IsWarm M μ ν` is `∀ S, μ S ≤ M · ν S`.  When `μ` and `ν` are given by densities
against a *common* base measure — which is exactly how `Arlib.GaussianCooling.coolLaw` is
built, both phases reweighting `volume.restrict K` — a pointwise bound on the densities
gives it immediately, by monotonicity of the lower integral. -/

/-- **Pointwise density domination implies warmness.**  If `f ≤ M · g` pointwise then the
measure with density `f` is `M`-warm with respect to the measure with density `g`, against
any common base measure `μ`.

No finiteness, no probability-measure hypothesis, and no measurability of `f`: only `g` has
to be measurable, to pull the constant out of the lower integral. -/
theorem isWarm_withDensity_of_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ≥0∞} {M : ℝ≥0∞} (hg : Measurable g) (h : ∀ x, f x ≤ M * g x) :
    IsWarm M (μ.withDensity f) (μ.withDensity g) := by
  intro S hS
  rw [withDensity_apply _ hS, withDensity_apply _ hS]
  calc ∫⁻ x in S, f x ∂μ ≤ ∫⁻ x in S, M * g x ∂μ := lintegral_mono h
    _ = M * ∫⁻ x in S, g x ∂μ := lintegral_const_mul _ hg

/-- The phase-`i` density of `Arlib.GaussianCooling.coolLaw`, as an `ℝ≥0∞`-valued function,
is measurable. -/
theorem measurable_coolDensity (m : ℕ) (σsq : ℕ → ℝ) (K : Set (EuclSpace n)) (i : ℕ) :
    Measurable fun x : EuclSpace n =>
      ENNReal.ofReal (coolWeight m σsq i x / chain m σsq K i) :=
  (((continuous_coolWeight m σsq i).measurable).div_const _).ennreal_ofReal

/-! ## A wider Gaussian is pointwise larger

The first of the two factors in `sup_x pᵢ(x)/pᵢ₊₁(x) = (Z(i+1)/Z(i))·sup_x wᵢ(x)/wᵢ₊₁(x)`.
Since `σ²ᵢ ≤ σ²ᵢ₊₁`, the exponent `-‖x‖²/(2σ²)` increases with `σ²`, so `wᵢ ≤ wᵢ₊₁`
everywhere and the second factor is at most `1`.  Cousins–Vempala use exactly this step,
where it reads `sup_{x ∈ K} e^{-aᵢ‖x‖²/n} = 1` "since `0 ∈ K`" (`vol3_journal.tex:778`);
here it needs no reference to `K` at all. -/

/-- **A wider Gaussian dominates a narrower one, pointwise.**  For `0 < σsq i ≤ σsq j` and
both indices below the terminal index, `coolWeight i x ≤ coolWeight j x` for every `x`. -/
theorem coolWeight_le_coolWeight {m : ℕ} {σsq : ℕ → ℝ} {i j : ℕ} (hi : i < m) (hj : j < m)
    (hσ : 0 < σsq i) (hij : σsq i ≤ σsq j) (x : EuclSpace n) :
    coolWeight m σsq i x ≤ coolWeight m σsq j x := by
  rw [coolWeight_of_lt hi, coolWeight_of_lt hj]
  refine Real.exp_le_exp.2 ?_
  have hσj : 0 < σsq j := lt_of_lt_of_le hσ hij
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ‖x‖]

/-! ## The crux: the partition-function ratio

Everything `n`-free about the warm start is this one bound.  `Z(i+1) = ∫_K wᵢ₊₁` and
`Z(i) = ∫_K wᵢ` differ by the widening of the Gaussian, and the substitution `x = λ·y`
(`λ = σᵢ₊₁/σᵢ`) converts one integrand into the other exactly:
`wᵢ₊₁(λ·y) = wᵢ(y)`.  The Jacobian contributes `λⁿ`, and the domain `K` becomes `λ⁻¹K`,
which is *inside* `K` because `K` is convex and contains the origin.  Discarding
`K \ λ⁻¹K` — where the integrand is positive — is the only inequality used.

Cousins–Vempala prove the same bound (`vol3_journal.tex:781-802`) by decomposing `K` into
infinitesimal cones and comparing radial integrals; the rescaling below needs neither polar
coordinates nor convexity in full (star-shapedness about `0` is all that `λ⁻¹K ⊆ K` asks
for). -/

/-- **The crux.**  For a convex body `K` containing the origin and two consecutive Gaussian
phases with `σ²ᵢ₊₁ = λ²·σ²ᵢ`, `λ ≥ 1`, the partition functions satisfy

  `Z(i+1) ≤ λⁿ · Z(i)`.

`λⁿ = (σ²ᵢ₊₁/σ²ᵢ)^{n/2}` is exactly the ratio of the two *unrestricted* Gaussian integrals
over `ℝⁿ`; the content of the lemma is that restricting to `K` cannot make the ratio worse.

Proof: substitute `x = λ·y` in `Z(i+1)`, which is `MeasureTheory.integral_comp_smul` with
`finrank ℝ (EuclSpace n) = n`, and use `λ⁻¹K ⊆ K`. -/
theorem chain_succ_le_pow_mul {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (hi : i + 1 < m) (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hconv : Convex ℝ K) (h0 : (0 : EuclSpace n) ∈ K) (hσ : 0 < σsq i)
    {lam : ℝ} (hlam : 1 ≤ lam) (hs : σsq (i + 1) = lam ^ 2 * σsq i) :
    chain m σsq K (i + 1) ≤ lam ^ n * chain m σsq K i := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam
  have hlamne : lam ≠ 0 := ne_of_gt hlam0
  have him : i < m := Nat.lt_of_succ_lt hi
  -- The rescaled weight identity: `wᵢ₊₁(λ·x) = wᵢ(x)`.
  have hpt : ∀ x : EuclSpace n,
      coolWeight m σsq (i + 1) (lam • x) = coolWeight m σsq i x := by
    intro x
    rw [coolWeight_of_lt hi, coolWeight_of_lt him, norm_smul, Real.norm_eq_abs,
      abs_of_pos hlam0, hs]
    congr 1
    field_simp
  -- The rescaled domain, and the fact that it sits inside `K`.
  set T : Set (EuclSpace n) := (fun x : EuclSpace n => lam • x) ⁻¹' K with hTdef
  have hTm : MeasurableSet T := hKm.preimage (continuous_const_smul lam).measurable
  have hTK : T ⊆ K := by
    intro x hx
    have hx' : lam • x ∈ K := hx
    have hmem : lam⁻¹ • (lam • x) ∈ K :=
      hconv.smul_mem_of_zero_mem h0 hx'
        ⟨le_of_lt (inv_pos.2 hlam0), inv_le_one_of_one_le₀ hlam⟩
    rwa [inv_smul_smul₀ hlamne] at hmem
  -- Change of variables.
  have h1 : ∀ x : EuclSpace n,
      Set.indicator K (coolWeight m σsq (i + 1)) (lam • x)
        = Set.indicator T (coolWeight m σsq i) x := by
    intro x
    by_cases hx : lam • x ∈ K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ T from hx), hpt]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ T from hx)]
  have hcov : (∫ x in T, coolWeight m σsq i x)
      = (lam ^ n)⁻¹ * chain m σsq K (i + 1) := by
    have hchange := Measure.integral_comp_smul (E := EuclSpace n) volume
      (Set.indicator K (coolWeight m σsq (i + 1))) lam
    rw [finrank_euclideanSpace_fin, abs_of_nonneg (by positivity : (0:ℝ) ≤ (lam ^ n)⁻¹),
      smul_eq_mul] at hchange
    rw [← integral_indicator hTm,
      ← integral_congr_ae (Filter.Eventually.of_forall h1), hchange,
      integral_indicator hKm, chain_def]
  -- Discard `K \ T`, on which the integrand is positive.
  have hmono : (∫ x in T, coolWeight m σsq i x) ≤ chain m σsq K i :=
    setIntegral_mono_set (integrableOn_coolWeight hσ hfin)
      (Filter.Eventually.of_forall fun x => (coolWeight_pos m σsq i x).le)
      (Filter.Eventually.of_forall fun x hx => hTK hx)
  rw [hcov] at hmono
  have hlamn : (0 : ℝ) < lam ^ n := by positivity
  have hfin' := mul_le_mul_of_nonneg_left hmono (le_of_lt hlamn)
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hlamn), one_mul] at hfin'

/-! ## The two-phase warmness step

The crux plus the pointwise monotonicity, assembled.  The warmness constant is `λⁿ` with
`λ = σᵢ₊₁/σᵢ`; nothing else about `K` enters. -/

/-- **The two-phase warmness step.**  On a convex body containing the unit ball, the
phase-`i` law is `λⁿ`-warm for the phase-`i+1` law, where `σ²ᵢ₊₁ = λ²σ²ᵢ` and `λ ≥ 1`.

This is Cousins–Vempala's `M(Qᵢ, Qᵢ₊₁) ≤ A` (`vol3_journal.tex:767-780`) with `A` the
partition-function ratio, together with the bound on `A` (`chain_succ_le_pow_mul`). -/
theorem isWarm_coolLaw_of_le {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (hfin : volume K ≠ ⊤) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hσ : ∀ j, 0 < σsq j)
    {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ x : EuclSpace n, coolWeight m σsq i x ≤ coolWeight m σsq (i + 1) x)
    (hZ : chain m σsq K (i + 1) ≤ M * chain m σsq K i) :
    IsWarm (ENNReal.ofReal M) (coolLaw m σsq K i) (coolLaw m σsq K (i + 1)) := by
  have hZi : 0 < chain m σsq K i := chain_pos hσ hball hfin i
  have hZi1 : 0 < chain m σsq K (i + 1) := chain_pos hσ hball hfin (i + 1)
  refine isWarm_withDensity_of_le (measurable_coolDensity m σsq K (i + 1)) fun x => ?_
  have hreal : coolWeight m σsq i x / chain m σsq K i
      ≤ M * (coolWeight m σsq (i + 1) x / chain m σsq K (i + 1)) := by
    rw [mul_div_assoc', div_le_div_iff₀ hZi hZi1]
    calc coolWeight m σsq i x * chain m σsq K (i + 1)
        ≤ coolWeight m σsq i x * (M * chain m σsq K i) :=
          mul_le_mul_of_nonneg_left hZ (coolWeight_pos m σsq i x).le
      _ ≤ coolWeight m σsq (i + 1) x * (M * chain m σsq K i) :=
          mul_le_mul_of_nonneg_right (hw x) (mul_nonneg hM hZi.le)
      _ = M * coolWeight m σsq (i + 1) x * chain m σsq K i := by ring
  calc ENNReal.ofReal (coolWeight m σsq i x / chain m σsq K i)
      ≤ ENNReal.ofReal (M * (coolWeight m σsq (i + 1) x / chain m σsq K (i + 1))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal M
          * ENNReal.ofReal (coolWeight m σsq (i + 1) x / chain m σsq K (i + 1)) :=
        ENNReal.ofReal_mul hM

/-- **The two-phase warmness step**, the `λⁿ` form. -/
theorem isWarm_coolLaw_succ {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (hi : i + 1 < m) (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hconv : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hσ : ∀ j, 0 < σsq j)
    {lam : ℝ} (hlam : 1 ≤ lam) (hs : σsq (i + 1) = lam ^ 2 * σsq i) :
    IsWarm (ENNReal.ofReal (lam ^ n)) (coolLaw m σsq K i) (coolLaw m σsq K (i + 1)) := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam
  have him : i < m := Nat.lt_of_succ_lt hi
  have h0 : (0 : EuclSpace n) ∈ K := hball (mem_ball_self one_pos)
  have hl2 : (1 : ℝ) ≤ lam ^ 2 := by nlinarith
  have hmono : σsq i ≤ σsq (i + 1) := by
    rw [hs]; nlinarith [hσ i]
  exact isWarm_coolLaw_of_le hfin hball hσ (by positivity)
    (fun x => coolWeight_le_coolWeight him hi (hσ i) hmono x)
    (chain_succ_le_pow_mul hi hKm hfin hconv h0 (hσ i) hlam hs)

/-! ## Making the constant `n`-free

`λⁿ = (σ²ᵢ₊₁/σ²ᵢ)^{n/2} = cc^{n/2}`, so the schedule condition `cc ≤ 1 + c/n` gives
`λⁿ ≤ e^{c/2}` by `(1 + c/n)ⁿ ≤ e^c`.  This is the entire reason the Gaussian-cooling
schedule has a `1 + O(1/n)` ratio, and it is the mathematical content of the repository's
binder `hcc : cc ≤ 1 + 2/n`. -/

/-- **`cc^{n/2} ≤ e^{c/2}` under the schedule condition `cc ≤ 1 + c/n`.**  The `n` in the
exponent and the `n` in the schedule cancel: `(1 + c/n)ⁿ ≤ (e^{c/n})ⁿ = e^c`.

Stated for the square root because `√cc ^ n` is `cc^{n/2}` written with a natural power.
Degenerate `n = 0` is included: there `c/n = 0`, so `cc = 1` and both sides are `≥ 1`. -/
theorem sqrt_pow_le_exp {cc c : ℝ} (hcc1 : 1 ≤ cc) (hc : 0 ≤ c)
    (hcc : cc ≤ 1 + c / (n : ℝ)) : Real.sqrt cc ^ n ≤ Real.exp (c / 2) := by
  have hcc0 : (0 : ℝ) ≤ cc := le_trans zero_le_one hcc1
  -- `cc ^ n ≤ e^c`
  have hpow : cc ^ n ≤ Real.exp c := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa using Real.one_le_exp hc
    · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have hstep : cc ≤ Real.exp (c / (n : ℝ)) :=
        le_trans hcc (by simpa [add_comm] using Real.add_one_le_exp (c / (n : ℝ)))
      calc cc ^ n ≤ Real.exp (c / (n : ℝ)) ^ n := pow_le_pow_left₀ hcc0 hstep n
        _ = Real.exp ((n : ℝ) * (c / (n : ℝ))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp c := by rw [mul_div_cancel₀ _ hn0]
  -- compare squares
  have hsq : (Real.sqrt cc ^ n) ^ 2 ≤ (Real.exp (c / 2)) ^ 2 := by
    have h1 : (Real.sqrt cc ^ n) ^ 2 = cc ^ n := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hcc0]
    have h2 : (Real.exp (c / 2)) ^ 2 = Real.exp c := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [h1, h2]; exact hpow
  have h3 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (Real.exp_pos _).le] at h3

/-- **The two-phase step in schedule form.**  If the variance grows by the factor `cc` from
phase `i` to phase `i+1`, the phase-`i` law is `cc^{n/2}`-warm for the phase-`i+1` law. -/
theorem isWarm_coolLaw_succ_of_ratio {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (hi : i + 1 < m) (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hconv : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hσ : ∀ j, 0 < σsq j)
    {cc : ℝ} (hcc1 : 1 ≤ cc) (hs : σsq (i + 1) = cc * σsq i) :
    IsWarm (ENNReal.ofReal (Real.sqrt cc ^ n)) (coolLaw m σsq K i)
      (coolLaw m σsq K (i + 1)) := by
  refine isWarm_coolLaw_succ hi hKm hfin hconv hball hσ
    (Real.one_le_sqrt.2 hcc1) ?_
  rw [hs, Real.sq_sqrt (le_trans zero_le_one hcc1)]

/-- **The `n`-free two-phase step**, at the repository's own schedule condition
`cc ≤ 1 + 2/n` (`Ttc.ttc_runtime_mn4`, binder `hcc`, #33): the phase-`i` law is
**`e`-warm** for the phase-`i+1` law, and `e` does not depend on `n`, on `K`, on the
variance, or on the phase index. -/
theorem isWarm_coolLaw_succ_exp {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (hi : i + 1 < m) (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hconv : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hσ : ∀ j, 0 < σsq j)
    {cc : ℝ} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : ℝ)) (hs : σsq (i + 1) = cc * σsq i) :
    IsWarm (ENNReal.ofReal (Real.exp 1)) (coolLaw m σsq K i) (coolLaw m σsq K (i + 1)) := by
  refine (isWarm_coolLaw_succ_of_ratio hi hKm hfin hconv hball hσ hcc1 hs).mono ?_
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using sqrt_pow_le_exp hcc1 (by norm_num : (0:ℝ) ≤ 2) hcc

/-- **Cousins–Vempala's own constant.**  At their schedule `σ²ᵢ₊₁ = (1 + 1/n)σ²ᵢ`
(`vol3_journal.tex:751-757`) the warmness constant is `√e`, exactly as their Lemma
"sigma-small-warmness" asserts. -/
theorem isWarm_coolLaw_succ_sqrt_exp {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (hi : i + 1 < m) (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hconv : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hσ : ∀ j, 0 < σsq j)
    (hs : σsq (i + 1) = (1 + 1 / (n : ℝ)) * σsq i) :
    IsWarm (ENNReal.ofReal (Real.exp (1 / 2))) (coolLaw m σsq K i)
      (coolLaw m σsq K (i + 1)) := by
  have hcc1 : (1 : ℝ) ≤ 1 + 1 / (n : ℝ) := by
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  refine (isWarm_coolLaw_succ_of_ratio hi hKm hfin hconv hball hσ hcc1 hs).mono ?_
  exact ENNReal.ofReal_le_ofReal
    (sqrt_pow_le_exp hcc1 (by norm_num : (0:ℝ) ≤ 1) le_rfl)

/-! ## The chain

Two statements, and the difference between them is the whole reason annealing works.

* `isWarm_coolLaw_chain` — **every consecutive pair** on a schedule with ratio `cc ≤ 1+2/n`
  is `e`-warm, with one and the same `e`.  This is the statement a per-phase mixing bound
  consumes: phase `i+1` starts its ball walk from a sample of phase `i`'s law, so the only
  warmness constant that ever enters a mixing time is the *consecutive* one.
* `isWarm_coolLaw_add` — the composite from phase `i` to phase `i+k` is `eᵏ`-warm.  This is
  **not** what the algorithm uses and it is **not** `O(1)`: warmness composes by
  multiplication (`Arlib.IsWarm.trans`), so it degrades geometrically along the schedule.
  Stating it makes the distinction unmissable. -/

/-- **The chain: the same `n`-free constant at every phase.**  On a geometric-ratio schedule
obeying `cc ≤ 1 + 2/n`, *every* consecutive pair of phase laws is `e`-warm.  The constant
does not depend on the phase index, so no phase pays more than `log e = 1` in its mixing
time. -/
theorem isWarm_coolLaw_chain {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)}
    (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤) (hconv : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hσ : ∀ j, 0 < σsq j)
    {cc : ℝ} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : ℝ))
    (hs : ∀ j, σsq (j + 1) = cc * σsq j) :
    ∀ i, i + 1 < m →
      IsWarm (ENNReal.ofReal (Real.exp 1)) (coolLaw m σsq K i) (coolLaw m σsq K (i + 1)) :=
  fun i hi => isWarm_coolLaw_succ_exp hi hKm hfin hconv hball hσ hcc1 hcc (hs i)

/-- **The composite along `k` phases is `eᵏ`-warm — and no better.**  Warmness multiplies
(`Arlib.IsWarm.trans`), so the phase-`i` law is `eᵏ`-warm for the phase-`(i+k)` law.

This is recorded to be explicit that warmness does **not** telescope to `O(1)` across the
whole schedule.  The algorithm never needs it to: each phase is re-seeded from the previous
phase's samples, so the constant that enters the per-phase mixing time is the consecutive
`e` of `isWarm_coolLaw_chain`, not `eᵏ`.  "What `M` the last phase sees" is `e`. -/
theorem isWarm_coolLaw_add {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)}
    (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤) (hconv : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hσ : ∀ j, 0 < σsq j)
    {cc : ℝ} (hcc1 : 1 ≤ cc) (hcc : cc ≤ 1 + 2 / (n : ℝ))
    (hs : ∀ j, σsq (j + 1) = cc * σsq j) (i : ℕ) :
    ∀ k : ℕ, i + k < m →
      IsWarm (ENNReal.ofReal (Real.exp 1) ^ k) (coolLaw m σsq K i)
        (coolLaw m σsq K (i + k)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : i + k < m := by omega
      have hstep := isWarm_coolLaw_chain hKm hfin hconv hball hσ hcc1 hcc hs (i + k) (by omega)
      have hcomp := (ih hk').trans hstep
      rw [← pow_succ] at hcomp
      rwa [← Nat.add_assoc]

/-! ## Routes that do not need convexity: a bounded body

The rescaling crux uses `λ⁻¹K ⊆ K`.  Two situations are not covered by it and are handled
here by a pointwise comparison on `K` instead, at the price of a circumradius hypothesis
`K ⊆ R·Bₙ`:

* the **terminal jump** from the last Gaussian phase to the *uniform* law on `K` — the
  terminal `coolWeight` is the constant `1`, not a Gaussian, so there is no rescaling;
* Cousins–Vempala's **accelerated** schedule (`vol3_journal.tex:760-766`), whose ratio is
  `1 + σᵢ²/(C²n)` rather than `1 + O(1/n)`.

Both come from the same one-line comparison of the two weights on `K`. -/

/-- If `wᵢ ≤ B·w_j` pointwise on `K`, the chain entries compare the same way. -/
theorem chain_le_mul_of_forall_le {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i j : ℕ}
    (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤) (hσi : 0 < σsq i) (hσj : 0 < σsq j)
    {B : ℝ} (h : ∀ x ∈ K, coolWeight m σsq i x ≤ B * coolWeight m σsq j x) :
    chain m σsq K i ≤ B * chain m σsq K j := by
  show (∫ x in K, coolWeight m σsq i x) ≤ B * ∫ x in K, coolWeight m σsq j x
  rw [← integral_const_mul]
  exact setIntegral_mono_on (integrableOn_coolWeight hσi hfin)
    ((integrableOn_coolWeight hσj hfin).const_mul B) hKm h

/-- **The terminal jump.**  The last Gaussian phase is `e^{R²/(2σ²ᵢ)}`-warm for the
*uniform* law on `K` (which is what `coolLaw m σsq K (i+1)` is once `m ≤ i+1`: the terminal
weight is the constant `1`).

No convexity is used — only `K ⊆ R·Bₙ`.  This is the phase the rescaling argument cannot
reach, and it is exactly the shape a hit-and-run warm-start hypothesis wants: warmness
against the uniform measure on the body, with an empty exceptional set. -/
theorem isWarm_coolLaw_terminal {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (hi : i < m) (him : m ≤ i + 1) (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hσ : ∀ j, 0 < σsq j)
    {R : ℝ} (hK : K ⊆ closedBall (0 : EuclSpace n) R) :
    IsWarm (ENNReal.ofReal (Real.exp (R ^ 2 / (2 * σsq i)))) (coolLaw m σsq K i)
      (coolLaw m σsq K (i + 1)) := by
  have hσi : 0 < σsq i := hσ i
  have hw : ∀ x : EuclSpace n, coolWeight m σsq i x ≤ coolWeight m σsq (i + 1) x := by
    intro x; rw [coolWeight_of_ge him]; exact coolWeight_le_one hσi x
  refine isWarm_coolLaw_of_le hfin hball hσ (Real.exp_pos _).le hw ?_
  refine chain_le_mul_of_forall_le hKm hfin (hσ (i + 1)) hσi fun x hx => ?_
  rw [coolWeight_of_ge him, coolWeight_of_lt hi, ← Real.exp_add]
  refine Real.one_le_exp ?_
  have heq : R ^ 2 / (2 * σsq i) + -(‖x‖ ^ 2) / (2 * σsq i)
      = (R ^ 2 - ‖x‖ ^ 2) / (2 * σsq i) := by ring
  rw [heq]
  have hxR : ‖x‖ ≤ R := by simpa using mem_closedBall_zero_iff.1 (hK hx)
  exact div_nonneg (by nlinarith [norm_nonneg x]) (by positivity)

/-- **The terminal jump, `n`-free.**  Once the last variance is at least `R²/2` — the
"the Gaussian is flat on the body" regime — the terminal phase is `e`-warm for the uniform
law on `K`. -/
theorem isWarm_coolLaw_terminal_exp {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (hi : i < m) (him : m ≤ i + 1) (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hσ : ∀ j, 0 < σsq j)
    {R : ℝ} (hK : K ⊆ closedBall (0 : EuclSpace n) R) (hflat : R ^ 2 ≤ 2 * σsq i) :
    IsWarm (ENNReal.ofReal (Real.exp 1)) (coolLaw m σsq K i) (coolLaw m σsq K (i + 1)) := by
  have hσi : 0 < σsq i := hσ i
  refine (isWarm_coolLaw_terminal hi him hKm hfin hball hσ hK).mono ?_
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  rw [div_le_one (by positivity)]
  exact hflat

/-- **The radius route** — Cousins–Vempala's Lemma "sigma-large" (`vol3_journal.tex:760-766`,
proof at `:803-830`).  With `K ⊆ R·Bₙ` and **no convexity assumption at all**, a variance
ratio of `cc` gives warmness `e^{R²(cc−1)/(2·cc·σ²ᵢ)}`.

Unlike the rescaling crux this bound degrades with the circumradius, which is why
Cousins–Vempala can only use it once the body is round (`R = C√n`) — but in exchange the
schedule may accelerate to `1 + σ²ᵢ/(C²n)`, far faster than `1 + O(1/n)`. -/
theorem isWarm_coolLaw_of_subset_ball {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (hi : i + 1 < m) (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hσ : ∀ j, 0 < σsq j)
    {R cc : ℝ} (hK : K ⊆ closedBall (0 : EuclSpace n) R) (hcc1 : 1 ≤ cc)
    (hs : σsq (i + 1) = cc * σsq i) :
    IsWarm (ENNReal.ofReal (Real.exp (R ^ 2 * (cc - 1) / (2 * cc * σsq i))))
      (coolLaw m σsq K i) (coolLaw m σsq K (i + 1)) := by
  have him : i < m := Nat.lt_of_succ_lt hi
  have hσi : 0 < σsq i := hσ i
  have hcc0 : (0 : ℝ) < cc := lt_of_lt_of_le one_pos hcc1
  have hmono : σsq i ≤ σsq (i + 1) := by rw [hs]; nlinarith
  refine isWarm_coolLaw_of_le hfin hball hσ (Real.exp_pos _).le
    (fun x => coolWeight_le_coolWeight him hi hσi hmono x) ?_
  refine chain_le_mul_of_forall_le hKm hfin (hσ (i + 1)) hσi fun x hx => ?_
  rw [coolWeight_of_lt hi, coolWeight_of_lt him, ← Real.exp_add, Real.exp_le_exp, hs,
    ← sub_nonneg]
  have hx2 : ‖x‖ ^ 2 ≤ R ^ 2 := by
    have hxR : ‖x‖ ≤ R := by simpa using mem_closedBall_zero_iff.1 (hK hx)
    nlinarith [norm_nonneg x]
  have key : R ^ 2 * (cc - 1) / (2 * cc * σsq i) + -(‖x‖ ^ 2) / (2 * σsq i)
      - -(‖x‖ ^ 2) / (2 * (cc * σsq i))
      = (cc - 1) * (R ^ 2 - ‖x‖ ^ 2) / (2 * cc * σsq i) := by
    field_simp
    ring
  rw [key]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)

/-- **The radius route, `n`-free.**  When the accelerated schedule respects
`R²·(cc − 1) ≤ cc·σ²ᵢ` — which is exactly Cousins–Vempala's `cc = 1 + σ²ᵢ/(C²n)` at
`R = C√n` — the warmness constant is `√e`, their stated value. -/
theorem isWarm_coolLaw_of_subset_ball_sqrt_exp {m : ℕ} {σsq : ℕ → ℝ}
    {K : Set (EuclSpace n)} {i : ℕ} (hi : i + 1 < m) (hKm : MeasurableSet K)
    (hfin : volume K ≠ ⊤) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hσ : ∀ j, 0 < σsq j)
    {R cc : ℝ} (hK : K ⊆ closedBall (0 : EuclSpace n) R) (hcc1 : 1 ≤ cc)
    (hs : σsq (i + 1) = cc * σsq i) (hrate : R ^ 2 * (cc - 1) ≤ cc * σsq i) :
    IsWarm (ENNReal.ofReal (Real.exp (1 / 2))) (coolLaw m σsq K i)
      (coolLaw m σsq K (i + 1)) := by
  have hσi : 0 < σsq i := hσ i
  have hcc0 : (0 : ℝ) < cc := lt_of_lt_of_le one_pos hcc1
  refine (isWarm_coolLaw_of_subset_ball hi hKm hfin hball hσ hK hcc1 hs).mono ?_
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
  linarith

/-! ## Non-vacuity (`CLAUDE.md` §11)

Every theorem above is an implication.  The witness below discharges all of its hypotheses
at once with concrete data — dimension `2`, the unit ball, the schedule `σ²ⱼ = 2ʲ` (whose
ratio `2` sits *exactly* at the boundary `1 + 2/n` for `n = 2`) — and exhibits both phase
laws as honest probability measures, so `IsWarm` is being asserted between two genuine
distributions and the constant `e < 3` is finite and explicit. -/

/-- `e < 3`: the warmness constant of this file is a concrete finite number. -/
theorem exp_one_lt_three : Real.exp 1 < 3 := by
  have := Real.exp_one_lt_d9
  linarith

/-- **Non-vacuity witness.**  In dimension `2`, on `K = B̄(0,1)`, with the two-phase
schedule `σ²₀ = 1`, `σ²₁ = 2` (ratio exactly `1 + 2/n`), both phase laws are probability
measures and the phase-`0` law is `e`-warm for the phase-`1` law.

Nothing here is a placeholder: the schedule ratio is at the extreme the binder allows, and
`e < 3` by `exp_one_lt_three`. -/
theorem exists_isWarm_coolLaw_succ :
    ∃ (K : Set (EuclSpace 2)) (σsq : ℕ → ℝ),
      MeasurableSet K ∧ Convex ℝ K ∧ ball (0 : EuclSpace 2) 1 ⊆ K ∧ volume K ≠ ⊤ ∧
        (∀ j, 0 < σsq j) ∧ σsq 0 = 1 ∧ σsq 1 = 2 ∧
        IsProbabilityMeasure (coolLaw 2 σsq K 0) ∧ IsProbabilityMeasure (coolLaw 2 σsq K 1) ∧
        IsWarm (ENNReal.ofReal (Real.exp 1)) (coolLaw 2 σsq K 0) (coolLaw 2 σsq K 1) := by
  have hpos : ∀ j : ℕ, 0 < geomSchedule 1 1 j := by
    intro j; simp only [geomSchedule]; positivity
  have hball : ball (0 : EuclSpace 2) 1 ⊆ closedBall (0 : EuclSpace 2) 1 :=
    ball_subset_closedBall
  have hfin : volume (closedBall (0 : EuclSpace 2) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  refine ⟨closedBall (0 : EuclSpace 2) 1, geomSchedule 1 1, measurableSet_closedBall,
    convex_closedBall _ _, hball, hfin, hpos, by norm_num [geomSchedule],
    by norm_num [geomSchedule],
    coolLaw_isProbabilityMeasure hpos hball hfin 0,
    coolLaw_isProbabilityMeasure hpos hball hfin 1, ?_⟩
  refine isWarm_coolLaw_succ_exp (by norm_num) measurableSet_closedBall hfin
    (convex_closedBall _ _) hball hpos (by norm_num : (1:ℝ) ≤ 2) (by norm_num) ?_
  norm_num [geomSchedule]

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms isWarm_withDensity_of_le
#print axioms measurable_coolDensity
#print axioms coolWeight_le_coolWeight
#print axioms chain_succ_le_pow_mul
#print axioms isWarm_coolLaw_of_le
#print axioms isWarm_coolLaw_succ
#print axioms sqrt_pow_le_exp
#print axioms isWarm_coolLaw_succ_of_ratio
#print axioms isWarm_coolLaw_succ_exp
#print axioms isWarm_coolLaw_succ_sqrt_exp
#print axioms isWarm_coolLaw_chain
#print axioms isWarm_coolLaw_add
#print axioms chain_le_mul_of_forall_le
#print axioms isWarm_coolLaw_terminal
#print axioms isWarm_coolLaw_terminal_exp
#print axioms isWarm_coolLaw_of_subset_ball
#print axioms isWarm_coolLaw_of_subset_ball_sqrt_exp
#print axioms exp_one_lt_three
#print axioms exists_isWarm_coolLaw_succ

end Arlib.GaussianCooling

