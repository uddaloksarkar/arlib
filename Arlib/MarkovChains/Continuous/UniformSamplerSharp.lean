/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.UniformSamplerUncond
import Arlib.MarkovChains.Continuous.SmoothSqrt
import Arlib.MarkovChains.Continuous.SpeedyConductanceSqrt

/-!
# The unconditional uniform sampler, sharpened — `n⁴` unconditionally, `n³` modulo `hcomp`

`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond`
(`UniformSamplerUncond.lean`) is unconditional and costs `O(n⁵·D²·log(1+D)/ρ²)` steps.  Its
docstring names three sources of loss against the literature's `O(n²D²)`.  Two of them have
since been closed upstream, independently; this file **composes them in** and states, with
`#print axioms` for every declaration, exactly what each one buys and what it does not.

## What is landed here

**1. The smoothness sharpening — a drop-in, and the result is unconditional.**
`Arlib.MarkovChains.isSmooth_sqrt_of_ball_subset` (`SmoothSqrt.lean:620`) certifies
`IsSmooth K δ (ofReal (4e²·δ√n))` under *exactly* the hypotheses already carried (`K` convex,
measurable, `B(0,1) ⊆ K`, `vol K ≠ ⊤`, plus the regime guard `δ√n ≤ 1`), where
`isSmooth_of_ball_subset` gave `1 − (1−δ)ⁿ ≈ nδ`.  Substituting it, the step size that buys
bias `ρ/2` moves from `δ = ρ/(4n)` to **`δ = ρ/(128√n)`**, and since the step count is `δ⁻²`
that is one whole factor `n`:

    φ_sharp = min(1/32, κ·(ρ/(128√n))/(256n)) = min(1/32, ρ/(262144·D·n^{3/2}))   at κ = 1/(8D)
    t       = (2n·log(1+D) + 2·log(2/ρ)) / φ_sharp²  + 1
            = O( n⁴ · D² · log(1+D) / ρ² ).

`mixesWithin_lazy_speedyWalk_uniformOn_sharp` is the honest final theorem at that count: no
isoperimetry binder, no warmness binder, no smoothness binder, **no comparability binder**.
`mixesWithin_lazy_speedyWalk_uniformOn_sharp_ballTwo` discharges every one of its hypotheses
on `K = B(0,2)`, `ρ = 1/2`, leaving only `2 ≤ n`.

**2. The conductance sharpening — a second factor `n`, but it carries a binder.**
`Arlib.MarkovChains.conductance_speedyWalk_sqrt_ge` (`SpeedyConductanceSqrt.lean:277`) gives
`Φ ≥ min(1/96, κ·ofReal(δ/√n)/384)` against the old `min(1/16, κ·ofReal(δ/(2n))/64)`, at the
price of

    hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x − y‖ ≤ δ/√n → ell K δ x ≤ ofReal (3/2) · ell K δ y.

Composed with the sharpened `δ`, and with `δ/√n = ρ/(128n)`:

    φ_cond = min(1/192, κ·(ρ/(128n))/768) = min(1/192, ρ/(786432·D·n))            at κ = 1/(8D)
    t      = O( n³ · D² · log(1+D) / ρ² ).

`mixesWithin_lazy_speedyWalk_uniformOn_sharp3` states exactly that, with **`hcomp` as the one
and only surviving mathematical binder** — warmness, smoothness and isoperimetry are all
discharged inside.  It is *not* an unconditional theorem and must not be quoted as one.

## The central question, answered: (c), and here is the machine-checked obstruction

Can `hcomp` be discharged?  The known route is the **good-points body**
`K_δ = K ∩ {ℓ_K ≥ 3/4}`, which is convex (`convex_goodPoints`, `SmoothSqrt.lean:107`) and
fills `K` up to `(1 − 16e²δ√n)` (`volume_goodPoints_ge`, `SmoothSqrt.lean:650`), and on which
the `3/4` floor *does* give comparability (`three_quarters_le_ell_comparable`,
`SpeedyConductanceSqrt.lean:163`).  The answer is **(c): that route does not close**, for two
independent reasons, both machine-checked below.

* **The certificate is about the wrong function.**  `three_quarters_le_ell_comparable` bounds
  `ell K δ`, but a walk living on `K_δ` is normalised by `ell K_δ δ`, and
  `ell_mono_body` / `ell_goodPoints_le_ell` prove `ell K_δ δ x ≤ ell K δ x` — the inequality
  runs the *wrong way* to transport a lower floor.  The `3/4` floor for `K` is no floor at all
  for `K_δ`, so `hcomp` for `speedyWalk K_δ δ` would need `(K_δ)_δ`, and so on.  This is the
  regress that `SpeedyWalk.lean:1296-1298` already records in prose ("restricting the walk to
  `K' = K ∩ SpeedyPoints K δ` only moves the problem"); here it is as a theorem.
* **Sampling `K_δ` is not sampling `K`, at any finite time.**
  `speedyWalk_apply_compl_eq_zero` → `lazy_speedyWalk_apply_compl_eq_zero` →
  `iterate_lazy_speedyWalk_compl_eq_zero`: a walk started inside `S` never charges `Sᶜ`, for
  **every** `t`.  Hence `le_of_mixesWithin_lazy_speedyWalk_confined`: any `MixesWithin` claim
  for `lazy (speedyWalk S δ)` against `uniformOn volume K` forces
  `1 − vol S / vol K ≤ r`.  `le_of_mixesWithin_goodPoints` instantiates it at `S = K_δ`, and
  `obstruction_ballOne_in_ballTwo` is a fully discharged instance (`S = B(0,1)`,
  `K = B(0,2)`: the error can never beat `1 − 2⁻ⁿ`).  This is an *`EllFloor`-style* negative:
  it is not a statement about the limit, it holds at every finite time.

**What this does not say.**  The volume gap is *bounded* by `16e²δ√n` (`volume_goodPoints_ge`),
so the second bullet is a quantitative price, not an infinity — an `s`-conductance argument
with `s = 16e²δ√n` is exactly the device that would pay it.  The obstruction that has no
price attached is the **first** bullet: the comparability certificate simply does not exist
for the body the walk would have to run on.

## What `s`-conductance machinery this repository actually has

* `Arlib.MarkovChains.MidSets`, `conductanceSOn`, `conductanceS`,
  `conductanceOn_le_conductanceSOn`, `conductance_le_conductanceS`, `le_conductanceS`
  (`HitAndRunMixing.lean:270-318`) — the definitions and the "an ordinary conductance bound is
  an `s`-conductance bound" direction.
* `Arlib.MarkovChains.lsThresholdS`, `mul_pow_le_of_lsThresholdS_le`,
  `tvLe_iterate_of_sConductance` (`HitAndRunMixing.lean:619`) — mixing from `s`-conductance,
  but it carries `hLSs`, the Lovász–Simonovits bound, as an **explicitly unproved binder**;
  the same file proves the usual formulation *false* on a measurable space with atoms.
* `Arlib.MarkovChains.SmallSets` and `mixesWithin_of_conductance_of_smallSets`
  (`ConductanceToTV.lean:336`) are **not** `s`-conductance: `SmallSets pi (1/2)` is the
  non-degeneracy condition "some measurable set has mass in `(0,1/2]`".

So route (b) — pay the volume gap with `s`-conductance — cannot yield an *unconditional*
theorem in this repository even if the first obstruction were removed: it would inherit
`hLSs`.  And it could not be assembled from outside `SpeedyConductanceSqrt.lean` in any case,
because `conductance_speedyWalk_sqrt_ge` consumes `hcomp` globally on `K` inside a single
proof.

## The machine-checked comparison against the `n⁵` bound

* `sqrtSharp_gain_eq` — the isoperimetric branch of `φ` is multiplied by **exactly `√n/32`**
  (an equality, not an estimate).
* `sqrtSharp_sq_gain_eq` — hence `1024·φ_sharp² = n·φ_uncond²` on that branch: the `φ⁻²` step
  count drops by exactly the factor `n/1024`.
* `phi_uncond_le_phi_sharp` — for `1024 ≤ n`, `φ_uncond ≤ φ_sharp` for the *whole* `min`.
* `steps_sharp_le_steps_uncond` — for `1024 ≤ n`, the closed-form step bound of
  `mixesWithin_lazy_speedyWalk_uniformOn_sharp_steps` is at most that of
  `mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps`.

The threshold `1024` is the crude absolute constant `4e²` of `isSmooth_sqrt_of_ball_subset`
(the book's is `2`); the *asymptotic* gain `n/1024` is unconditional in `n`.

## The third loss is untouched

The warm-start factor `log M = 2n·log(1+D)` from a single inscribed ball is loss source 3 of
`UniformSamplerUncond.lean` and nothing here touches it; that is why even the conditional
count is `n³` and not the book's `n²`.  See `WarmEllProb.lean` for why the exponential
constant is *necessary* for this `mu0`.

## Scope — read before quoting anything from this file

Every theorem here is a **Markov-chain mixing statement**: after `t` applications of the
kernel `lazy (speedyWalk K δ)`, the law of the walk is within total variation `ρ` of
`Arlib.uniformOn volume K`.  It is **not** a running-time claim about any algorithm — `t`
counts abstract kernel applications and nothing here bounds the cost of one step — and it is
not a statement about the TTC pipeline, volume computation or lattice counting.  `2 ≤ n` is
the scope limit of `Arlib.hiso_ellProb_of_ball_bound` and is not widened.

**No `def`, `structure`, `class`, `axiom` or named `Prop` is introduced in this file.**  Every
declaration is a `theorem` and every hypothesis is an inline binder.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## 0. Two numeric facts -/

/-- `e² < 8`. -/
theorem exp_two_lt_eight : Real.exp 2 < 8 := by
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  nlinarith

/-- **The smoothness bias in the `δ√n` regime**: for `0 ≤ c ≤ 1/2`,
`ofReal c / (1 − ofReal c) ≤ ofReal (2c)`. -/
theorem ofReal_div_one_sub_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) :
    ENNReal.ofReal c / (1 - ENNReal.ofReal c) ≤ ENNReal.ofReal (2 * c) := by
  have hpos : (0:ℝ) < 1 - c := by linarith
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal c = ENNReal.ofReal (1 - c) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hc0]
  rw [hsub, ENNReal.div_le_iff (by simpa using (ENNReal.ofReal_pos.2 hpos).ne')
    ENNReal.ofReal_ne_top, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

/-! ## 1. The composition at `δ = ρ/(128√n)` -/

/-- **The lazy speedy walk mixes to the uniform measure on `K`, with the `δ√n` smoothness
certificate.**

The analogue of `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_poly`
(`SpeedyUniformPoly.lean:261`) with `isSmooth_of_ball_subset` replaced by
`isSmooth_sqrt_of_ball_subset`.  At `δ = ρ/(128√n)` the smoothness parameter is
`s = 4e²·ρ/128 = e²ρ/32 < ρ/4`, so the bias `s/(1−s)` is at most `2s = e²ρ/16 ≤ ρ/2`
(`ofReal_div_one_sub_le` and `exp_two_lt_eight`), and the tolerance closes at `ρ/2 + ρ/2`.

The old route needed `δ = ρ/(4n)` for the same bias; that is the whole `√n`. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_sqrt (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (hbdd : Bornology.IsBounded K) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d
          * ellProb K (rho / (128 * Real.sqrt n)) A
          * ellProb K (rho / (128 * Real.sqrt n)) B
        ≤ ellProb K (rho / (128 * Real.sqrt n)) ((K \ A) \ B))
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellProb K (rho / (128 * Real.sqrt n)))) {t : ℕ}
    (ht : conductanceMixingTime M
        (min (1 / 32) (kappa * (rho / (128 * Real.sqrt n)) / (256 * (n : ℝ)))) (rho / 2) ≤ t) :
    MixesWithin (lazy (speedyWalk K (rho / (128 * Real.sqrt n))))
      (Arlib.uniformOn volume K) mu0 t (ENNReal.ofReal rho) := by
  haveI : NeZero n := ⟨by omega⟩
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hsq : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hδ : 0 < rho / (128 * Real.sqrt n) := by positivity
  have hδsq : rho / (128 * Real.sqrt n) * Real.sqrt n = rho / 128 := by
    field_simp
  have hK0 : volume K ≠ 0 := fun h => volume_unitBall_ne_zero (measure_mono_null hball h)
  have hKtop : volume K ≠ ⊤ := hbdd.measure_lt_top.ne
  have hsmooth : IsSmooth K (rho / (128 * Real.sqrt n))
      (ENNReal.ofReal (4 * Real.exp 2 * (rho / 128))) := by
    have h := isSmooth_sqrt_of_ball_subset hK hconv hball hKtop hδ
      (by rw [hδsq]; linarith)
    rwa [hδsq] at h
  have he8 := exp_two_lt_eight
  have he0 : (0:ℝ) < Real.exp 2 := Real.exp_pos 2
  have hc0 : (0:ℝ) ≤ 4 * Real.exp 2 * (rho / 128) := by positivity
  have hc : 4 * Real.exp 2 * (rho / 128) ≤ 1 / 2 := by nlinarith
  have hbias : ENNReal.ofReal (4 * Real.exp 2 * (rho / 128))
      / (1 - ENNReal.ofReal (4 * Real.exp 2 * (rho / 128)))
      ≤ ENNReal.ofReal (rho / 2) := by
    refine (ofReal_div_one_sub_le hc0 hc).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith
  have h := mixesWithin_lazy_speedyWalk_uniformOn hn hK hconv hK0 hKtop hδ hkappa hiso
    hsmooth hM hwarm (by linarith : (0:ℝ) < rho / 2) ht
  refine h.mono_err ?_
  calc ENNReal.ofReal (rho / 2) + ENNReal.ofReal (4 * Real.exp 2 * (rho / 128))
        / (1 - ENNReal.ofReal (4 * Real.exp 2 * (rho / 128)))
      ≤ ENNReal.ofReal (rho / 2) + ENNReal.ofReal (rho / 2) := by gcongr
    _ = ENNReal.ofReal rho := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        norm_num

/-! ## 2. The warm start discharged, `κ` still symbolic -/

/-- **The sharpened walk from the samplable start**, with `hwarm` and `hsmooth` discharged and
`κ` still symbolic — the statement a better isoperimetric coefficient slots into.  The
warm-start constant is `M = (1+D)^(2n)`, exactly as in
`mixesWithin_lazy_speedyWalk_uniformOn_unitBallStart`; the sharpening does not touch it. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_sqrt_unitBallStart (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d
          * ellProb K (rho / (128 * Real.sqrt n)) A
          * ellProb K (rho / (128 * Real.sqrt n)) B
        ≤ ellProb K (rho / (128 * Real.sqrt n)) ((K \ A) \ B))
    {t : ℕ}
    (ht : conductanceMixingTime ((1 + D) ^ (2 * n))
        (min (1 / 32) (kappa * (rho / (128 * Real.sqrt n)) / (256 * (n : ℝ)))) (rho / 2) ≤ t) :
    MixesWithin (lazy (speedyWalk K (rho / (128 * Real.sqrt n))))
      (Arlib.uniformOn volume K)
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      t (ENNReal.ofReal rho) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt hn1
    rwa [Real.sqrt_one] at h
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (Metric.mem_ball_self one_pos)
  have hD0 : (0 : ℝ) ≤ D := by simpa using hD 0 h0K 0 h0K
  have hKR : ∀ x ∈ K, ‖x‖ ≤ D := by
    intro x hx
    simpa using hD x hx 0 h0K
  have hsubcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) D := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hKR x hx
  have hbdd : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hsubcb
  have hδ : 0 < rho / (128 * Real.sqrt n) := by positivity
  have hδ1 : rho / (128 * Real.sqrt n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hMeq : (1 + D) ^ n * (1 + D) ^ n = (1 + D) ^ (2 * n) := by
    rw [two_mul, pow_add]
  have hcpow : (1 : ℝ) ≤ (1 + D) ^ n := one_le_pow₀ (by linarith)
  have hM : (1 : ℝ) ≤ (1 + D) ^ (2 * n) := by
    rw [← hMeq]; exact one_le_warmConst hD0 hcpow n
  have hwarm : IsWarm (ENNReal.ofReal ((1 + D) ^ (2 * n)))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (ellProb K (rho / (128 * Real.sqrt n))) := by
    rw [← hMeq]
    exact isWarm_uniformOn_unitBall_ellProb hconv hball hD hcpow
      (volume_le_one_add_pow_mul_volume_unitBall hD0 hKR) hδ hδ1
  haveI : IsProbabilityMeasure
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    Arlib.isProbabilityMeasure_uniformOn volume volume_unitBall_ne_zero volume_unitBall_ne_top
  exact mixesWithin_lazy_speedyWalk_uniformOn_sqrt hn hK hconv hball hbdd hrho hrho1 hkappa
    hiso hM hwarm ht

/-! ## 3. The honest final theorem, sharpened -/

/-- **Unconditional uniform sampling on a convex body, at `O(n⁴·D²·log(1+D)/ρ²)` steps.**

Let `2 ≤ n`, let `K ⊆ ℝⁿ` be measurable and convex with `B(0,1) ⊆ K` and all pairwise
distances at most `D`, and let `0 < ρ ≤ 1`.  Then from the **samplable** start
`Arlib.uniformOn volume (Metric.ball 0 1)`, after

    t ≥ conductanceMixingTime ((1+D)^(2n))
          (min (1/32) ((1/(8D))·(ρ/(128√n))/(256n))) (ρ/2)

steps the law of the lazy speedy walk at step size `δ = ρ/(128√n)` is within total variation
`ρ` of `Arlib.uniformOn volume K`.  Unfolding,

    φ = min(1/32, ρ/(262144·D·n^{3/2})),   log M = 2n·log(1+D),
    t = O( n⁴ · D² · log(1+D) / ρ² ),

one whole factor `n` better than `mixesWithin_lazy_speedyWalk_uniformOn_uncond`, and the
comparison is machine-checked (`sqrtSharp_sq_gain_eq`, `steps_sharp_le_steps_uncond`).

**Every binder is geometry of `K` or a numeric side condition.**  No isoperimetry
(`Arlib.hiso_ellProb_of_ball_bound` at `κ = 1/(8D)`), no warmness
(`isWarm_uniformOn_unitBall_ellProb` at `M = (1+D)^(2n)`), no smoothness
(`isSmooth_sqrt_of_ball_subset` at `s = 4e²·ρ/128`), and — unlike
`mixesWithin_lazy_speedyWalk_uniformOn_sharp3` — **no comparability binder**.

**Scope.**  A mixing statement about a Markov kernel, not a running-time claim.  See the
module docstring. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_sharp (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) {t : ℕ}
    (ht : conductanceMixingTime ((1 + D) ^ (2 * n))
        (min (1 / 32)
          (1 / (8 * D) * (rho / (128 * Real.sqrt n)) / (256 * (n : ℝ)))) (rho / 2) ≤ t) :
    MixesWithin (lazy (speedyWalk K (rho / (128 * Real.sqrt n))))
      (Arlib.uniformOn volume K)
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      t (ENNReal.ofReal rho) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hD2 : (1 : ℝ) / 2 ≤ D := half_le_diam_bound_of_ball_subset hn1 hball hD
  have hD0 : (0 : ℝ) < D := by linarith
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (Metric.mem_ball_self one_pos)
  have hKR : ∀ x ∈ K, ‖x‖ ≤ D := by
    intro x hx
    simpa using hD x hx 0 h0K
  have hK0 : volume K ≠ 0 := fun h => volume_unitBall_ne_zero (measure_mono_null hball h)
  have hδ : 0 < rho / (128 * Real.sqrt n) := by
    have : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
    positivity
  exact mixesWithin_lazy_speedyWalk_uniformOn_sqrt_unitBallStart hn1 hK hconv hball hD hrho
    hrho1 (by positivity)
    (Arlib.hiso_ellProb_of_ball_bound hn hD0 hδ hK hconv hKR hK0) ht

/-! ## 4. The step count in closed form -/

/-- **The sharpened sampler with the step count written out.**

Same statement as `mixesWithin_lazy_speedyWalk_uniformOn_sharp`, with `conductanceMixingTime`
replaced by the explicit sufficient count

    t ≥ (2n·log(1+D) + 2·log(2/ρ)) / min(1/32, (1/(8D))·(ρ/(128√n))/(256n))² + 1,

i.e. `O(n⁴·D²·log(1+D)/ρ²)`.  `steps_sharp_le_steps_uncond` compares this expression, term for
term, with the `n⁵` one of `mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps`. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_sharp_steps (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) {t : ℕ}
    (ht : (2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho))
          / (min (1 / 32)
              (1 / (8 * D) * (rho / (128 * Real.sqrt n)) / (256 * (n : ℝ)))) ^ 2 + 1
        ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyWalk K (rho / (128 * Real.sqrt n))))
      (Arlib.uniformOn volume K)
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      t (ENNReal.ofReal rho) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hsqp : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hD2 : (1 : ℝ) / 2 ≤ D := half_le_diam_bound_of_ball_subset hn1 hball hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hM : (1 : ℝ) ≤ (1 + D) ^ (2 * n) := one_le_pow₀ (by linarith)
  have hphi0 : 0 < min (1 / 32)
      (1 / (8 * D) * (rho / (128 * Real.sqrt n)) / (256 * (n : ℝ))) := by
    refine lt_min (by norm_num) ?_
    positivity
  have heps : (0 : ℝ) < rho / 2 := by linarith
  have hsqrt : rho / 2 ≤ Real.sqrt ((1 + D) ^ (2 * n)) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt ((1 + D) ^ (2 * n)) := by
      have h2 := Real.sqrt_le_sqrt hM
      rwa [Real.sqrt_one] at h2
    linarith
  have hlogM : Real.log ((1 + D) ^ (2 * n)) = 2 * (n : ℝ) * Real.log (1 + D) := by
    rw [Real.log_pow]
    push_cast
    ring
  have hlogeps : Real.log (1 / (rho / 2)) = Real.log (2 / rho) := by
    rw [one_div_div]
  refine mixesWithin_lazy_speedyWalk_uniformOn_sharp hn hK hconv hball hD hrho hrho1 ?_
  have hle := conductanceMixingTime_le (M := (1 + D) ^ (2 * n))
    (phi := min (1 / 32) (1 / (8 * D) * (rho / (128 * Real.sqrt n)) / (256 * (n : ℝ))))
    (eps := rho / 2) hM hphi0 heps hsqrt
  rw [hlogM, hlogeps] at hle
  exact_mod_cast hle.trans ht

/-! ## 5. Non-vacuity witness -/

/-- **The non-vacuity witness for the sharpened sampler** (`CLAUDE.md` §11).

`K = B(0,2)`, `ρ = 1/2`, `t` the concrete step count.  Every hypothesis of
`mixesWithin_lazy_speedyWalk_uniformOn_sharp` is discharged:

| binder | discharged by |
| --- | --- |
| `hK : MeasurableSet K` | `measurableSet_ball` |
| `hconv : Convex ℝ K` | `convex_ball` |
| `hball : B(0,1) ⊆ K` | `Metric.ball_subset_ball` |
| `hD : diam K ≤ 4` | `dist_le_four_of_mem_ballTwo` |
| `hrho, hrho1` | `norm_num` at `ρ = 1/2` |
| `ht` | `le_rfl` — `t` *is* the step count |
| `hiso` | `Arlib.hiso_ellProb_of_ball_bound` (inside `..._sharp`) |
| `hwarm` | `isWarm_uniformOn_unitBall_ellProb` (inside `..._sqrt_unitBallStart`) |
| `hsmooth` | `isSmooth_sqrt_of_ball_subset` (inside `..._sqrt`) |

**The only surviving hypothesis is `hn : 2 ≤ n`**, the scope limit of
`Arlib.hiso_ellProb_of_ball_bound`.  The body is `B(0,2)` rather than `B(0,1)` so that the
start law is genuinely different from the target, and `ρ = 1/2` is a non-trivial tolerance. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_sharp_ballTwo (hn : 2 ≤ n) :
    MixesWithin
      (lazy (speedyWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
        ((1 / 2 : ℝ) / (128 * Real.sqrt n))))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (conductanceMixingTime ((1 + 4 : ℝ) ^ (2 * n))
        (min (1 / 32)
          (1 / (8 * 4) * ((1 / 2 : ℝ) / (128 * Real.sqrt n)) / (256 * (n : ℝ))))
        ((1 / 2 : ℝ) / 2))
      (ENNReal.ofReal (1 / 2)) :=
  mixesWithin_lazy_speedyWalk_uniformOn_sharp hn measurableSet_ball (convex_ball _ _)
    (Metric.ball_subset_ball (by norm_num)) dist_le_four_of_mem_ballTwo (by norm_num)
    (by norm_num) le_rfl

/-! ## 6. The machine-checked comparison with the `n⁵` bound -/

/-- **The gain in the isoperimetric branch of `φ` is exactly `√n/32`** — an equality, not an
estimate.  `δ` moved from `ρ/(4n)` to `ρ/(128√n)`, and `(4n)/(128√n) = √n/32`. -/
theorem sqrtSharp_gain_eq (hn : 1 ≤ n) (rho kappa : ℝ) :
    kappa * (rho / (128 * Real.sqrt n)) / (256 * (n : ℝ))
      = Real.sqrt n / 32 * (kappa * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))) := by
  have hn0 : (0:ℝ) < (n : ℝ) := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  set s : ℝ := Real.sqrt ((n : ℝ)) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hn0
  have hss : s * s = (n : ℝ) := by rw [hsdef]; exact Real.mul_self_sqrt hn0.le
  rw [← hss]
  field_simp
  ring

/-- **The step-count gain in the isoperimetric branch is exactly `n/1024`**: since the count
is `φ⁻²`, `1024·φ_sharp² = n·φ_uncond²`.  This is the `n⁵ → n⁴` claim, machine-checked as an
identity between the two `φ`s the two files actually carry. -/
theorem sqrtSharp_sq_gain_eq (hn : 1 ≤ n) (rho kappa : ℝ) :
    1024 * (kappa * (rho / (128 * Real.sqrt n)) / (256 * (n : ℝ))) ^ 2
      = (n : ℝ) * (kappa * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))) ^ 2 := by
  have hn0 : (0:ℝ) < (n : ℝ) := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hss : Real.sqrt ((n:ℝ)) * Real.sqrt ((n:ℝ)) = (n : ℝ) := Real.mul_self_sqrt hn0.le
  rw [sqrtSharp_gain_eq hn rho kappa]
  nlinarith [hss, sq_nonneg (kappa * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))]

/-- **The sharpened conductance dominates the old one from dimension `1024` on**, for the
whole `min` and not just the isoperimetric branch.  `1024` is where `√n ≥ 32` — it is the
crude absolute constant `4e²` of `isSmooth_sqrt_of_ball_subset` (the book's is `2`), not a
feature of the mathematics; the asymptotic gain `n/1024` of `sqrtSharp_sq_gain_eq` holds for
every `n ≥ 1`. -/
theorem phi_uncond_le_phi_sharp (hn : 1024 ≤ n) {rho kappa : ℝ} (hrho : 0 ≤ rho)
    (hkappa : 0 ≤ kappa) :
    min (1 / 32) (kappa * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))
      ≤ min (1 / 32) (kappa * (rho / (128 * Real.sqrt n)) / (256 * (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1024:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs32 : (32:ℝ) ≤ Real.sqrt ((n:ℝ)) := by
    have h1 : Real.sqrt (1024:ℝ) ≤ Real.sqrt ((n:ℝ)) := Real.sqrt_le_sqrt hnR
    have h2 : Real.sqrt (1024:ℝ) = 32 := by
      rw [show (1024:ℝ) = 32 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rwa [h2] at h1
  have hold0 : 0 ≤ kappa * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)) := by
    have : (0:ℝ) < (n:ℝ) := by linarith
    positivity
  refine min_le_min le_rfl ?_
  rw [sqrtSharp_gain_eq hn1 rho kappa]
  nlinarith

/-- **The step-count bound of the sharpened sampler is at most that of the `n⁵` one.**

The closed-form count of `mixesWithin_lazy_speedyWalk_uniformOn_sharp_steps` is bounded by
that of `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps`, at the same
`n`, `D`, `ρ`, for `n ≥ 1024`.  Both numerators are literally the same expression
`2n·log(1+D) + 2·log(2/ρ)` — the warm start is untouched by either sharpening — so the whole
comparison is `φ_uncond ≤ φ_sharp`. -/
theorem steps_sharp_le_steps_uncond (hn : 1024 ≤ n) {D rho : ℝ} (hD : (1:ℝ)/2 ≤ D)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    (2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho))
        / (min (1 / 32)
            (1 / (8 * D) * (rho / (128 * Real.sqrt n)) / (256 * (n : ℝ)))) ^ 2 + 1
      ≤ (2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho))
        / (min (1 / 32) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2 + 1 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1024:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hD0 : (0:ℝ) < D := by linarith
  have hLlog : 0 ≤ Real.log (1 + D) := Real.log_nonneg (by linarith)
  have hLeps : 0 ≤ Real.log (2 / rho) := Real.log_nonneg (by
    rw [le_div_iff₀ hrho]; linarith)
  have hL : 0 ≤ 2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho) := by
    have : (0:ℝ) ≤ (n:ℝ) := by linarith
    positivity
  have hold0 : 0 < min (1 / 32) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))) := by
    refine lt_min (by norm_num) ?_
    have : (0:ℝ) < (n:ℝ) := by linarith
    positivity
  have hle := phi_uncond_le_phi_sharp hn (rho := rho) (kappa := 1 / (8 * D)) hrho.le
    (by positivity)
  have hsq : (min (1 / 32) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2
      ≤ (min (1 / 32)
          (1 / (8 * D) * (rho / (128 * Real.sqrt n)) / (256 * (n : ℝ)))) ^ 2 := by
    nlinarith [hold0]
  gcongr

/-! ## 7. The conductance half, with `hcomp` carried -/

/-- **The lazy speedy walk mixes to `ellProb K δ` at the `δ/√n` conductance.**

`conductance_speedyWalk_sqrt_ge` + `conductance_lazy` + `mixesWithin_of_conductance`, at

    φ = min(1/192, κ·(δ/√n)/768),

which is `conductance_speedyWalk_sqrt_ge`'s `min(1/96, κ·(δ/√n)/384)` halved by laziness
(`conductance_lazy` is an equality, so nothing is lost beyond the exact factor `2`).

This is the analogue of `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk` (`SpeedyWalk.lean:1206`),
which gets `min(1/32, κδ/(256n))` with no `hcomp`.  Reversibility, nonneg spectrum and the
`SmallSets` non-degeneracy are discharged exactly as there. -/
theorem mixesWithin_lazy_speedyWalk_sqrtCond (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ)
    (hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ / Real.sqrt n →
      ell K δ x ≤ ENNReal.ofReal (3 / 2) * ell K δ y)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d * ellProb K δ A * ellProb K δ B
        ≤ ellProb K δ ((K \ A) \ B))
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellProb K δ))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M
      (min (1 / 192) (kappa * (δ / Real.sqrt n) / 768)) eps ≤ t) :
    MixesWithin (lazy (speedyWalk K δ)) (ellProb K δ) mu0 t (ENNReal.ofReal eps) := by
  haveI : IsProbabilityMeasure (ellProb K δ) :=
    isProbabilityMeasure_ellProb_of_volume hK hK0 hKtop hδ
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hsq : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hrev : IsReversible (lazy (speedyWalk K δ)) (ellProb K δ) :=
    isReversible_lazy (isReversible_speedyWalk_prob hK δ)
  have hpsd : HasNonnegSpectrum (lazy (speedyWalk K δ)) (ellProb K δ) :=
    hasNonnegSpectrum_lazy (isReversible_speedyWalk_prob hK δ)
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ :=
    exists_smallSet_of_absolutelyContinuous hn1 (ellProb K δ) (ellProb_absolutelyContinuous K δ)
  have hne := rayleighSet_nonempty_of_smallSet (lazy (speedyWalk K δ)) hS0m hS0pos hS0half
  set phi : ℝ := min (1 / 192) (kappa * (δ / Real.sqrt n) / 768) with hphidef
  have hphi0 : 0 < phi := lt_min (by norm_num) (by positivity)
  have hphi1 : phi ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have hcond := conductance_speedyWalk_sqrt_ge hn hK hconv hK0 hKtop hδ hcomp
    (kappa := ENNReal.ofReal kappa) hiso
  have hmul : ENNReal.ofReal phi * 2 = ENNReal.ofReal (phi * 2) := by
    rw [ENNReal.ofReal_mul hphi0.le]
    norm_num
  have hbranch1 : ENNReal.ofReal phi * 2 ≤ (1 : ℝ≥0∞) / 96 := by
    have h96 : ((1:ℝ≥0∞) / 96) = ENNReal.ofReal ((1:ℝ) / 96) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 96)]
      norm_num
    rw [h96, hmul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmin := min_le_left (1 / 192 : ℝ) (kappa * (δ / Real.sqrt n) / 768)
    rw [← hphidef] at hmin
    linarith
  have hbranch2 : ENNReal.ofReal phi * 2
      ≤ ENNReal.ofReal kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384 := by
    have hrhs : ENNReal.ofReal kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384
        = ENNReal.ofReal (kappa * (δ / Real.sqrt n) / 384) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 384),
        ENNReal.ofReal_mul hkappa.le]
      norm_num
    rw [hrhs, hmul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmin := min_le_right (1 / 192 : ℝ) (kappa * (δ / Real.sqrt n) / 768)
    rw [← hphidef] at hmin
    linarith
  have hlazy : ENNReal.ofReal phi
      ≤ conductance (lazy (speedyWalk K δ)) (ellProb K δ) := by
    rw [conductance_lazy]
    have hstep : ENNReal.ofReal phi
        ≤ min ((1:ℝ≥0∞) / 96)
            (ENNReal.ofReal kappa * ENNReal.ofReal (δ / Real.sqrt n) / 384) / 2 := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      exact le_min hbranch1 hbranch2
    exact hstep.trans (by gcongr)
  have hcondtop : conductance (lazy (speedyWalk K δ)) (ellProb K δ) ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num)
      (conductance_le_one _ _ ⟨S0, hS0m, hS0pos, hS0half⟩)
  have hphireal : phi ≤ (conductance (lazy (speedyWalk K δ)) (ellProb K δ)).toReal := by
    have h := ENNReal.toReal_mono hcondtop hlazy
    rwa [ENNReal.toReal_ofReal hphi0.le] at h
  exact mixesWithin_of_conductance hrev hpsd hne hM hwarm hphi0 hphi1 heps hphireal ht

/-- **Both sharpenings composed**: the `δ√n` smoothness fixes `δ = ρ/(128√n)` and the `δ/√n`
conductance then reads `φ = min(1/192, κ·(ρ/(128n))/768)`.  `κ` and the warm-start constant
`M` are still symbolic; `hcomp` is carried. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_sqrtCond (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (hbdd : Bornology.IsBounded K) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ rho / (128 * (n : ℝ)) →
      ell K (rho / (128 * Real.sqrt n)) x
        ≤ ENNReal.ofReal (3 / 2) * ell K (rho / (128 * Real.sqrt n)) y)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d
          * ellProb K (rho / (128 * Real.sqrt n)) A
          * ellProb K (rho / (128 * Real.sqrt n)) B
        ≤ ellProb K (rho / (128 * Real.sqrt n)) ((K \ A) \ B))
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellProb K (rho / (128 * Real.sqrt n)))) {t : ℕ}
    (ht : conductanceMixingTime M
        (min (1 / 192) (kappa * (rho / (128 * (n : ℝ))) / 768)) (rho / 2) ≤ t) :
    MixesWithin (lazy (speedyWalk K (rho / (128 * Real.sqrt n))))
      (Arlib.uniformOn volume K) mu0 t (ENNReal.ofReal rho) := by
  haveI : NeZero n := ⟨by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hsq : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hδ : 0 < rho / (128 * Real.sqrt n) := by positivity
  have hδsq : rho / (128 * Real.sqrt n) * Real.sqrt n = rho / 128 := by
    field_simp
  have hdiv : rho / (128 * Real.sqrt n) / Real.sqrt n = rho / (128 * (n : ℝ)) := by
    rw [div_div, mul_assoc, Real.mul_self_sqrt hnR.le]
  have hK0 : volume K ≠ 0 := fun h => volume_unitBall_ne_zero (measure_mono_null hball h)
  have hKtop : volume K ≠ ⊤ := hbdd.measure_lt_top.ne
  have hcomp' : ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ ≤ rho / (128 * Real.sqrt n) / Real.sqrt n →
      ell K (rho / (128 * Real.sqrt n)) x
        ≤ ENNReal.ofReal (3 / 2) * ell K (rho / (128 * Real.sqrt n)) y := by
    rw [hdiv]
    exact hcomp
  have hsmooth : IsSmooth K (rho / (128 * Real.sqrt n))
      (ENNReal.ofReal (4 * Real.exp 2 * (rho / 128))) := by
    have h := isSmooth_sqrt_of_ball_subset hK hconv hball hKtop hδ
      (by rw [hδsq]; linarith)
    rwa [hδsq] at h
  have he8 := exp_two_lt_eight
  have he0 : (0:ℝ) < Real.exp 2 := Real.exp_pos 2
  have hc0 : (0:ℝ) ≤ 4 * Real.exp 2 * (rho / 128) := by positivity
  have hc : 4 * Real.exp 2 * (rho / 128) ≤ 1 / 2 := by nlinarith
  have hbias : ENNReal.ofReal (4 * Real.exp 2 * (rho / 128))
      / (1 - ENNReal.ofReal (4 * Real.exp 2 * (rho / 128)))
      ≤ ENNReal.ofReal (rho / 2) := by
    refine (ofReal_div_one_sub_le hc0 hc).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith
  have hmix := mixesWithin_lazy_speedyWalk_sqrtCond (t := t) hn hK hconv hK0 hKtop hδ hcomp'
    hkappa hiso hM hwarm (by linarith : (0:ℝ) < rho / 2) (by rw [hdiv]; exact ht)
  have h := TVLe.trans hmix (tvLe_ellProb_uniformOn hK hK0 hKtop hδ hsmooth)
  refine MixesWithin.mono_err h ?_
  calc ENNReal.ofReal (rho / 2) + ENNReal.ofReal (4 * Real.exp 2 * (rho / 128))
        / (1 - ENNReal.ofReal (4 * Real.exp 2 * (rho / 128)))
      ≤ ENNReal.ofReal (rho / 2) + ENNReal.ofReal (rho / 2) := by gcongr
    _ = ENNReal.ofReal rho := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        norm_num

/-- **The `O(n³)` sampler: warmness, smoothness and isoperimetry all discharged, `hcomp` the
single surviving mathematical binder.**

Same geometry as `mixesWithin_lazy_speedyWalk_uniformOn_sharp`, same step size
`δ = ρ/(128√n)`, same start, same tolerance — but the conductance comes from
`conductance_speedyWalk_sqrt_ge` instead of `conductance_speedyWalk_ge`, so

    φ = min(1/192, (1/(8D))·(ρ/(128n))/768) = min(1/192, ρ/(786432·D·n)),
    t = O( n³ · D² · log(1+D) / ρ² ).

**`hcomp` is a genuine hypothesis and this is not an unconditional theorem.**  It is
required only at separation `δ/√n = ρ/(128n)` — a *shorter* distance than the step `δ`
itself — but it is not automatic, and §8 below shows that the good-points device does not
supply it: `ell_goodPoints_le_ell` says the `3/4` floor for `ell K` is not a floor for
`ell K_δ`, and `le_of_mixesWithin_goodPoints` says a walk confined to `K_δ` samples the wrong
body at every finite time.  So the `n³` here is *conditionally reachable*, and the honest
unconditional headline of this file remains
`mixesWithin_lazy_speedyWalk_uniformOn_sharp` at `n⁴`. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_sharp3 (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ rho / (128 * (n : ℝ)) →
      ell K (rho / (128 * Real.sqrt n)) x
        ≤ ENNReal.ofReal (3 / 2) * ell K (rho / (128 * Real.sqrt n)) y)
    {t : ℕ}
    (ht : conductanceMixingTime ((1 + D) ^ (2 * n))
        (min (1 / 192) (1 / (8 * D) * (rho / (128 * (n : ℝ))) / 768)) (rho / 2) ≤ t) :
    MixesWithin (lazy (speedyWalk K (rho / (128 * Real.sqrt n))))
      (Arlib.uniformOn volume K)
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      t (ENNReal.ofReal rho) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnR1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hsq : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt hnR1
    rwa [Real.sqrt_one] at h
  have hD2 : (1 : ℝ) / 2 ≤ D := half_le_diam_bound_of_ball_subset hn1 hball hD
  have hD0 : (0 : ℝ) < D := by linarith
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (Metric.mem_ball_self one_pos)
  have hD0' : (0 : ℝ) ≤ D := hD0.le
  have hKR : ∀ x ∈ K, ‖x‖ ≤ D := by
    intro x hx
    simpa using hD x hx 0 h0K
  have hsubcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) D := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hKR x hx
  have hbdd : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hsubcb
  have hK0 : volume K ≠ 0 := fun h => volume_unitBall_ne_zero (measure_mono_null hball h)
  have hδ : 0 < rho / (128 * Real.sqrt n) := by positivity
  have hδ1 : rho / (128 * Real.sqrt n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hMeq : (1 + D) ^ n * (1 + D) ^ n = (1 + D) ^ (2 * n) := by
    rw [two_mul, pow_add]
  have hcpow : (1 : ℝ) ≤ (1 + D) ^ n := one_le_pow₀ (by linarith)
  have hM : (1 : ℝ) ≤ (1 + D) ^ (2 * n) := by
    rw [← hMeq]; exact one_le_warmConst hD0' hcpow n
  have hwarm : IsWarm (ENNReal.ofReal ((1 + D) ^ (2 * n)))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (ellProb K (rho / (128 * Real.sqrt n))) := by
    rw [← hMeq]
    exact isWarm_uniformOn_unitBall_ellProb hconv hball hD hcpow
      (volume_le_one_add_pow_mul_volume_unitBall hD0' hKR) hδ hδ1
  haveI : IsProbabilityMeasure
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    Arlib.isProbabilityMeasure_uniformOn volume volume_unitBall_ne_zero volume_unitBall_ne_top
  exact mixesWithin_lazy_speedyWalk_uniformOn_sqrtCond hn hK hconv hball hbdd hrho hrho1 hcomp
    (by positivity) (Arlib.hiso_ellProb_of_ball_bound hn hD0 hδ hK hconv hKR hK0) hM hwarm ht

/-! ## 8. The obstruction: why `hcomp` is not discharged by the good-points body -/

/-- **`ell` is monotone in the body**: shrinking `K` can only shrink the local conductance,
because the numerator `vol(B(x,δ) ∩ ·)` does and the denominator does not depend on the body
at all. -/
theorem ell_mono_body {A B : Set (EuclideanSpace ℝ (Fin n))} (hAB : A ⊆ B) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ell A δ x ≤ ell B δ x := by
  rw [ell_apply, ell_apply]
  exact ENNReal.div_le_div_right (measure_mono (Set.inter_subset_inter_right _ hAB)) _

/-- **The good-points certificate does not transfer to the good-points body.**

`three_quarters_le_ell_comparable` (`SpeedyConductanceSqrt.lean:163`) discharges `hcomp` from
a *lower* bound `ell K δ ≥ 3/4`.  A walk that lives on `K_δ = K ∩ {ℓ_K ≥ 3/4}` is normalised
by `ell K_δ δ`, and this lemma says `ell K_δ δ ≤ ell K δ` — the inequality runs the wrong way,
so the certificate for `K` gives **no** lower bound for `K_δ`.  Discharging `hcomp` on the
body the walk actually runs on would need the good-points body of `K_δ`, and so on without
end.

This is the formal content of the prose remark at `SpeedyWalk.lean:1296-1298`. -/
theorem ell_goodPoints_le_ell (K : Set (EuclideanSpace ℝ (Fin n))) (δ c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ell (K ∩ {y : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal c ≤ ell K δ y}) δ x
      ≤ ell K δ x :=
  ell_mono_body Set.inter_subset_left δ x

/-- **The speedy walk on `S` never leaves `S`.**  From `x ∈ S` the accepted part of the
proposal is `B(x,δ) ∩ S ⊆ S`, and the holding atom sits at `x ∈ S`; so `Sᶜ` gets mass `0`. -/
theorem speedyWalk_apply_compl_eq_zero {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) (δ : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) :
    speedyWalk S δ x Sᶜ = 0 := by
  have hempty : Sᶜ ∩ (Metric.ball x δ ∩ S) = ∅ := by
    refine Set.subset_empty_iff.1 ?_
    rintro z ⟨hz1, -, hz3⟩
    exact absurd hz3 hz1
  rw [speedyWalk_apply_set hS δ x hS.compl, hempty, measure_empty]
  simp [hx]

/-- The same for the lazy chain. -/
theorem lazy_speedyWalk_apply_compl_eq_zero {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) (δ : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) :
    lazy (speedyWalk S δ) x Sᶜ = 0 := by
  rw [lazy_apply_set _ _ hS.compl, speedyWalk_apply_compl_eq_zero hS δ hx]
  simp [hx]

/-- **The law of the walk confined to `S` charges no set outside `S`, at any time.** -/
theorem iterate_lazy_speedyWalk_compl_eq_zero {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) (δ : ℝ) {mu0 : Measure (EuclideanSpace ℝ (Fin n))}
    (hmu : mu0 Sᶜ = 0) (t : ℕ) :
    iterate (lazy (speedyWalk S δ)) mu0 t Sᶜ = 0 := by
  induction t with
  | zero => simpa using hmu
  | succ t ih =>
      rw [iterate_succ, step_apply _ _ hS.compl]
      have h0 : ∀ᵐ x ∂(iterate (lazy (speedyWalk S δ)) mu0 t), x ∈ S :=
        MeasureTheory.ae_iff.2 ih
      have hae : (fun x => lazy (speedyWalk S δ) x Sᶜ)
          =ᵐ[iterate (lazy (speedyWalk S δ)) mu0 t] (fun _ => (0:ℝ≥0∞)) := by
        filter_upwards [h0] with x hx
        exact lazy_speedyWalk_apply_compl_eq_zero hS δ hx
      rw [lintegral_congr_ae hae, lintegral_zero]

/-- **Sampling a proper subbody is not sampling the body — at every finite time.**

If the chain is `lazy (speedyWalk S δ)` and the start puts no mass outside `S`, then a
`MixesWithin` bound `r` against `Arlib.uniformOn volume K` forces

    1 − vol S / vol K  ≤  r,

for **every** `t`.  The proof is the support statement
`iterate_lazy_speedyWalk_compl_eq_zero` evaluated at the set `S` itself: the law of the walk
gives `S` mass `1`, the target gives it `vol S / vol K`.

No convexity, no isoperimetry, no conductance: this is a statement about *which body the
kernel lives on*, and it is why replacing `K` by a subbody in order to discharge a
hypothesis is not free. -/
theorem le_of_mixesWithin_lazy_speedyWalk_confined {K S : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (hSm : MeasurableSet S) (δ : ℝ)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0]
    (hmu : mu0 Sᶜ = 0) {t : ℕ} {r : ℝ≥0∞}
    (h : MixesWithin (lazy (speedyWalk S δ)) (Arlib.uniformOn volume K) mu0 t r) :
    1 - volume S / volume K ≤ r := by
  have hz := iterate_lazy_speedyWalk_compl_eq_zero hSm δ hmu t
  have hone : iterate (lazy (speedyWalk S δ)) mu0 t S = 1 := by
    have hadd := measure_add_measure_compl
      (μ := iterate (lazy (speedyWalk S δ)) mu0 t) hSm
    rw [hz, add_zero, measure_univ] at hadd
    exact hadd
  have h1 := (h S hSm).1
  rw [hone] at h1
  have hKS : Arlib.uniformOn volume K S ≤ volume S / volume K := by
    rw [Arlib.uniformOn_apply volume hKm hSm]
    gcongr
    exact Set.inter_subset_left
  exact tsub_le_iff_left.2 (h1.trans (by gcongr))

/-- **The obstruction at the good-points body.**

`le_of_mixesWithin_lazy_speedyWalk_confined` instantiated at
`S = K ∩ {x | ofReal (3/4) ≤ ell K δ x}`, the body of `convex_goodPoints` and
`volume_goodPoints_ge`.  Running the walk there costs at least the relative volume deficit
`1 − vol K_δ / vol K` in total variation, at every `t`.

`volume_goodPoints_ge` (`SmoothSqrt.lean:650`) bounds that deficit by `16e²·δ√n`, so the price
is *quantified*, not infinite — an `s`-conductance argument at `s = 16e²δ√n` is exactly the
device that would pay it.  What has no price attached is `ell_goodPoints_le_ell`: on `K_δ` the
comparability certificate does not exist at all. -/
theorem le_of_mixesWithin_goodPoints {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (δ : ℝ)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0]
    (hmu : mu0 (K ∩ {x : EuclideanSpace ℝ (Fin n) |
      ENNReal.ofReal (3 / 4) ≤ ell K δ x})ᶜ = 0)
    {t : ℕ} {r : ℝ≥0∞}
    (h : MixesWithin (lazy (speedyWalk (K ∩ {x : EuclideanSpace ℝ (Fin n) |
        ENNReal.ofReal (3 / 4) ≤ ell K δ x}) δ))
      (Arlib.uniformOn volume K) mu0 t r) :
    1 - volume (K ∩ {x : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal (3 / 4) ≤ ell K δ x})
        / volume K ≤ r :=
  le_of_mixesWithin_lazy_speedyWalk_confined hKm
    (hKm.inter (measurableSet_le measurable_const (measurable_ell hKm δ))) δ hmu h

/-- **A fully discharged instance of the obstruction** (`CLAUDE.md` §11).

`S = B(0,1) ⊆ K = B(0,2) ⊆ ℝⁿ`.  Every hypothesis of
`le_of_mixesWithin_lazy_speedyWalk_confined` is discharged — measurability by
`measurableSet_ball`, the start `mu0 = uniformOn volume B(0,1)` by
`Arlib.uniformOn_apply`, the volume ratio by `Measure.addHaar_ball_of_pos` — and the
conclusion is a number: the lazy speedy walk **confined to the unit ball** is never, at any
`t` and any step size `δ`, within total variation better than `1 − 2⁻ⁿ` of the uniform law on
`B(0,2)`.

This is the shape the `K_δ` route would have to beat, and it shows the obstruction is not an
artefact of the good-points body: it is a property of *confining the chain to a proper
subbody of positive volume deficit*, and it holds at every finite time, not in the limit. -/
theorem obstruction_ballOne_in_ballTwo (δ : ℝ) {t : ℕ} {r : ℝ≥0∞}
    (h : MixesWithin (lazy (speedyWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) t r) :
    1 - 1 / ENNReal.ofReal ((2:ℝ) ^ n) ≤ r := by
  haveI : IsProbabilityMeasure
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    Arlib.isProbabilityMeasure_uniformOn volume volume_unitBall_ne_zero volume_unitBall_ne_top
  have hmu : Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)ᶜ = 0 := by
    rw [Arlib.uniformOn_apply volume measurableSet_ball measurableSet_ball.compl,
      Set.compl_inter_self, measure_empty, ENNReal.zero_div]
  have hkey := le_of_mixesWithin_lazy_speedyWalk_confined measurableSet_ball
    measurableSet_ball δ hmu h
  have h2 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
      = ENNReal.ofReal ((2:ℝ) ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [Measure.addHaar_ball_of_pos volume 0 (by norm_num : (0:ℝ) < 2),
      finrank_euclideanSpace_fin]
  have hratio : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      / volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
      = 1 / ENNReal.ofReal ((2:ℝ) ^ n) := by
    have hv0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
      volume_unitBall_ne_zero
    have hvtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
      volume_unitBall_ne_top
    have hmd := ENNReal.mul_div_mul_right (1 : ℝ≥0∞) (ENNReal.ofReal ((2:ℝ) ^ n)) hv0 hvtop
    rw [one_mul] at hmd
    rw [h2]
    exact hmd
  rwa [hratio] at hkey

/-! ## Axiom check -/

#print axioms exp_two_lt_eight
#print axioms ofReal_div_one_sub_le
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_sqrt
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_sqrt_unitBallStart
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_sharp
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_sharp_steps
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_sharp_ballTwo
#print axioms sqrtSharp_gain_eq
#print axioms sqrtSharp_sq_gain_eq
#print axioms phi_uncond_le_phi_sharp
#print axioms steps_sharp_le_steps_uncond
#print axioms mixesWithin_lazy_speedyWalk_sqrtCond
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_sqrtCond
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_sharp3
#print axioms ell_mono_body
#print axioms ell_goodPoints_le_ell
#print axioms speedyWalk_apply_compl_eq_zero
#print axioms lazy_speedyWalk_apply_compl_eq_zero
#print axioms iterate_lazy_speedyWalk_compl_eq_zero
#print axioms le_of_mixesWithin_lazy_speedyWalk_confined
#print axioms le_of_mixesWithin_goodPoints
#print axioms obstruction_ballOne_in_ballTwo

end Arlib.MarkovChains
