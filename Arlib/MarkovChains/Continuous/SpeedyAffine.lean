/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.UniformSamplerUncond

/-!
# Affine equivariance of the speedy walk, and the unconditional sampler on a body with an
inscribed ball anywhere

`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond`
(`UniformSamplerUncond.lean`) is stated for a convex body `K` with
`Metric.ball 0 1 ⊆ K` — a **unit** ball at the **origin**.  Every consumer whose bodies are
not normalised that way (inflated polytopes, for instance, which come with an inscribed ball
`Metric.ball cen γ ⊆ K` at some interior centre and some radius) cannot use it directly.

The obstruction is purely affine, and this file removes it.  Under the chart

    x ↦ (x − cen)/γ,        equivalently        y ↦ γ • y + cen,

a body with `Metric.ball cen γ ⊆ K` becomes a body with `Metric.ball 0 1 ⊆ K'`, and the
speedy walk with step `δ` on `K` becomes the speedy walk with step `δ/γ` on `K'`.

## The crux

Everything is transport along one identity, `Arlib.MarkovChains.map_speedyWalk_affineChart`:

    Measure.map (fun z => γ • z + cen) (speedyWalk ((fun z => γ • z + cen) ⁻¹' K) (δ / γ) y)
      = speedyWalk K δ (γ • y + cen).

This is the `x ↦ (x − cen)/γ` equivariance read through the inverse chart
(`y = (x − cen)/γ ⟺ x = γ • y + cen`); the forward chart is used only through preimages,
which is what keeps every measure-theoretic side condition trivial:
`MeasureTheory.Measure.addHaar_preimage_smul` and `measure_preimage_add_right` hold for
*arbitrary* sets, so no image-measurability ever has to be proved.

The Jacobian `J = (γⁿ)⁻¹` appears in both the numerator and the denominator of the speedy
walk's one-step law and cancels; that cancellation is the whole content of the crux.

## Main results

* `Arlib.MarkovChains.volume_preimage_affineChart` — `vol(S⁻¹A) = (γⁿ)⁻¹ · vol A`, the
  Jacobian, for **every** set `A`.
* `Arlib.MarkovChains.preimage_affineChart_ball` — `S⁻¹(B(S y, δ)) = B(y, δ/γ)`.
* `Arlib.MarkovChains.ell_affineChart`, `Arlib.MarkovChains.stuckPoints_affineChart` — the
  local conductance and the stuck set are equivariant.
* `Arlib.MarkovChains.map_speedyWalk_affineChart` — **the crux**, above.
* `Arlib.MarkovChains.map_lazy_of_map_kernel`,
  `Arlib.MarkovChains.map_step_of_map_kernel`,
  `Arlib.MarkovChains.map_iterate_of_map_kernel` — a kernel identity of the crux's shape
  lifts through `lazy`, through one step of the chain, and through `t` steps.  Stated for an
  arbitrary measurable `S`, since none of it is about the affine chart.
* `Arlib.MarkovChains.map_uniformOn_affineChart` — `Arlib.uniformOn volume` is equivariant;
  here the Jacobian cancels against the normalisation, so **no** factor survives.
* `Arlib.MarkovChains.map_ellMeasure_affineChart`,
  `Arlib.MarkovChains.map_ellProb_affineChart` — the speedy walk's stationary measure is
  equivariant, the unnormalised one up to the Jacobian and the normalised one exactly.
* `Arlib.MarkovChains.tvLe_map`, `Arlib.MarkovChains.isWarm_map`,
  `Arlib.MarkovChains.mixesWithin_map` — `Arlib.TVLe`, `Arlib.IsWarm` and `MixesWithin` are
  stated in terms of measures of measurable sets, hence transport forwards along any
  measurable map.
* `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine` — **the payoff**:
  the unconditional sampler for a convex `K` with `Metric.ball cen γ ⊆ K`, `0 < γ`, and
  diameter at most `D`.
* `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine_steps` — the same
  with the step count in closed form.
* `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine_witness` — the
  non-vacuity witness at a concrete `cen`, `γ`, `K`.

## How the parameters transform — the well-roundedness cost

Write `S y = γ • y + cen`, `K' = S⁻¹ K`.  Then

| in `K'` (normalised) | in `K` (original) |
| --- | --- |
| inscribed ball `B(0,1)` | `B(cen, γ)` |
| diameter `D/γ` | diameter `D` |
| step `δ' = ρ/(4n)` | step `δ = γ·ρ/(4n)` |
| accuracy `ρ` | accuracy `ρ` — **unchanged** |

The accuracy does not move because total variation is a statement about measures of
measurable sets and `S` is a bijection whose inverse is measurable, so `tvLe_map` transports
`ρ` verbatim.  The diameter does move, and that is the price: substituting `D ↦ D/γ` into the
`O(n⁵D²log(1+D)/ρ²)` count of `UniformSamplerUncond.lean` gives

    t = O( n⁵ · (D/γ)² · log(1 + D/γ) / ρ² ).

`D/γ` is exactly the **well-roundedness ratio** of `K` witnessed by the pair
(inscribed ball `B(cen,γ)`, circumscribed diameter `D`), and the count is quadratic in it.
A caller whose body has a tiny inscribed ball pays for it here, quadratically, and no
rounding step in this file hides that: making `D/γ` small is the caller's job.

## Scope — read before quoting anything from this file

Every theorem here is a **Markov-chain mixing statement**, exactly as in
`UniformSamplerUncond.lean`.  It is **not** a running-time claim about any algorithm: `t`
counts abstract kernel applications, and nothing here bounds the cost of one step (which
needs a membership oracle for `K` and a sample from a ball), nor bit complexity, nor oracle
calls.  In particular nothing here is a claim about the TTC pipeline, about volume
computation, or about lattice counting.

`2 ≤ n` is inherited from `Arlib.hiso_ellProb_of_ball_bound` through
`mixesWithin_lazy_speedyWalk_uniformOn_uncond`; it is not widened.

**No `def`, `structure`, `class`, `axiom` or named `Prop` is introduced in this file.**  Every
declaration is a `theorem`, every hypothesis is an inline binder, and the affine chart is
spelled out as `fun z => γ • z + cen` at every occurrence rather than being named.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The chart and its Jacobian

`S y = γ • y + cen` is the inverse of `x ↦ (x − cen)/γ`.  Only preimages under `S` are used,
so every measure-theoretic statement below is unconditional in the set it is applied to. -/

/-- **The affine chart is measurable.**  Used as a side condition everywhere below. -/
theorem measurable_affineChart (γ : ℝ) (cen : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) := by
  fun_prop

/-- **The Jacobian of the chart.**  For every set `A` — no measurability needed, because
`MeasureTheory.Measure.addHaar_preimage_smul` and `measure_preimage_add_right` are both
unconditional in the set:

    vol( {z | γ • z + cen ∈ A} )  =  (γⁿ)⁻¹ · vol A.

This is the one factor that has to cancel for the speedy walk to be equivariant. -/
theorem volume_preimage_affineChart {γ : ℝ} (hγ : 0 < γ) (cen : EuclideanSpace ℝ (Fin n))
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    volume ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' A)
      = ENNReal.ofReal ((γ ^ n)⁻¹) * volume A := by
  have hpre : (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' A
      = (fun z : EuclideanSpace ℝ (Fin n) => γ • z) ⁻¹'
        ((fun z : EuclideanSpace ℝ (Fin n) => z + cen) ⁻¹' A) := rfl
  rw [hpre, Measure.addHaar_preimage_smul volume hγ.ne', measure_preimage_add_right,
    finrank_euclideanSpace_fin, abs_of_pos (by positivity : (0:ℝ) < (γ ^ n)⁻¹)]

/-- The Jacobian is neither `0` nor `⊤`; both are needed for it to cancel. -/
theorem ofReal_inv_pow_ne_zero {γ : ℝ} (hγ : 0 < γ) :
    ENNReal.ofReal ((γ ^ n)⁻¹) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (by positivity)).ne'

/-- **The chart scales distances by `γ`.** -/
theorem dist_affineChart {γ : ℝ} (hγ : 0 < γ) (cen : EuclideanSpace ℝ (Fin n))
    (y z : EuclideanSpace ℝ (Fin n)) :
    dist (γ • y + cen) (γ • z + cen) = γ * dist y z := by
  rw [dist_eq_norm, dist_eq_norm,
    show γ • y + cen - (γ • z + cen) = γ • (y - z) by module, norm_smul, Real.norm_eq_abs,
    abs_of_pos hγ]

/-- **The chart carries `B(y, δ/γ)` onto `B(S y, δ)`**, stated as a preimage. -/
theorem preimage_affineChart_ball {γ : ℝ} (hγ : 0 < γ) (cen : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' (Metric.ball (γ • y + cen) δ)
      = Metric.ball y (δ / γ) := by
  ext z
  simp only [Set.mem_preimage, Metric.mem_ball, dist_affineChart hγ, lt_div_iff₀ hγ]
  constructor <;> intro h <;> linarith

/-! ## 2. `ell` and the stuck set are equivariant -/

/-- **The local conductance is a chart invariant.**  `ell` is a ratio of two volumes that
pick up the *same* Jacobian, so the Jacobian cancels:

    ell (S⁻¹ K) (δ/γ) y  =  ell K δ (S y). -/
theorem ell_affineChart {K : Set (EuclideanSpace ℝ (Fin n))} {γ : ℝ} (hγ : 0 < γ)
    (cen : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ell ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K) (δ / γ) y
      = ell K δ (γ • y + cen) := by
  rw [ell_apply, ell_apply, ← preimage_affineChart_ball hγ cen y δ, ← Set.preimage_inter,
    volume_preimage_affineChart hγ, volume_preimage_affineChart hγ]
  exact ENNReal.mul_div_mul_left _ _ (ofReal_inv_pow_ne_zero hγ) ENNReal.ofReal_ne_top

/-- **The stuck set is a chart invariant**, being a level set of `ell`. -/
theorem stuckPoints_affineChart {K : Set (EuclideanSpace ℝ (Fin n))} {γ : ℝ} (hγ : 0 < γ)
    (cen : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    StuckPoints ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K) (δ / γ)
      = (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' StuckPoints K δ := by
  ext y
  rw [StuckPoints, Set.mem_setOf_eq, ell_affineChart hγ]
  rfl

/-! ## 3. The crux: the speedy-walk kernel is equivariant -/

/-- **The crux — the speedy walk is equivariant under the affine chart.**

    Measure.map (fun z => γ • z + cen) (speedyWalk ((fun z => γ • z + cen) ⁻¹' K) (δ/γ) y)
      = speedyWalk K δ (γ • y + cen).

Read through the inverse chart `x ↦ (x − cen)/γ`: proposing uniformly from
`B(x, δ) ∩ K` and then normalising `x` is the same as normalising first and proposing
uniformly from `B(y, δ/γ) ∩ ((K − cen)/γ)`.

The proof is the cancellation of the Jacobian `J = (γⁿ)⁻¹`: it multiplies the numerator
`vol(t ∩ B(x,δ) ∩ K)` and the denominator `vol(B(x,δ) ∩ K)` of the one-step law by the same
factor.  The holding atom transports because the stuck set does (`stuckPoints_affineChart`).

Needs only `MeasurableSet K` and `0 < γ`: no convexity, no positivity of `δ`, no bound on
`vol K`. -/
theorem map_speedyWalk_affineChart {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {γ : ℝ} (hγ : 0 < γ) (cen : EuclideanSpace ℝ (Fin n)) (δ : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    Measure.map (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen)
        (speedyWalk ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K) (δ / γ) y)
      = speedyWalk K δ (γ • y + cen) := by
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) :=
    measurable_affineChart γ cen
  have hK' : MeasurableSet ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K) :=
    hK.preimage hS
  have hJ0 : ENNReal.ofReal ((γ ^ n)⁻¹) ≠ 0 := ofReal_inv_pow_ne_zero hγ
  have hJtop : ENNReal.ofReal ((γ ^ n)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  ext t ht
  rw [Measure.map_apply hS ht, speedyWalk_apply_set hK' (δ / γ) y (ht.preimage hS),
    speedyWalk_apply_set hK δ (γ • y + cen) ht, stuckPoints_affineChart hγ,
    ← preimage_affineChart_ball hγ cen y δ, ← Set.preimage_inter, ← Set.preimage_inter,
    volume_preimage_affineChart hγ, volume_preimage_affineChart hγ]
  -- the two indicators are the same, and the Jacobian cancels in the first summand
  have hind1 : ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' StuckPoints K δ).indicator
        (fun _ => (1 : ℝ≥0∞)) y
      = (StuckPoints K δ).indicator (fun _ => (1 : ℝ≥0∞)) (γ • y + cen) := by
    by_cases h : γ • y + cen ∈ StuckPoints K δ
    · have hy : y ∈ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' StuckPoints K δ := h
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem h]
    · have hy : y ∉ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' StuckPoints K δ := h
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem h]
  have hind2 : ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' t).indicator
        (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) y
      = t.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (γ • y + cen) := by
    by_cases h : γ • y + cen ∈ t
    · have hy : y ∈ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' t := h
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem h, Pi.one_apply, Pi.one_apply]
    · have hy : y ∉ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' t := h
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem h]
  rw [hind1, hind2]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hJ0) (Or.inl hJtop),
    show (ENNReal.ofReal ((γ ^ n)⁻¹))⁻¹
          * (volume (Metric.ball (γ • y + cen) δ ∩ K))⁻¹
          * (ENNReal.ofReal ((γ ^ n)⁻¹)
            * volume (t ∩ (Metric.ball (γ • y + cen) δ ∩ K)))
        = ((ENNReal.ofReal ((γ ^ n)⁻¹))⁻¹ * ENNReal.ofReal ((γ ^ n)⁻¹))
          * ((volume (Metric.ball (γ • y + cen) δ ∩ K))⁻¹
            * volume (t ∩ (Metric.ball (γ • y + cen) δ ∩ K))) by ring,
    ENNReal.inv_mul_cancel hJ0 hJtop, one_mul]

/-! ## 4. Transport along a kernel identity of the crux's shape

Nothing in this section is about the affine chart: the hypothesis is exactly the conclusion
of the crux, for an arbitrary measurable `S`. -/

/-- **`lazy` transports.**  If `Measure.map S (P' y) = P (S y)` for every `y`, the same holds
for the lazy versions: the holding atom at `y` maps to the holding atom at `S y`. -/
theorem map_lazy_of_map_kernel {S : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hS : Measurable S) {P' P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (h : ∀ y, Measure.map S (P' y) = P (S y)) (y : EuclideanSpace ℝ (Fin n)) :
    Measure.map S (lazy P' y) = lazy P (S y) := by
  ext t ht
  have h1 : P' y (S ⁻¹' t) = P (S y) t := by
    rw [← Measure.map_apply hS ht, h y]
  have h2 : (S ⁻¹' t).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) y
      = t.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (S y) := by
    by_cases hmem : S y ∈ t
    · have hy : y ∈ S ⁻¹' t := hmem
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hmem, Pi.one_apply, Pi.one_apply]
    · have hy : y ∉ S ⁻¹' t := hmem
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hmem]
  rw [Measure.map_apply hS ht, lazy_apply_set P' y (ht.preimage hS), lazy_apply_set P (S y) ht,
    h1, h2]

/-- **One step of the chain transports.**  `step P' ν` pushed forward is `step P` of the
push-forward. -/
theorem map_step_of_map_kernel {S : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hS : Measurable S) {P' P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (h : ∀ y, Measure.map S (P' y) = P (S y)) (nu : Measure (EuclideanSpace ℝ (Fin n))) :
    Measure.map S (step P' nu) = step P (Measure.map S nu) := by
  ext t ht
  rw [Measure.map_apply hS ht, step_apply P' nu (ht.preimage hS), step_apply P _ ht,
    lintegral_map (Kernel.measurable_coe P ht) hS]
  refine lintegral_congr fun y => ?_
  rw [← Measure.map_apply hS ht, h y]

/-- **The whole chain transports.**  `t` steps commute with the push-forward.  This is the
statement `MixesWithin` is transported along. -/
theorem map_iterate_of_map_kernel {S : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hS : Measurable S) {P' P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (h : ∀ y, Measure.map S (P' y) = P (S y)) (nu : Measure (EuclideanSpace ℝ (Fin n)))
    (t : ℕ) :
    Measure.map S (iterate P' nu t) = iterate P (Measure.map S nu) t := by
  induction t with
  | zero => rfl
  | succ m ih => rw [iterate_succ, iterate_succ, ← ih, map_step_of_map_kernel hS h]

/-! ## 5. The measures transport: `uniformOn`, `ellMeasure`, `ellProb` -/

/-- **`Arlib.uniformOn volume` is equivariant.**  Numerator and denominator both pick up the
Jacobian, so it cancels and **no factor survives**:

    Measure.map S (Arlib.uniformOn volume (S⁻¹ A)) = Arlib.uniformOn volume A.

Unconditional in `vol A` — the `0` and `⊤` cases hold for the same reason
`Arlib.uniformOn_apply` needs no guard. -/
theorem map_uniformOn_affineChart {γ : ℝ} (hγ : 0 < γ) (cen : EuclideanSpace ℝ (Fin n))
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    Measure.map (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen)
        (Arlib.uniformOn volume ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' A))
      = Arlib.uniformOn volume A := by
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) :=
    measurable_affineChart γ cen
  ext t ht
  rw [Measure.map_apply hS ht, Arlib.uniformOn_apply volume (hA.preimage hS) (ht.preimage hS),
    Arlib.uniformOn_apply volume hA ht, ← Set.preimage_inter, volume_preimage_affineChart hγ,
    volume_preimage_affineChart hγ]
  exact ENNReal.mul_div_mul_left _ _ (ofReal_inv_pow_ne_zero hγ) ENNReal.ofReal_ne_top

/-- **Lebesgue measure transports with the Jacobian.** -/
theorem map_volume_affineChart {γ : ℝ} (hγ : 0 < γ) (cen : EuclideanSpace ℝ (Fin n)) :
    Measure.map (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
      = ENNReal.ofReal ((γ ^ n)⁻¹) • (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  ext t ht
  rw [Measure.map_apply (measurable_affineChart γ cen) ht, volume_preimage_affineChart hγ,
    Measure.smul_apply, smul_eq_mul]

/-- **Change of variables for `∫⁻` along the chart.** -/
theorem lintegral_comp_affineChart {γ : ℝ} (hγ : 0 < γ) (cen : EuclideanSpace ℝ (Fin n))
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (γ • x + cen) = ENNReal.ofReal ((γ ^ n)⁻¹) * ∫⁻ y, f y := by
  have h := lintegral_map (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hf
    (measurable_affineChart γ cen)
  rw [map_volume_affineChart hγ, lintegral_smul_measure] at h
  exact h.symm

/-- **Change of variables for a set integral along the chart.** -/
theorem setLIntegral_comp_affineChart {γ : ℝ} (hγ : 0 < γ) (cen : EuclideanSpace ℝ (Fin n))
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' A, f (γ • x + cen)
      = ENNReal.ofReal ((γ ^ n)⁻¹) * ∫⁻ y in A, f y := by
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) :=
    measurable_affineChart γ cen
  rw [← lintegral_indicator (hA.preimage hS), ← lintegral_indicator hA]
  have hrw : ∀ x : EuclideanSpace ℝ (Fin n),
      ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' A).indicator
          (fun x => f (γ • x + cen)) x
        = (A.indicator f) (γ • x + cen) := by
    intro x
    by_cases hmem : γ • x + cen ∈ A
    · have hx : x ∈ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' A := hmem
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hmem]
    · have hx : x ∉ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' A := hmem
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hmem]
  simp_rw [hrw]
  exact lintegral_comp_affineChart hγ cen (hf.indicator hA)

/-- **The unnormalised stationary measure of the speedy walk transports, up to the
Jacobian.** -/
theorem map_ellMeasure_affineChart {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {γ : ℝ} (hγ : 0 < γ) (cen : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    Measure.map (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen)
        (ellMeasure ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K) (δ / γ))
      = ENNReal.ofReal ((γ ^ n)⁻¹) • ellMeasure K δ := by
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) :=
    measurable_affineChart γ cen
  ext t ht
  have h1 : ellMeasure ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K) (δ / γ)
        ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' t)
      = ∫⁻ x in (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' (t ∩ K),
          ell K δ (γ • x + cen) := by
    rw [ellMeasure, withDensity_apply _ (ht.preimage hS),
      Measure.restrict_restrict (ht.preimage hS), ← Set.preimage_inter]
    exact lintegral_congr fun x => ell_affineChart hγ cen δ x
  have h2 : ellMeasure K δ t = ∫⁻ y in t ∩ K, ell K δ y := by
    rw [ellMeasure, withDensity_apply _ ht, Measure.restrict_restrict ht]
  rw [Measure.map_apply hS ht, Measure.smul_apply, smul_eq_mul, h1, h2,
    setLIntegral_comp_affineChart hγ cen (ht.inter hK) (measurable_ell hK δ)]

/-- **The stationary *probability* measure of the speedy walk is a chart invariant.**  The
Jacobian of `map_ellMeasure_affineChart` is cancelled by the normalisation, exactly as for
`Arlib.uniformOn`. -/
theorem map_ellProb_affineChart {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {γ : ℝ} (hγ : 0 < γ) (cen : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    Measure.map (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen)
        (ellProb ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K) (δ / γ))
      = ellProb K δ := by
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) :=
    measurable_affineChart γ cen
  have hJ0 : ENNReal.ofReal ((γ ^ n)⁻¹) ≠ 0 := ofReal_inv_pow_ne_zero hγ
  have hJtop : ENNReal.ofReal ((γ ^ n)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  have huniv : ellMeasure ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K) (δ / γ)
        Set.univ
      = ENNReal.ofReal ((γ ^ n)⁻¹) * ellMeasure K δ Set.univ := by
    have h := congrArg (fun m : Measure (EuclideanSpace ℝ (Fin n)) => m Set.univ)
      (map_ellMeasure_affineChart hK hγ cen δ)
    rwa [Measure.map_apply hS MeasurableSet.univ, Set.preimage_univ, Measure.smul_apply,
      smul_eq_mul] at h
  have hcancel : (ENNReal.ofReal ((γ ^ n)⁻¹) * ellMeasure K δ Set.univ)⁻¹
        * ENNReal.ofReal ((γ ^ n)⁻¹)
      = (ellMeasure K δ Set.univ)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hJ0) (Or.inl hJtop),
      show (ENNReal.ofReal ((γ ^ n)⁻¹))⁻¹ * (ellMeasure K δ Set.univ)⁻¹
            * ENNReal.ofReal ((γ ^ n)⁻¹)
          = ((ENNReal.ofReal ((γ ^ n)⁻¹))⁻¹ * ENNReal.ofReal ((γ ^ n)⁻¹))
            * (ellMeasure K δ Set.univ)⁻¹ by ring,
      ENNReal.inv_mul_cancel hJ0 hJtop, one_mul]
  rw [ellProb, Measure.map_smul, map_ellMeasure_affineChart hK hγ cen δ, huniv, smul_smul,
    hcancel, ellProb]

/-! ## 6. The predicates transport

`Arlib.TVLe`, `Arlib.IsWarm` and `MixesWithin` are stated purely in terms of the measures of
measurable sets, so they transport forwards along **any** measurable map — no bijectivity, no
Jacobian, and the accuracy `ε` (resp. the warmness `M`) is unchanged. -/

/-- **Total variation transports.**  The accuracy `ε` is unchanged. -/
theorem tvLe_map {S : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hS : Measurable S)
    {mu nu : Measure (EuclideanSpace ℝ (Fin n))} {eps : ℝ≥0∞} (h : Arlib.TVLe mu nu eps) :
    Arlib.TVLe (Measure.map S mu) (Measure.map S nu) eps := by
  intro t ht
  rw [Measure.map_apply hS ht, Measure.map_apply hS ht]
  exact h _ (ht.preimage hS)

/-- **Warmness transports.**  The constant `M` is unchanged. -/
theorem isWarm_map {S : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hS : Measurable S)
    {M : ℝ≥0∞} {mu nu : Measure (EuclideanSpace ℝ (Fin n))} (h : Arlib.IsWarm M mu nu) :
    Arlib.IsWarm M (Measure.map S mu) (Measure.map S nu) := by
  intro t ht
  rw [Measure.map_apply hS ht, Measure.map_apply hS ht]
  exact h _ (ht.preimage hS)

/-- **A mixing bound transports** along any kernel identity of the crux's shape, with the
same number of steps and the same accuracy. -/
theorem mixesWithin_map {S : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hS : Measurable S) {P' P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (h : ∀ y, Measure.map S (P' y) = P (S y))
    {pi mu0 : Measure (EuclideanSpace ℝ (Fin n))} {t : ℕ} {eps : ℝ≥0∞}
    (hmix : MixesWithin P' pi mu0 t eps) :
    MixesWithin P (Measure.map S pi) (Measure.map S mu0) t eps := by
  rw [mixesWithin_iff, ← map_iterate_of_map_kernel hS h]
  exact tvLe_map hS hmix

/-! ## 7. The payoff: the unconditional sampler with the inscribed ball anywhere -/

/-- **Unconditional polynomial-time uniform sampling on a convex body with an inscribed ball
at an arbitrary centre and radius.**

Let `2 ≤ n`, let `K ⊆ ℝⁿ` be measurable and convex with `Metric.ball cen γ ⊆ K` for some
`0 < γ`, and let all pairwise distances in `K` be at most `D`.  Let `0 < ρ ≤ 1`.  Then,
starting from the **samplable** law `Arlib.uniformOn volume (Metric.ball cen γ)`, after

    t ≥ conductanceMixingTime ((1 + D/γ)^(2n))
          (min (1/32) ((1/(8·(D/γ)))·(ρ/(4n))/(256n))) (ρ/2)

steps the law of the lazy speedy walk with step size `δ = γ·ρ/(4n)` is within total
variation `ρ` of `Arlib.uniformOn volume K`.

This is `mixesWithin_lazy_speedyWalk_uniformOn_uncond` transported along the chart
`x ↦ (x − cen)/γ`.  The substitution is `D ↦ D/γ` in the step count, `δ ↦ γ·δ` in the walk,
and `ρ ↦ ρ` — the accuracy is **unchanged**, because `tvLe_map` moves it verbatim.

`D/γ` is the well-roundedness ratio of `K` witnessed by the given inscribed ball, and the
count is quadratic in it; `mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine_steps` writes
that out.

**Scope.**  A mixing statement about a Markov kernel — not a running-time claim, and not a
bound on the cost of one step.  See the module docstring. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    {cen : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) {t : ℕ}
    (ht : conductanceMixingTime ((1 + D / γ) ^ (2 * n))
        (min (1 / 32)
          (1 / (8 * (D / γ)) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) (rho / 2) ≤ t) :
    MixesWithin (lazy (speedyWalk K (γ * (rho / (4 * (n : ℝ))))))
      (Arlib.uniformOn volume K)
      (Arlib.uniformOn volume (Metric.ball cen γ))
      t (ENNReal.ofReal rho) := by
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) :=
    measurable_affineChart γ cen
  have hK' : MeasurableSet ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K) :=
    hK.preimage hS
  -- the chart sends `B(0,1)` onto `B(cen, γ)`
  have hcen : γ • (0 : EuclideanSpace ℝ (Fin n)) + cen = cen := by
    rw [smul_zero, zero_add]
  have hball0 : (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' (Metric.ball cen γ)
      = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    have h := preimage_affineChart_ball hγ cen (0 : EuclideanSpace ℝ (Fin n)) γ
    rw [hcen, div_self hγ.ne'] at h
    exact h
  -- the normalised body: convex, containing the unit ball, of diameter `D/γ`
  have hconv' : Convex ℝ ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K) := by
    intro u hu v hv a b ha hb hab
    have hmem : γ • (a • u + b • v) + cen
        = a • (γ • u + cen) + b • (γ • v + cen) := by
      have : a • (γ • u + cen) + b • (γ • v + cen)
          = γ • (a • u + b • v) + (a + b) • cen := by module
      rw [this, hab, one_smul]
    show γ • (a • u + b • v) + cen ∈ K
    rw [hmem]
    exact hconv hu hv ha hb hab
  have hball' : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1
      ⊆ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K := by
    rw [← hball0]
    exact Set.preimage_mono hball
  have hD' : ∀ x ∈ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K,
      ∀ y ∈ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K, dist x y ≤ D / γ := by
    intro x hx y hy
    have h := hD _ hx _ hy
    rw [dist_affineChart hγ] at h
    rw [le_div_iff₀ hγ, mul_comm]
    exact h
  -- the normalised statement
  have hmix := mixesWithin_lazy_speedyWalk_uniformOn_uncond hn hK' hconv' hball' hD' hrho hrho1
    ht
  -- transport it back along the chart
  have hstep : γ * (rho / (4 * (n : ℝ))) / γ = rho / (4 * (n : ℝ)) :=
    mul_div_cancel_left₀ _ hγ.ne'
  have hker : ∀ y : EuclideanSpace ℝ (Fin n),
      Measure.map (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen)
          (lazy (speedyWalk ((fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K)
            (rho / (4 * (n : ℝ)))) y)
        = lazy (speedyWalk K (γ * (rho / (4 * (n : ℝ))))) (γ • y + cen) := by
    refine map_lazy_of_map_kernel hS (fun z => ?_)
    have h := map_speedyWalk_affineChart hK hγ cen (γ * (rho / (4 * (n : ℝ)))) z
    rwa [hstep] at h
  have htrans := mixesWithin_map hS hker hmix
  rwa [map_uniformOn_affineChart hγ cen hK, ← hball0,
    map_uniformOn_affineChart hγ cen measurableSet_ball] at htrans

/-- **The affine sampler with the step count written out — the `(D/γ)²` made explicit.**

Same statement as `mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine`, with
`conductanceMixingTime` replaced by the explicit sufficient count

    t ≥ (2n·log(1 + D/γ) + 2·log(2/ρ))
          / min(1/32, (1/(8·(D/γ)))·(ρ/(4n))/(256n))²  +  1.

Since `min(1/32, (1/(8·(D/γ)))·(ρ/(4n))/(256n)) = min(1/32, ργ/(8192·D·n²))`, the count is

    O( n⁵ · (D/γ)² · log(1 + D/γ) / ρ² ),

polynomial in `n`, `D/γ` and `1/ρ`, and unconditional.  **The `(D/γ)²` is the
well-roundedness cost** of the inscribed ball `Metric.ball cen γ`: a caller with a small `γ`
pays for it quadratically, here and nowhere else. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine_steps (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    {cen : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) {t : ℕ}
    (ht : (2 * (n : ℝ) * Real.log (1 + D / γ) + 2 * Real.log (2 / rho))
          / (min (1 / 32)
              (1 / (8 * (D / γ)) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2 + 1
        ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyWalk K (γ * (rho / (4 * (n : ℝ))))))
      (Arlib.uniformOn volume K)
      (Arlib.uniformOn volume (Metric.ball cen γ))
      t (ENNReal.ofReal rho) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  -- `1/2 ≤ D/γ`, obtained on the normalised body
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) :=
    measurable_affineChart γ cen
  have hcen : γ • (0 : EuclideanSpace ℝ (Fin n)) + cen = cen := by rw [smul_zero, zero_add]
  have hball0 : (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' (Metric.ball cen γ)
      = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    have h := preimage_affineChart_ball hγ cen (0 : EuclideanSpace ℝ (Fin n)) γ
    rw [hcen, div_self hγ.ne'] at h
    exact h
  have hball' : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1
      ⊆ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K := by
    rw [← hball0]; exact Set.preimage_mono hball
  have hD' : ∀ x ∈ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K,
      ∀ y ∈ (fun z : EuclideanSpace ℝ (Fin n) => γ • z + cen) ⁻¹' K, dist x y ≤ D / γ := by
    intro x hx y hy
    have h := hD _ hx _ hy
    rw [dist_affineChart hγ] at h
    rw [le_div_iff₀ hγ, mul_comm]
    exact h
  have hD2 : (1 : ℝ) / 2 ≤ D / γ := half_le_diam_bound_of_ball_subset hn1 hball' hD'
  have hD0 : (0 : ℝ) < D / γ := by linarith
  have hMpos : (0 : ℝ) < 1 + D / γ := by linarith
  have hM : (1 : ℝ) ≤ (1 + D / γ) ^ (2 * n) := one_le_pow₀ (by linarith)
  have hphi0 : 0 < min (1 / 32)
      (1 / (8 * (D / γ)) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))) := by
    refine lt_min (by norm_num) ?_
    positivity
  have heps : (0 : ℝ) < rho / 2 := by linarith
  have hsqrt : rho / 2 ≤ Real.sqrt ((1 + D / γ) ^ (2 * n)) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt ((1 + D / γ) ^ (2 * n)) := by
      have h2 := Real.sqrt_le_sqrt hM
      rwa [Real.sqrt_one] at h2
    linarith
  have hlogM : Real.log ((1 + D / γ) ^ (2 * n)) = 2 * (n : ℝ) * Real.log (1 + D / γ) := by
    rw [Real.log_pow]; push_cast; ring
  have hlogeps : Real.log (1 / (rho / 2)) = Real.log (2 / rho) := by rw [one_div_div]
  refine mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine hn hK hconv hγ hball hD hrho hrho1 ?_
  have hle := conductanceMixingTime_le (M := (1 + D / γ) ^ (2 * n))
    (phi := min (1 / 32) (1 / (8 * (D / γ)) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))))
    (eps := rho / 2) hM hphi0 heps hsqrt
  rw [hlogM, hlogeps] at hle
  exact_mod_cast hle.trans ht

/-! ## 8. Non-vacuity (`CLAUDE.md` §11)

Every theorem of §7 is an implication.  The witness below discharges **every** hypothesis of
`mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine` at a concrete `cen`, a concrete `γ` and
a concrete `K`, leaving `hn : 2 ≤ n` — the scope limit inherited from
`Arlib.hiso_ellProb_of_ball_bound` — as the only surviving assumption.

The chart is genuinely affine: `cen = 3·e₀ ≠ 0` (a nonzero translation) and `γ = 1/2 ≠ 1`
(a non-unit scaling), so neither half of `x ↦ (x − cen)/γ` is the identity.  The body is
`K = B(cen, 1)`, which contains the inscribed ball `B(cen, 1/2)` **strictly**, so the start
law `Arlib.uniformOn volume (B(cen,1/2))` is genuinely different from the target
`Arlib.uniformOn volume K`, and `ρ = 1/2` is a non-trivial tolerance (`ofReal 1` would be the
vacuous total-variation bound).  Note `D/γ = 2/(1/2) = 4`, the same well-roundedness ratio as
the origin-centred witness `mixesWithin_lazy_speedyWalk_uniformOn_uncond_ballTwo`. -/

/-- **The diameter of `Metric.ball cen 1` is at most `2`**, by the triangle inequality
through the centre.  The `hD` hypothesis of the witness. -/
theorem dist_le_two_of_mem_ball_one (cen : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball cen 1)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Metric.ball cen 1) :
    dist x y ≤ 2 := by
  rw [Metric.mem_ball] at hx hy
  have h := dist_triangle x cen y
  rw [dist_comm cen y] at h
  linarith

/-- **The non-vacuity witness — a concrete `cen`, `γ`, `K`, `ρ`, `t`.**

`cen = 3·e₀`, `γ = 1/2`, `K = Metric.ball cen 1`, `ρ = 1/2`, and `t` the concrete step count.
Every hypothesis of `mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine` is discharged:

| binder | discharged by |
| --- | --- |
| `hK : MeasurableSet K` | `measurableSet_ball` |
| `hconv : Convex ℝ K` | `convex_ball` |
| `hγ : 0 < γ` | `norm_num` at `γ = 1/2` |
| `hball : B(cen, 1/2) ⊆ K` | `Metric.ball_subset_ball` |
| `hD : diam K ≤ 2` | `dist_le_two_of_mem_ball_one` |
| `hrho, hrho1` | `norm_num` at `ρ = 1/2` |
| `ht` | `le_rfl` — `t` *is* the step count |

**The only surviving hypothesis is `hn : 2 ≤ n`.**  So: the lazy speedy walk on `B(3e₀, 1)`
with step size `(1/2)·(1/2)/(4n) = 1/(16n)`, started from the uniform law on `B(3e₀, 1/2)`,
is within total variation `1/2` of the uniform law on `B(3e₀, 1)` after the stated number of
steps — a theorem with no unproved input. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine_witness (hn : 2 ≤ n) :
    MixesWithin
      (lazy (speedyWalk
        (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (3 : ℝ)) 1)
        ((1 / 2 : ℝ) * ((1 / 2 : ℝ) / (4 * (n : ℝ))))))
      (Arlib.uniformOn volume
        (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (3 : ℝ)) 1))
      (Arlib.uniformOn volume
        (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (3 : ℝ)) (1 / 2 : ℝ)))
      (conductanceMixingTime ((1 + (2 : ℝ) / (1 / 2 : ℝ)) ^ (2 * n))
        (min (1 / 32)
          (1 / (8 * ((2 : ℝ) / (1 / 2 : ℝ))) * ((1 / 2 : ℝ) / (4 * (n : ℝ)))
            / (256 * (n : ℝ))))
        ((1 / 2 : ℝ) / 2))
      (ENNReal.ofReal (1 / 2)) :=
  mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine hn measurableSet_ball (convex_ball _ _)
    (by norm_num) (Metric.ball_subset_ball (by norm_num))
    (dist_le_two_of_mem_ball_one _) (by norm_num) (by norm_num) le_rfl

/-! ## Axiom check -/

#print axioms measurable_affineChart
#print axioms volume_preimage_affineChart
#print axioms ofReal_inv_pow_ne_zero
#print axioms dist_affineChart
#print axioms preimage_affineChart_ball
#print axioms ell_affineChart
#print axioms stuckPoints_affineChart
#print axioms map_speedyWalk_affineChart
#print axioms map_lazy_of_map_kernel
#print axioms map_step_of_map_kernel
#print axioms map_iterate_of_map_kernel
#print axioms map_uniformOn_affineChart
#print axioms map_volume_affineChart
#print axioms lintegral_comp_affineChart
#print axioms setLIntegral_comp_affineChart
#print axioms map_ellMeasure_affineChart
#print axioms map_ellProb_affineChart
#print axioms tvLe_map
#print axioms isWarm_map
#print axioms mixesWithin_map
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine_steps
#print axioms dist_le_two_of_mem_ball_one
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_uncond_affine_witness

end Arlib.MarkovChains
