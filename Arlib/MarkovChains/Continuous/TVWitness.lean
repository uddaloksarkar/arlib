/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.PointwiseRoute

/-!
# A non-degenerate witness for the total-variation route

`Arlib.PointwiseRoute.exists_theorem2_of_tvLe_witness` shows that the hypotheses of
`Arlib.PointwiseRoute.theorem2_of_tvLe_inv_volume` are satisfiable, but it does so at the
*degenerate* instance: the sampler's law is taken to be `uniformOn volume S` on the nose and
the total-variation hypothesis is discharged by `Arlib.TVLe.refl`, i.e. at `ε = 0`.  That
leaves open the question the sampler interface actually depends on — whether the bundle is
satisfiable at a **strictly positive** tolerance, which is the only regime a real ball walk
ever reaches.

This file answers it, with everything computed rather than bounded.

## The witness

Fix a lattice point `x : EuclideanSpace ℝ (Fin (n+1))` and take the body to be the
Kannan–Vempala cube `S = roundBox x = {p | ∀ i, |pᵢ − xᵢ| ≤ 1}` about it.  Then

* `volume S = 2^(n+1)` exactly (`volume_roundBox`), so `V = 2^(n+1)`;
* the escape mass is **exactly zero** — the rounding kernel `prodTent x` vanishes off
  `roundBox x` — so `E = 0` (`setIntegral_prodTent_compl_roundBox`);
* the sampler's law is `boxAtomLaw x t = (1 − t)·uniformOn volume S + t·δₓ`: the uniform law
  contaminated with an **atom of mass `t` at the centre**.  This is not a cosmetic
  perturbation.  It is the exact shape of a ball-walk law started at a point, whose holding
  term `(1 − ℓ(x))·δₓ` never disappears
  (`Arlib.MarkovChains.ballWalk_apply_set`), and it is a law for which the *pointwise*
  hypothesis is false for **every** `ε` (`not_pointwiseClose_boxAtomLaw`).

The total-variation distance from `boxAtomLaw x t` to `uniformOn volume S` is **exactly
`t`**, not merely at most `t`: `tvLe_boxAtomLaw` gives the upper bound and
`le_of_tvLe_boxAtomLaw` shows no smaller `ε` works, because the singleton `{x}` carries mass
`t` under the law and `0` under the target.

Running `theorem2_of_tvLe_inv_volume` at tolerance `θ / V` therefore needs `t = θ/2^(n+1)`,
and returns the window

  `(1 − θ)/2^(n+1)  ≤  Pr[rnd p = x]  ≤  (1 + θ)/2^(n+1)`

(`boxAtomLaw_window`).  Both endpoints are finite, both are explicit, and they are distinct
for every `θ > 0`; at `θ < 1` the lower endpoint is positive.  Nothing here is the
degenerate instance: `boxAtomLaw x t ≠ uniformOn volume S` for `t ≠ 0`
(`boxAtomLaw_ne_uniformOn`), and the two laws differ on the set `S \ {x}`, which has full
volume `2^(n+1)` (`boxAtomLaw_apply_sdiff`).

## A second, atom-free witness

Because the atom is Lebesgue-null, a sceptic could object that `boxAtomLaw`'s non-uniformity
lives on a null set.  `boxDensityLaw x t = (1 − t)·uniformOn volume S + t·uniformOn volume
(cube x (1/2))` answers that: it is absolutely continuous
(`boxDensityLaw_absolutelyContinuous`), its density is the two-level step function that piles
an extra `t` of mass onto the inner cube — a set of volume exactly `1`
(`boxDensityLaw_apply_cube_half`) — and its distance to the uniform law is again *computed*,
exactly `t · (1 − 2^{−(n+1)})` (`tvLe_boxDensityLaw` and `le_of_tvLe_boxDensityLaw`).  It too
satisfies the theorem's hypotheses and yields the same window (`boxDensityLaw_window`).

The computation behind that number is `uniformOn_eq_mix`: `uniformOn μ S` is *itself* the
mixture `(μ A/μ S)·uniformOn μ A + (μ (S∖A)/μ S)·uniformOn μ (S∖A)`, which reads off the
distance from a sub-body's uniform law to the whole body's as exactly `1 − μ A/μ S`
(`tvLe_uniformOn_subset`).

## Main results

* `Arlib.TVWitness.mix`, `Arlib.TVWitness.tvLe_mix_of_tvLe`, `Arlib.TVWitness.le_of_tvLe_mix`,
  `Arlib.TVWitness.le_of_tvLe_mix_of_apply` — the contamination construction and its exact
  total-variation distance.
* `Arlib.TVWitness.uniformOn_eq_mix`, `Arlib.TVWitness.tvLe_uniformOn_subset` — the uniform
  law as a mixture over a sub-body, and the exact distance that follows.
* `Arlib.TVWitness.volume_cube`, `Arlib.TVWitness.volume_roundBox` — `volume (cube x c) =
  (2c)^n`, hence `volume (roundBox x) = 2^n`.
* `Arlib.TVWitness.boxAtomLaw_window`, `Arlib.TVWitness.boxDensityLaw_window` — the computed
  window at positive tolerance, for the atomic and the atom-free witness.
* `Arlib.TVWitness.not_pointwiseClose_boxAtomLaw` — the atomic law fails the pointwise
  hypothesis for every `ε`, so that witness lives strictly outside the reach of routes 1
  and 2.
* `Arlib.TVWitness.exists_nondegenerate_theorem2_of_tvLe_witness`,
  `Arlib.TVWitness.exists_atomFree_theorem2_of_tvLe_witness` — the `CLAUDE.md` §11
  witnesses, at strictly positive `ε`.

## Scope

Nothing here proves that a ball walk *reaches* total variation `θ/V`; that is a mixing
theorem, and this file is not one.  What is proved is that the hypothesis bundle of
`theorem2_of_tvLe_inv_volume` is inhabited by laws that are genuinely non-uniform, genuinely
atomic, and at a genuinely positive distance from the target — so the theorem is not
vacuous in the regime the sampler interface relies on.
-/

namespace Arlib.TVWitness

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Contaminating a law

`mix t ρ ν` is the law that draws from `ν` with probability `1 − t` and from `ρ` with
probability `t`.  It is pure data — a convex combination of two given measures — and every
statement about it below is proved, not assumed. -/

/-- **The contaminated law** `(1 − t)·ν + t·ρ`. -/
noncomputable def mix (t : ℝ≥0∞) (ρ ν : Measure Ω) : Measure Ω := (1 - t) • ν + t • ρ

@[simp] theorem mix_apply (t : ℝ≥0∞) (ρ ν : Measure Ω) (E : Set Ω) :
    mix t ρ ν E = (1 - t) * ν E + t * ρ E := by
  simp [mix]

/-- A convex combination of probability measures is a probability measure. -/
theorem isProbabilityMeasure_mix {t : ℝ≥0∞} (ht : t ≤ 1) (ρ ν : Measure Ω)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (mix t ρ ν) := by
  constructor
  rw [mix_apply, measure_univ, measure_univ, mul_one, mul_one, tsub_add_cancel_of_le ht]

/-- **Contamination scales the distance.**  If `ρ` is within `δ` of `ν`, then mixing in a
`t`-fraction of `ρ` moves the law by at most `t · δ`.  No probability-measure hypothesis is
needed: the statement is an identity about the convex combination. -/
theorem tvLe_mix_of_tvLe {t δ : ℝ≥0∞} {ρ ν : Measure Ω} (ht : t ≤ 1) (h : TVLe ρ ν δ) :
    TVLe (mix t ρ ν) ν (t * δ) := by
  intro E hE
  obtain ⟨h1, h2⟩ := h E hE
  have hsplit : ν E = (1 - t) * ν E + t * ν E := by
    rw [← add_mul, tsub_add_cancel_of_le ht, one_mul]
  refine ⟨?_, ?_⟩
  · rw [mix_apply]
    calc (1 - t) * ν E + t * ρ E ≤ (1 - t) * ν E + t * (ν E + δ) := by gcongr
      _ = (1 - t) * ν E + t * ν E + t * δ := by ring
      _ = ν E + t * δ := by rw [← hsplit]
  · rw [mix_apply]
    calc ν E = (1 - t) * ν E + t * ν E := hsplit
      _ ≤ (1 - t) * ν E + t * (ρ E + δ) := by gcongr
      _ = (1 - t) * ν E + t * ρ E + t * δ := by ring

/-- The crude form: contamination by a `t`-fraction of anything moves a probability measure
by at most `t`. -/
theorem tvLe_mix {t : ℝ≥0∞} {ρ ν : Measure Ω} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ν] (ht : t ≤ 1) : TVLe (mix t ρ ν) ν t := by
  simpa using tvLe_mix_of_tvLe ht (tvLe_one ρ ν)

/-- **The distance is exactly `t`, not less.**  If some measurable `E` is certain under the
contaminant and null under the target, then every valid total-variation bound for
`mix t ρ ν` against `ν` is at least `t`.  Together with `tvLe_mix` this *computes* the
distance rather than bounding it. -/
theorem le_of_tvLe_mix {t ε : ℝ≥0∞} {ρ ν : Measure Ω} {E : Set Ω} (hE : MeasurableSet E)
    (hρ : ρ E = 1) (hν : ν E = 0) (h : TVLe (mix t ρ ν) ν ε) : t ≤ ε := by
  simpa [hρ, hν] using (h E hE).1

/-- **The distance is exactly `t · (1 − ν E)`.**  The sharper companion of
`le_of_tvLe_mix`: when the contaminant is certain on `E` but the target only gives `E` mass
`ν E`, contaminating by a `t`-fraction raises the mass of `E` by exactly `t · (1 − ν E)`, so
no tolerance below that is valid.  Taking `ν E = 0` recovers `le_of_tvLe_mix`. -/
theorem le_of_tvLe_mix_of_apply {t ε : ℝ≥0∞} {ρ ν : Measure Ω} [IsProbabilityMeasure ν]
    {E : Set Ω} (hE : MeasurableSet E) (ht : t ≤ 1) (hρ : ρ E = 1)
    (h : TVLe (mix t ρ ν) ν ε) : t * (1 - ν E) ≤ ε := by
  have hle : ν E ≤ 1 := prob_le_one
  have hone : ν E + (1 - ν E) = 1 := add_tsub_cancel_of_le hle
  have key : mix t ρ ν E = ν E + t * (1 - ν E) := by
    rw [mix_apply, hρ, mul_one]
    calc (1 - t) * ν E + t = (1 - t) * ν E + t * (ν E + (1 - ν E)) := by rw [hone, mul_one]
      _ = (1 - t) * ν E + t * ν E + t * (1 - ν E) := by ring
      _ = ν E + t * (1 - ν E) := by rw [← add_mul, tsub_add_cancel_of_le ht, one_mul]
  have hmain := (h E hE).1
  rw [key] at hmain
  exact ENNReal.le_of_add_le_add_left (measure_ne_top ν E) hmain

/-- **The uniform law on `S` is itself a mixture.**  For `A ⊆ S` of positive finite measure
with a positive-measure complement in `S`,

  `uniformOn μ S = (μ A / μ S) · uniformOn μ A + (μ (S \ A) / μ S) · uniformOn μ (S \ A)`,

written in `mix` form with contamination weight `1 − uniformOn μ S A`.  Reading it backwards
this *computes* the total-variation distance from `uniformOn μ A` to `uniformOn μ S`: it is
exactly `1 − uniformOn μ S A` (`tvLe_uniformOn_subset`). -/
theorem uniformOn_eq_mix (μ : Measure Ω) {S A : Set Ω} (hS : MeasurableSet S)
    (hA : MeasurableSet A) (hAS : A ⊆ S) (hA0 : μ A ≠ 0) (hAtop : μ A ≠ ⊤)
    (hD0 : μ (S \ A) ≠ 0) (hDtop : μ (S \ A) ≠ ⊤) :
    uniformOn μ S = mix (1 - uniformOn μ S A) (uniformOn μ (S \ A)) (uniformOn μ A) := by
  have hD : MeasurableSet (S \ A) := hS.diff hA
  have hSsplit : μ A + μ (S \ A) = μ S := by
    have := measure_inter_add_sdiff (μ := μ) S hA
    rwa [Set.inter_eq_right.2 hAS] at this
  have hStop : μ S ≠ ⊤ := by
    rw [← hSsplit]; exact ENNReal.add_ne_top.2 ⟨hAtop, hDtop⟩
  have hS0 : μ S ≠ 0 := fun h => hA0 (measure_mono_null hAS h)
  haveI : IsProbabilityMeasure (uniformOn μ S) := isProbabilityMeasure_uniformOn μ hS0 hStop
  have hSA : uniformOn μ S A = μ A / μ S := by
    rw [uniformOn_apply μ hS hA, Set.inter_eq_left.2 hAS]
  have hsum : μ A / μ S + μ (S \ A) / μ S = 1 := by
    rw [ENNReal.div_add_div_same, hSsplit, ENNReal.div_self hS0 hStop]
  have hsum' : μ (S \ A) / μ S + μ A / μ S = 1 := by rw [add_comm]; exact hsum
  have hAdivtop : μ A / μ S ≠ ⊤ := ENNReal.div_ne_top hAtop hS0
  have hcompl : (1 : ℝ≥0∞) - μ A / μ S = μ (S \ A) / μ S :=
    ENNReal.sub_eq_of_eq_add hAdivtop hsum'.symm
  have hinner : (1 : ℝ≥0∞) - (1 - uniformOn μ S A) = uniformOn μ S A :=
    ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one
  have hcancel : ∀ a y : ℝ≥0∞, a ≠ 0 → a ≠ ⊤ → a / μ S * (y / a) = y / μ S := by
    intro a y ha hatop
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    calc a * (μ S)⁻¹ * (y * a⁻¹) = a * a⁻¹ * (y * (μ S)⁻¹) := by ring
      _ = y * (μ S)⁻¹ := by rw [ENNReal.mul_inv_cancel ha hatop, one_mul]
  ext E hE
  have hset1 : E ∩ S ∩ A = E ∩ A := by
    ext p
    simp only [Set.mem_inter_iff]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hAS h.2⟩, h.2⟩⟩
  have hset2 : (E ∩ S) \ A = E ∩ (S \ A) := by
    ext p
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hsplitE : μ (E ∩ A) + μ (E ∩ (S \ A)) = μ (E ∩ S) := by
    have := measure_inter_add_sdiff (μ := μ) (E ∩ S) hA
    rwa [hset1, hset2] at this
  rw [mix_apply, hinner, hSA, hcompl, uniformOn_apply μ hS hE, uniformOn_apply μ hA hE,
    uniformOn_apply μ hD hE, hcancel _ _ hA0 hAtop, hcancel _ _ hD0 hDtop,
    ENNReal.div_add_div_same, hsplitE]

/-- **The distance from a sub-body's uniform law to the whole body's is exactly
`1 − μ A / μ S`.**  Immediate from `uniformOn_eq_mix`: the target *is* the sub-body's law
contaminated by a `(1 − μ A / μ S)`-fraction of the uniform law on `S \ A`. -/
theorem tvLe_uniformOn_subset (μ : Measure Ω) {S A : Set Ω} (hS : MeasurableSet S)
    (hA : MeasurableSet A) (hAS : A ⊆ S) (hA0 : μ A ≠ 0) (hAtop : μ A ≠ ⊤)
    (hD0 : μ (S \ A) ≠ 0) (hDtop : μ (S \ A) ≠ ⊤) :
    TVLe (uniformOn μ A) (uniformOn μ S) (1 - uniformOn μ S A) := by
  have hD : MeasurableSet (S \ A) := hS.diff hA
  haveI : IsProbabilityMeasure (uniformOn μ A) := isProbabilityMeasure_uniformOn μ hA0 hAtop
  haveI : IsProbabilityMeasure (uniformOn μ (S \ A)) :=
    isProbabilityMeasure_uniformOn μ hD0 hDtop
  have hdec := uniformOn_eq_mix μ hS hA hAS hA0 hAtop hD0 hDtop
  have := tvLe_mix (ρ := uniformOn μ (S \ A)) (ν := uniformOn μ A)
    (t := 1 - uniformOn μ S A) (by exact tsub_le_self)
  rw [← hdec] at this
  exact this.symm

/-- A convex combination of two laws dominated by `μ` is dominated by `μ`. -/
theorem mix_absolutelyContinuous {t : ℝ≥0∞} {ρ ν μ : Measure Ω} (hρ : ρ ≪ μ) (hν : ν ≪ μ) :
    mix t ρ ν ≪ μ := fun s hs => by
  rw [mix_apply, hν hs, hρ hs, mul_zero, mul_zero, add_zero]

/-- Contamination by a contaminant that is singular against the target really does change
the law: `mix t ρ ν = ν` forces `t = 0`. -/
theorem mix_ne_of_ne_zero {t : ℝ≥0∞} {ρ ν : Measure Ω} {E : Set Ω} (hE : MeasurableSet E)
    (hρ : ρ E = 1) (hν : ν E = 0) (ht : t ≠ 0) : mix t ρ ν ≠ ν := by
  intro hEq
  have h0 : TVLe (mix t ρ ν) ν 0 := by rw [hEq]; exact TVLe.refl ν
  exact ht (nonpos_iff_eq_zero.1 (le_of_tvLe_mix hE hρ hν h0))

/-! ## The body: the Kannan–Vempala cube, whose volume is exact

Taking the body to be the rounding kernel's own support box makes both of the theorem's
numerical inputs exact rather than estimated: the volume is `2^n` and the escape mass is
`0`. -/

section Box

open Arlib.Lattice.Rounding

variable {n : ℕ}

/-- The axis-aligned cube of half-width `c` about `x`.  At `c = 1` this is the
Kannan–Vempala box `Arlib.Lattice.Rounding.roundBox x` (`cube_one`). -/
def cube (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {p | ∀ i, |p i - x i| ≤ c}

theorem cube_one (x : EuclideanSpace ℝ (Fin n)) : cube x 1 = roundBox x := rfl

theorem measurableSet_cube (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    MeasurableSet (cube x c) := by
  have hrw : cube x c = ⋂ i, {p : EuclideanSpace ℝ (Fin n) | |p i - x i| ≤ c} := by
    ext p; simp [cube]
  rw [hrw]
  refine MeasurableSet.iInter fun i => measurableSet_le ?_ measurable_const
  exact continuous_abs.measurable.comp ((measurable_coord i).sub measurable_const)

theorem cube_mono (x : EuclideanSpace ℝ (Fin n)) {c d : ℝ} (hcd : c ≤ d) :
    cube x c ⊆ cube x d := fun _ hp i => (hp i).trans hcd

/-- **The cube's volume is exactly `(2c)ⁿ`.**  `cube x c` is the preimage of the product box
`∏ᵢ [xᵢ − c, xᵢ + c]` under the volume-preserving identification of `EuclideanSpace ℝ (Fin n)`
with `Fin n → ℝ`, and each factor has length `2c`. -/
theorem volume_cube (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    volume (cube x c) = ENNReal.ofReal (2 * c) ^ n := by
  have hpre : cube x c
      = (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ⁻¹'
        (Set.univ.pi fun i => Set.Icc (x i - c) (x i + c)) := by
    ext p
    simp only [cube, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      forall_const, Set.mem_Icc, abs_le]
    constructor
    · intro hp i
      exact ⟨by linarith [(hp i).1], by linarith [(hp i).2]⟩
    · intro hp i
      exact ⟨by linarith [(hp i).1], by linarith [(hp i).2]⟩
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet,
    volume_pi_pi]
  have hfac : ∀ i : Fin n,
      volume (Set.Icc (x i - c) (x i + c)) = ENNReal.ofReal (2 * c) := by
    intro i
    rw [Real.volume_Icc]
    congr 1
    ring
  simp [hfac]

/-- The half-width-`½` cube has volume exactly `1`, in every dimension. -/
theorem volume_cube_half (x : EuclideanSpace ℝ (Fin n)) : volume (cube x (1 / 2)) = 1 := by
  rw [volume_cube]
  norm_num

/-- **The Kannan–Vempala box has volume exactly `2ⁿ`.** -/
theorem volume_roundBox (x : EuclideanSpace ℝ (Fin n)) :
    volume (roundBox x) = 2 ^ n := by
  rw [← cube_one, volume_cube]
  norm_num

theorem volume_roundBox_ne_zero (x : EuclideanSpace ℝ (Fin n)) : volume (roundBox x) ≠ 0 := by
  rw [volume_roundBox]
  exact pow_ne_zero _ two_ne_zero

theorem volume_roundBox_ne_top (x : EuclideanSpace ℝ (Fin n)) : volume (roundBox x) ≠ ⊤ := by
  rw [volume_roundBox]
  exact ENNReal.pow_ne_top (by norm_num)

theorem volume_roundBox_toReal (x : EuclideanSpace ℝ (Fin n)) :
    (volume (roundBox x)).toReal = 2 ^ n := by
  rw [volume_roundBox]
  simp

theorem cube_half_subset_roundBox (x : EuclideanSpace ℝ (Fin n)) :
    cube x (1 / 2) ⊆ roundBox x := by
  rw [← cube_one]
  exact cube_mono x (by norm_num)

theorem one_le_two_pow (m : ℕ) : (1 : ℝ≥0∞) ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    calc (1 : ℝ≥0∞) = 1 * 1 := (mul_one 1).symm
      _ ≤ 2 ^ k * 2 := mul_le_mul' ih one_le_two

theorem one_lt_two_pow_succ (m : ℕ) : (1 : ℝ≥0∞) < 2 ^ (m + 1) := by
  have h2 : (2 : ℝ≥0∞) ≤ 2 ^ (m + 1) := by
    rw [pow_succ]
    calc (2 : ℝ≥0∞) = 1 * 2 := (one_mul 2).symm
      _ ≤ 2 ^ m * 2 := mul_le_mul' (one_le_two_pow m) le_rfl
  exact lt_of_lt_of_le (by norm_num) h2

/-- **The escape mass is exactly zero.**  The rounding kernel vanishes off its own box. -/
theorem setIntegral_prodTent_compl_roundBox (x : EuclideanSpace ℝ (Fin n)) :
    ∫ p in (roundBox x)ᶜ, prodTent x p = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun _ hp => prodTent_eq_zero_of_notMem hp

end Box

/-! ## The witness law: uniform on the cube, plus an atom at the centre -/

section Witness

open Arlib.Lattice.Rounding Arlib.PointwiseRoute

variable {n : ℕ}

/-- **The witness law.**  `(1 − t)·uniformOn volume (roundBox x) + t·δₓ`: uniform on the
Kannan–Vempala cube, contaminated by an atom of mass `t` at its centre.  This is the shape
of a ball-walk law started at a point, and it is *not* absolutely continuous, so no
pointwise hypothesis can hold of it. -/
noncomputable def boxAtomLaw (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ≥0∞) :
    Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
  mix t (Measure.dirac x) (uniformOn volume (roundBox x))

instance isProbabilityMeasure_uniformOn_roundBox (x : EuclideanSpace ℝ (Fin (n + 1))) :
    IsProbabilityMeasure (uniformOn volume (roundBox x)) :=
  isProbabilityMeasure_uniformOn volume (volume_roundBox_ne_zero x) (volume_roundBox_ne_top x)

theorem isProbabilityMeasure_boxAtomLaw (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ≥0∞}
    (ht : t ≤ 1) : IsProbabilityMeasure (boxAtomLaw x t) :=
  isProbabilityMeasure_mix ht _ _

/-- The centre is an atom of mass exactly `t`. -/
theorem boxAtomLaw_singleton (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ≥0∞) :
    boxAtomLaw x t {x} = t := by
  simp [boxAtomLaw, uniformOn_singleton_eq_zero volume (roundBox x) (measure_singleton x)]

/-- The target gives the centre no mass at all. -/
theorem uniformOn_roundBox_singleton (x : EuclideanSpace ℝ (Fin (n + 1))) :
    uniformOn volume (roundBox x) {x} = 0 :=
  uniformOn_singleton_eq_zero volume (roundBox x) (measure_singleton x)

/-- **Upper bound on the distance.** -/
theorem tvLe_boxAtomLaw (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ≥0∞} (ht : t ≤ 1) :
    TVLe (boxAtomLaw x t) (uniformOn volume (roundBox x)) t :=
  tvLe_mix ht

/-- **Lower bound on the distance**: no tolerance below `t` is valid.  With
`tvLe_boxAtomLaw` this says the total-variation distance is *exactly* `t`. -/
theorem le_of_tvLe_boxAtomLaw (x : EuclideanSpace ℝ (Fin (n + 1))) {t ε : ℝ≥0∞}
    (h : TVLe (boxAtomLaw x t) (uniformOn volume (roundBox x)) ε) : t ≤ ε :=
  le_of_tvLe_mix (measurableSet_singleton x) (by simp)
    (uniformOn_roundBox_singleton x) h

/-- **The witness is not the degenerate one.** -/
theorem boxAtomLaw_ne_uniformOn (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ≥0∞} (ht : t ≠ 0) :
    boxAtomLaw x t ≠ uniformOn volume (roundBox x) :=
  mix_ne_of_ne_zero (measurableSet_singleton x) (by simp)
    (uniformOn_roundBox_singleton x) ht

/-- **The two laws differ on a set of full Lebesgue measure.**  On `S \ {x}` — which has
volume `2^(n+1)`, the whole of the body — the witness puts mass `1 − t` and the target
puts mass `1`. -/
theorem boxAtomLaw_apply_sdiff (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ≥0∞) :
    volume (roundBox x \ {x}) = 2 ^ (n + 1) ∧
      uniformOn volume (roundBox x) (roundBox x \ {x}) = 1 ∧
      boxAtomLaw x t (roundBox x \ {x}) = 1 - t := by
  have hmeas : MeasurableSet (roundBox x \ {x}) :=
    (measurableSet_roundBox x).diff (measurableSet_singleton x)
  have hvol : volume (roundBox x \ {x}) = volume (roundBox x) := by
    exact measure_sdiff_null (measure_singleton x)
  have hunif : uniformOn volume (roundBox x) (roundBox x \ {x}) = 1 := by
    rw [uniformOn_apply volume (measurableSet_roundBox x) hmeas,
      Set.inter_eq_left.2 Set.sdiff_subset, hvol,
      ENNReal.div_self (volume_roundBox_ne_zero x) (volume_roundBox_ne_top x)]
  refine ⟨by rw [hvol, volume_roundBox], hunif, ?_⟩
  rw [boxAtomLaw, mix_apply, hunif, mul_one, Measure.dirac_apply' _ hmeas]
  simp

/-- **The witness is invisible to the pointwise route.**  For every `ε`, including `⊤`, the
law `boxAtomLaw x t` with `t ≠ 0` is *not* pointwise `ε`-close to the uniform law: it has an
atom at a Lebesgue-null point.  So this witness is not merely a non-degenerate instance of
the total-variation hypothesis, it is one that the pointwise hypothesis cannot describe at
all — which is the whole reason `Ttc.KV97Sampler` carries `law_tv` and not a pointwise
field. -/
theorem not_pointwiseClose_boxAtomLaw (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ≥0∞}
    (ht : t ≠ 0) (ε : ℝ≥0∞) :
    ¬ Arlib.MarkovChains.PointwiseClose (boxAtomLaw x t) (uniformOn volume (roundBox x)) ε :=
  not_pointwiseClose_uniformOn_of_atom (measure_singleton x)
    (by rw [boxAtomLaw_singleton]; exact ht) ε

/-! ### The window, computed -/

/-- **The non-degenerate witness, with the window computed.**

For every lattice point `x` and every tolerance `0 ≤ θ ≤ 2^(n+1)`, the law
`boxAtomLaw x (ENNReal.ofReal (θ / 2^(n+1)))` — uniform on the cube `roundBox x` of volume
`2^(n+1)`, contaminated by an atom of mass `θ/2^(n+1)` at `x` — satisfies every hypothesis of
`Arlib.PointwiseRoute.theorem2_of_tvLe_inv_volume` and yields the window

  `(1 − θ)/2^(n+1)  ≤  Pr[rnd p = x]  ≤  (1 + θ)/2^(n+1)`.

The escape coefficient is `E = 0` because the rounding kernel's support is exactly the body,
so the window is the one the theorem promises with no slack absorbed into `E`. -/
theorem boxAtomLaw_window (x : EuclideanSpace ℝ (Fin (n + 1))) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 2 ^ (n + 1)) :
    (1 - θ) / 2 ^ (n + 1)
        ≤ ∫ p, prodTent x p ∂(boxAtomLaw x (ENNReal.ofReal (θ / 2 ^ (n + 1)))) ∧
      ∫ p, prodTent x p ∂(boxAtomLaw x (ENNReal.ofReal (θ / 2 ^ (n + 1))))
        ≤ (1 + θ) / 2 ^ (n + 1) := by
  have hVpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have ht1 : ENNReal.ofReal (θ / 2 ^ (n + 1)) ≤ 1 :=
    ENNReal.ofReal_le_one.2 ((div_le_one hVpos).2 hθ1)
  haveI := isProbabilityMeasure_boxAtomLaw x ht1
  have hwin := theorem2_of_tvLe_inv_volume (S := roundBox x)
    (μ := boxAtomLaw x (ENNReal.ofReal (θ / 2 ^ (n + 1)))) (V := 2 ^ (n + 1)) (E := 0)
    (θ := θ) (x := x) (measurableSet_roundBox x) (volume_roundBox_ne_zero x)
    (volume_roundBox_ne_top x) (volume_roundBox_toReal x)
    (tvLe_boxAtomLaw x ht1) hθ0 (le_of_eq (setIntegral_prodTent_compl_roundBox x))
  simpa using hwin

/-- **The distance really is positive.**  At `0 < θ` the witness sits at total-variation
distance exactly `θ / 2^(n+1) > 0` from the uniform law — the hypothesis is met at a
strictly positive tolerance, and at no smaller one. -/
theorem tvDist_boxAtomLaw_eq (x : EuclideanSpace ℝ (Fin (n + 1))) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 2 ^ (n + 1)) :
    0 < ENNReal.ofReal (θ / 2 ^ (n + 1)) ∧
      TVLe (boxAtomLaw x (ENNReal.ofReal (θ / 2 ^ (n + 1)))) (uniformOn volume (roundBox x))
        (ENNReal.ofReal (θ / 2 ^ (n + 1))) ∧
      ∀ ε : ℝ≥0∞,
        TVLe (boxAtomLaw x (ENNReal.ofReal (θ / 2 ^ (n + 1))))
            (uniformOn volume (roundBox x)) ε →
          ENNReal.ofReal (θ / 2 ^ (n + 1)) ≤ ε := by
  have hVpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have ht1 : ENNReal.ofReal (θ / 2 ^ (n + 1)) ≤ 1 :=
    ENNReal.ofReal_le_one.2 ((div_le_one hVpos).2 hθ1)
  exact ⟨ENNReal.ofReal_pos.2 (div_pos hθ0 hVpos), tvLe_boxAtomLaw x ht1,
    fun _ h => le_of_tvLe_boxAtomLaw x h⟩

/-! ### A second witness, with no atom at all

The atom in `boxAtomLaw` is what puts it beyond the reach of the pointwise route, but it
also means its non-uniformity is carried by a Lebesgue-null set.  The law below has no atom:
it is absolutely continuous with respect to `volume` (`boxDensityLaw_absolutelyContinuous`),
its density is the two-level step function that is heavier on the inner cube
`cube x (1/2)` — a set of volume exactly `1` — than on the rest of the body, and its
distance to the uniform law is again computed exactly. -/

/-- **The density-perturbed witness.**  `(1 − t)·uniformOn volume (roundBox x) +
t·uniformOn volume (cube x (1/2))`: uniform on the body, with an extra `t` of mass piled
onto the concentric half-width cube.  Absolutely continuous, genuinely non-uniform. -/
noncomputable def boxDensityLaw (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ≥0∞) :
    Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
  mix t (uniformOn volume (cube x (1 / 2))) (uniformOn volume (roundBox x))

theorem volume_cube_half_ne_zero (x : EuclideanSpace ℝ (Fin (n + 1))) :
    volume (cube x (1 / 2)) ≠ 0 := by rw [volume_cube_half]; exact one_ne_zero

theorem volume_cube_half_ne_top (x : EuclideanSpace ℝ (Fin (n + 1))) :
    volume (cube x (1 / 2)) ≠ ⊤ := by rw [volume_cube_half]; exact ENNReal.one_ne_top

theorem volume_roundBox_sdiff_cube_half (x : EuclideanSpace ℝ (Fin (n + 1))) :
    volume (roundBox x \ cube x (1 / 2)) = 2 ^ (n + 1) - 1 := by
  rw [measure_sdiff (cube_half_subset_roundBox x)
      (measurableSet_cube x (1 / 2)).nullMeasurableSet (volume_cube_half_ne_top x),
    volume_roundBox, volume_cube_half]

theorem volume_roundBox_sdiff_cube_half_ne_zero (x : EuclideanSpace ℝ (Fin (n + 1))) :
    volume (roundBox x \ cube x (1 / 2)) ≠ 0 := by
  rw [volume_roundBox_sdiff_cube_half]
  intro h
  exact absurd (tsub_eq_zero_iff_le.1 h) (not_le.2 (one_lt_two_pow_succ n))

theorem volume_roundBox_sdiff_cube_half_ne_top (x : EuclideanSpace ℝ (Fin (n + 1))) :
    volume (roundBox x \ cube x (1 / 2)) ≠ ⊤ := by
  rw [volume_roundBox_sdiff_cube_half]
  exact ne_top_of_le_ne_top (ENNReal.pow_ne_top (by norm_num)) tsub_le_self

/-- Under the uniform law the inner cube has mass exactly `2^{-(n+1)}`. -/
theorem uniformOn_roundBox_cube_half (x : EuclideanSpace ℝ (Fin (n + 1))) :
    uniformOn volume (roundBox x) (cube x (1 / 2)) = (2 ^ (n + 1))⁻¹ := by
  rw [uniformOn_apply volume (measurableSet_roundBox x) (measurableSet_cube x (1 / 2)),
    Set.inter_eq_left.2 (cube_half_subset_roundBox x), volume_cube_half, volume_roundBox,
    one_div]

/-- **The distance from the inner cube's uniform law to the body's is exactly
`1 − 2^{-(n+1)}`.** -/
theorem tvLe_uniformOn_cube_half (x : EuclideanSpace ℝ (Fin (n + 1))) :
    TVLe (uniformOn volume (cube x (1 / 2))) (uniformOn volume (roundBox x))
      (1 - (2 ^ (n + 1))⁻¹) := by
  have h := tvLe_uniformOn_subset (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
    (measurableSet_roundBox x) (measurableSet_cube x (1 / 2)) (cube_half_subset_roundBox x)
    (volume_cube_half_ne_zero x) (volume_cube_half_ne_top x)
    (volume_roundBox_sdiff_cube_half_ne_zero x) (volume_roundBox_sdiff_cube_half_ne_top x)
  rwa [uniformOn_roundBox_cube_half] at h

theorem isProbabilityMeasure_boxDensityLaw (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ≥0∞}
    (ht : t ≤ 1) : IsProbabilityMeasure (boxDensityLaw x t) := by
  haveI : IsProbabilityMeasure (uniformOn volume (cube x (1 / 2))) :=
    isProbabilityMeasure_uniformOn volume (volume_cube_half_ne_zero x)
      (volume_cube_half_ne_top x)
  exact isProbabilityMeasure_mix ht _ _

/-- **No atom anywhere**: the density witness is absolutely continuous. -/
theorem boxDensityLaw_absolutelyContinuous (x : EuclideanSpace ℝ (Fin (n + 1)))
    (t : ℝ≥0∞) : boxDensityLaw x t ≪ volume :=
  mix_absolutelyContinuous (uniformOn_absolutelyContinuous volume _)
    (uniformOn_absolutelyContinuous volume _)

/-- **The density really is perturbed.**  On the inner cube — a set of volume exactly `1` —
the witness puts mass `(1 − t)·2^{-(n+1)} + t`, against the uniform law's `2^{-(n+1)}`. -/
theorem boxDensityLaw_apply_cube_half (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ≥0∞) :
    volume (cube x (1 / 2)) = 1 ∧
      uniformOn volume (roundBox x) (cube x (1 / 2)) = (2 ^ (n + 1))⁻¹ ∧
      boxDensityLaw x t (cube x (1 / 2)) = (1 - t) * (2 ^ (n + 1))⁻¹ + t := by
  refine ⟨volume_cube_half x, uniformOn_roundBox_cube_half x, ?_⟩
  rw [boxDensityLaw, mix_apply, uniformOn_roundBox_cube_half,
    uniformOn_self volume (measurableSet_cube x (1 / 2)) (volume_cube_half_ne_zero x)
      (volume_cube_half_ne_top x), mul_one]

/-- **Upper bound on the distance**: exactly `t · (1 − 2^{-(n+1)})`. -/
theorem tvLe_boxDensityLaw (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ≥0∞} (ht : t ≤ 1) :
    TVLe (boxDensityLaw x t) (uniformOn volume (roundBox x))
      (t * (1 - (2 ^ (n + 1))⁻¹)) :=
  tvLe_mix_of_tvLe ht (tvLe_uniformOn_cube_half x)

/-- **Lower bound on the distance**: no smaller tolerance is valid, so the distance is
*exactly* `t · (1 − 2^{-(n+1)})`. -/
theorem le_of_tvLe_boxDensityLaw (x : EuclideanSpace ℝ (Fin (n + 1))) {t ε : ℝ≥0∞}
    (ht : t ≤ 1) (h : TVLe (boxDensityLaw x t) (uniformOn volume (roundBox x)) ε) :
    t * (1 - (2 ^ (n + 1))⁻¹) ≤ ε := by
  have h' := le_of_tvLe_mix_of_apply (E := cube x (1 / 2)) (measurableSet_cube x (1 / 2)) ht
    (uniformOn_self volume (measurableSet_cube x (1 / 2)) (volume_cube_half_ne_zero x)
      (volume_cube_half_ne_top x)) h
  rwa [uniformOn_roundBox_cube_half] at h'

/-- The distance is strictly positive whenever the perturbation is. -/
theorem tvDist_boxDensityLaw_pos {t : ℝ≥0∞} (ht0 : t ≠ 0) :
    0 < t * (1 - ((2 : ℝ≥0∞) ^ (n + 1))⁻¹) := by
  have hlt : ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ < 1 := ENNReal.inv_lt_one.2 (one_lt_two_pow_succ n)
  have hne : (1 : ℝ≥0∞) - ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ ≠ 0 := fun h =>
    absurd (tsub_eq_zero_iff_le.1 h) (not_le.2 hlt)
  exact pos_iff_ne_zero.2 (mul_ne_zero ht0 hne)

/-- The atom-free witness is not the degenerate one either. -/
theorem boxDensityLaw_ne_uniformOn (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ≥0∞}
    (ht : t ≤ 1) (ht0 : t ≠ 0) :
    boxDensityLaw x t ≠ uniformOn volume (roundBox x) := by
  intro hEq
  have h0 : TVLe (boxDensityLaw x t) (uniformOn volume (roundBox x)) 0 := by
    rw [hEq]; exact TVLe.refl _
  exact (tvDist_boxDensityLaw_pos ht0).ne'
    (nonpos_iff_eq_zero.1 (le_of_tvLe_boxDensityLaw x ht h0))

/-- **The atom-free witness also satisfies `theorem2_of_tvLe_inv_volume`, with the same
computed window.**  Its distance to the uniform law is `θ/2^(n+1) · (1 − 2^{-(n+1)})`, which
is strictly positive and strictly below the tolerance `θ/2^(n+1)` the theorem is run at — so
the hypothesis is met with room to spare by a law that is not the target, has no atom, and
has an explicitly perturbed density. -/
theorem boxDensityLaw_window (x : EuclideanSpace ℝ (Fin (n + 1))) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 2 ^ (n + 1)) :
    (1 - θ) / 2 ^ (n + 1)
        ≤ ∫ p, prodTent x p ∂(boxDensityLaw x (ENNReal.ofReal (θ / 2 ^ (n + 1)))) ∧
      ∫ p, prodTent x p ∂(boxDensityLaw x (ENNReal.ofReal (θ / 2 ^ (n + 1))))
        ≤ (1 + θ) / 2 ^ (n + 1) := by
  have hVpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have ht1 : ENNReal.ofReal (θ / 2 ^ (n + 1)) ≤ 1 :=
    ENNReal.ofReal_le_one.2 ((div_le_one hVpos).2 hθ1)
  haveI := isProbabilityMeasure_boxDensityLaw x ht1
  have hmono : ENNReal.ofReal (θ / 2 ^ (n + 1)) * (1 - ((2 : ℝ≥0∞) ^ (n + 1))⁻¹)
      ≤ ENNReal.ofReal (θ / 2 ^ (n + 1)) := by
    calc ENNReal.ofReal (θ / 2 ^ (n + 1)) * (1 - ((2 : ℝ≥0∞) ^ (n + 1))⁻¹)
        ≤ ENNReal.ofReal (θ / 2 ^ (n + 1)) * 1 := by gcongr; exact tsub_le_self
      _ = ENNReal.ofReal (θ / 2 ^ (n + 1)) := mul_one _
  have hwin := theorem2_of_tvLe_inv_volume (S := roundBox x)
    (μ := boxDensityLaw x (ENNReal.ofReal (θ / 2 ^ (n + 1)))) (V := 2 ^ (n + 1)) (E := 0)
    (θ := θ) (x := x) (measurableSet_roundBox x) (volume_roundBox_ne_zero x)
    (volume_roundBox_ne_top x) (volume_roundBox_toReal x)
    ((tvLe_boxDensityLaw x ht1).mono hmono) hθ0
    (le_of_eq (setIntegral_prodTent_compl_roundBox x))
  simpa using hwin

/-- **The `CLAUDE.md` §11 witness at strictly positive `ε`.**

Every hypothesis of `Arlib.PointwiseRoute.theorem2_of_tvLe_inv_volume` holds simultaneously
for a body of exactly known volume `V = 2^(n+1)`, escape coefficient exactly `E = 0`, and a
law `μ` that

* is **not** the uniform law (`hne`), and differs from it on a set of full volume;
* is at total-variation distance **exactly** `ENNReal.ofReal (θ/V) > 0` — the bound holds
  (`htv`) and no smaller tolerance does (`hexact`);

and the conclusion is the two-sided window `[(1 − θ)/2^(n+1), (1 + θ)/2^(n+1)]`, whose
endpoints are finite and distinct.

This is the statement `exists_theorem2_of_tvLe_witness` does not make: there the law is the
target itself and `ε = 0`. -/
theorem exists_nondegenerate_theorem2_of_tvLe_witness (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 2 ^ (n + 1)) :
    ∃ (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (V E : ℝ),
      IsProbabilityMeasure μ ∧ MeasurableSet S ∧ volume S ≠ 0 ∧ volume S ≠ ⊤ ∧
        (volume S).toReal = V ∧ V = 2 ^ (n + 1) ∧ E = 0 ∧
        TVLe μ (uniformOn volume S) (ENNReal.ofReal (θ / V)) ∧
        (∫ p in Sᶜ, prodTent x p) ≤ E ∧
        0 < ENNReal.ofReal (θ / V) ∧
        μ ≠ uniformOn volume S ∧
        (∀ ε : ℝ≥0∞, TVLe μ (uniformOn volume S) ε → ENNReal.ofReal (θ / V) ≤ ε) ∧
        (∀ ε : ℝ≥0∞, ¬ Arlib.MarkovChains.PointwiseClose μ (uniformOn volume S) ε) ∧
        ((1 - (E + θ)) / V ≤ ∫ p, prodTent x p ∂μ ∧
          (∫ p, prodTent x p ∂μ) ≤ (1 + θ) / V) := by
  have hVpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have ht1 : ENNReal.ofReal (θ / 2 ^ (n + 1)) ≤ 1 :=
    ENNReal.ofReal_le_one.2 ((div_le_one hVpos).2 hθ1)
  have ht0 : ENNReal.ofReal (θ / 2 ^ (n + 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (div_pos hθ0 hVpos)).ne'
  haveI := isProbabilityMeasure_boxAtomLaw x ht1
  refine ⟨roundBox x, boxAtomLaw x (ENNReal.ofReal (θ / 2 ^ (n + 1))), 2 ^ (n + 1), 0,
    inferInstance, measurableSet_roundBox x, volume_roundBox_ne_zero x,
    volume_roundBox_ne_top x, volume_roundBox_toReal x, rfl, rfl,
    tvLe_boxAtomLaw x ht1, le_of_eq (setIntegral_prodTent_compl_roundBox x),
    ENNReal.ofReal_pos.2 (div_pos hθ0 hVpos), boxAtomLaw_ne_uniformOn x ht0,
    fun _ h => le_of_tvLe_boxAtomLaw x h, not_pointwiseClose_boxAtomLaw x ht0, ?_⟩
  simpa using boxAtomLaw_window x hθ0.le hθ1

/-- **The same, by an atom-free witness.**  Identical body, volume and escape coefficient,
but the law is absolutely continuous with respect to `volume` (`hac`) — a genuine density
perturbation, not a point mass.  Its exact distance to the target is the `d` produced here:
strictly positive, no smaller tolerance valid, and below the tolerance `θ/V` at which the
theorem is run.

Between this and `exists_nondegenerate_theorem2_of_tvLe_witness` the hypothesis bundle is
shown inhabited on both sides of the absolutely-continuous / atomic divide, at strictly
positive total variation, which is what the sampler interface needs. -/
theorem exists_atomFree_theorem2_of_tvLe_witness (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 2 ^ (n + 1)) :
    ∃ (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (V E : ℝ) (d : ℝ≥0∞),
      IsProbabilityMeasure μ ∧ MeasurableSet S ∧ volume S ≠ 0 ∧ volume S ≠ ⊤ ∧
        (volume S).toReal = V ∧ V = 2 ^ (n + 1) ∧ E = 0 ∧
        μ ≪ volume ∧
        TVLe μ (uniformOn volume S) (ENNReal.ofReal (θ / V)) ∧
        (∫ p in Sᶜ, prodTent x p) ≤ E ∧
        0 < d ∧ d ≤ ENNReal.ofReal (θ / V) ∧ TVLe μ (uniformOn volume S) d ∧
        (∀ ε : ℝ≥0∞, TVLe μ (uniformOn volume S) ε → d ≤ ε) ∧
        μ ≠ uniformOn volume S ∧
        ((1 - (E + θ)) / V ≤ ∫ p, prodTent x p ∂μ ∧
          (∫ p, prodTent x p ∂μ) ≤ (1 + θ) / V) := by
  have hVpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have ht1 : ENNReal.ofReal (θ / 2 ^ (n + 1)) ≤ 1 :=
    ENNReal.ofReal_le_one.2 ((div_le_one hVpos).2 hθ1)
  have ht0 : ENNReal.ofReal (θ / 2 ^ (n + 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (div_pos hθ0 hVpos)).ne'
  have hmono : ENNReal.ofReal (θ / 2 ^ (n + 1)) * (1 - ((2 : ℝ≥0∞) ^ (n + 1))⁻¹)
      ≤ ENNReal.ofReal (θ / 2 ^ (n + 1)) := by
    calc ENNReal.ofReal (θ / 2 ^ (n + 1)) * (1 - ((2 : ℝ≥0∞) ^ (n + 1))⁻¹)
        ≤ ENNReal.ofReal (θ / 2 ^ (n + 1)) * 1 := by gcongr; exact tsub_le_self
      _ = ENNReal.ofReal (θ / 2 ^ (n + 1)) := mul_one _
  haveI := isProbabilityMeasure_boxDensityLaw x ht1
  refine ⟨roundBox x, boxDensityLaw x (ENNReal.ofReal (θ / 2 ^ (n + 1))), 2 ^ (n + 1), 0,
    ENNReal.ofReal (θ / 2 ^ (n + 1)) * (1 - ((2 : ℝ≥0∞) ^ (n + 1))⁻¹),
    inferInstance, measurableSet_roundBox x, volume_roundBox_ne_zero x,
    volume_roundBox_ne_top x, volume_roundBox_toReal x, rfl, rfl,
    boxDensityLaw_absolutelyContinuous x _, (tvLe_boxDensityLaw x ht1).mono hmono,
    le_of_eq (setIntegral_prodTent_compl_roundBox x), tvDist_boxDensityLaw_pos ht0, hmono,
    tvLe_boxDensityLaw x ht1, fun _ h => le_of_tvLe_boxDensityLaw x ht1 h,
    boxDensityLaw_ne_uniformOn x ht1 ht0, ?_⟩
  simpa using boxDensityLaw_window x hθ0.le hθ1

end Witness

/-! ## Axiom check (`CLAUDE.md` §4) -/

#print axioms mix_apply
#print axioms isProbabilityMeasure_mix
#print axioms tvLe_mix_of_tvLe
#print axioms tvLe_mix
#print axioms le_of_tvLe_mix
#print axioms le_of_tvLe_mix_of_apply
#print axioms uniformOn_eq_mix
#print axioms tvLe_uniformOn_subset
#print axioms mix_absolutelyContinuous
#print axioms mix_ne_of_ne_zero
#print axioms volume_cube
#print axioms volume_cube_half
#print axioms volume_roundBox
#print axioms volume_roundBox_toReal
#print axioms setIntegral_prodTent_compl_roundBox
#print axioms boxAtomLaw_singleton
#print axioms tvLe_boxAtomLaw
#print axioms le_of_tvLe_boxAtomLaw
#print axioms boxAtomLaw_ne_uniformOn
#print axioms boxAtomLaw_apply_sdiff
#print axioms not_pointwiseClose_boxAtomLaw
#print axioms boxAtomLaw_window
#print axioms tvDist_boxAtomLaw_eq
#print axioms volume_roundBox_sdiff_cube_half
#print axioms uniformOn_roundBox_cube_half
#print axioms tvLe_uniformOn_cube_half
#print axioms boxDensityLaw_absolutelyContinuous
#print axioms boxDensityLaw_apply_cube_half
#print axioms tvLe_boxDensityLaw
#print axioms le_of_tvLe_boxDensityLaw
#print axioms tvDist_boxDensityLaw_pos
#print axioms boxDensityLaw_ne_uniformOn
#print axioms boxDensityLaw_window
#print axioms exists_nondegenerate_theorem2_of_tvLe_witness
#print axioms exists_atomFree_theorem2_of_tvLe_witness

end Arlib.TVWitness
