/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.PositionalCut

/-!
# Two-sided transverse cuts for nonnegative densities

This file settles the open statement **(P1)** of `Arlib.Convexity.PositionalCut` for
**nonnegative** integrands, without Borsuk–Ulam and without the two-measure ham-sandwich
theorem.

(P1) asks: given a measurable `C` with `0 < ∫_C g` and `0 < ∫_C h`, produce a direction `L` and a
level `s` such that **both** sides of the cut `{L ≤ s}`, `{s < L}` carry positive `g`-mass **and**
positive `h`-mass.  `Arlib.exists_side_extent_halved_pos` then halves an extent while keeping the
localisation invariant, and `Arlib.exists_cut_chain_extent_halved` iterates it.

## The argument

For a finite measure with a nonnegative density, the **mass centre** is a "thick" point: every
*open* halfspace whose boundary hyperplane passes through it carries positive mass.  Indeed if
`L x ≤ L a` a.e. on `C` for the mass centre `a`, then `∫_C g(x)·(L x - L a) dμ = 0` by the very
definition of `a`, and the integrand is a.e. nonpositive, so it vanishes a.e.; hence `g = 0` a.e.
off the hyperplane `{L = L a}`, which is Haar-null, so `∫_C g = 0` — a contradiction.  This is
`Arlib.exists_massCentre_halfSpace_pos`.

Now take mass centres `a` for `g` and `b` for `h`.  In dimension `≥ 2` there is a nonzero
functional `L` with `L (a - b) = 0` (`Arlib.exists_ne_zero_apply_eq_zero`), i.e. a direction in
which the two mass centres sit at the *same* level `s = L a = L b`.  Both sides of the cut at that
level then have positive `g`-mass (thickness of `a`) and positive `h`-mass (thickness of `b`).
That is `Arlib.exists_two_sided_halfSpace`, and `Arlib.exists_two_sided_halfSpace_extent_halved`
packages it with `Arlib.exists_side_extent_halved_pos`.

The set of admissible directions is the whole hyperplane `{L : L a = L b}` of the dual — an
`(n-1)`-dimensional family, i.e. exactly the transverse directions of the needle picture, and it
is disjoint from the longitudinal direction whenever `L a ≠ L b`.

## Main results

* `Arlib.exists_massCentre_halfSpace_pos` — the thick point (mass centre).  Nonnegative density,
  bounded measurable carrier, Haar measure.
* `Arlib.exists_ne_zero_apply_eq_zero` — in an inner-product space of dimension `≥ 2`, every
  vector is annihilated by some nonzero functional.
* `Arlib.exists_massCentres_two_sided` — the sharper per-direction form: the cut works for
  **every** nonzero `L` equalising the two mass centres, an `(n-1)`-dimensional family.
* `Arlib.exists_two_sided_halfSpace` — **(P1) for nonnegative `g, h`.**
* `Arlib.exists_two_sided_halfSpace_extent_halved` — (P1) fed into
  `Arlib.exists_side_extent_halved_pos`: a cut in a direction `L ≠ 0`, both of whose sides keep
  the invariant, one of which has half the `L`-extent.
* `Arlib.exists_two_sided_halfSpace_ball` — a closed, hypothesis-free instance on the Euclidean
  plane: the hypotheses above are simultaneously satisfiable, so nothing here is vacuous.
* `Arlib.exists_two_sided_halfSpace_single` — the *one*-function statement, for a **signed**
  integrand and in **every** direction: it is a two-line consequence of
  `Arlib.exists_halfSpace_bisecting`.  This is what isolates simultaneity as the entire content
  of (P1).
* `Arlib.not_two_sided_of_sign_separated_le` — the obstruction, sharpened from `a < b` to
  `a ≤ b`: a direction in which the two masses sit in *touching* opposite halfspaces admits no
  two-sided cut either.

## What is assumed, stated plainly

`g, h ≥ 0` **on `C`**, `IntegrableOn`, `C` measurable and bounded, `μ` an additive Haar measure on
a finite-dimensional real inner-product space of dimension `≥ 2`.  All of these appear verbatim in
the statements below; none of them is a named predicate, and none of them asserts any part of the
conclusion.

## What is *not* proved here

**Signed integrands.**  The localisation argument of `Arlib.Convexity.LocalizationLemma` needs
*signed* `g, h`, and the mass centre is meaningless for a signed density (`∫_C g x • x / ∫_C g`
can sit anywhere, and the identity above loses its sign).  So the result below is a genuine
partial result, not a solution of (P1) in the generality localisation consumes.

The signed obstruction is *exactly* the simultaneity, and that is proved below, not asserted:
`Arlib.exists_two_sided_halfSpace_single` shows that for a *single* signed integrand every
direction already admits a two-sided level, since `Arlib.exists_halfSpace_bisecting` splits
`∫_C g` into two halves, each equal to `(∫_C g)/2 > 0`.  What can fail for signed `g, h` is that
the two-sided level sets of `g` and of `h` in a given direction are disjoint, and — unlike the
nonnegative case, where each is an interval — they need not be intervals, so no one-dimensional
comparison closes the gap.  That is where Borsuk–Ulam re-enters.

**Nonnegative but a *fixed* direction.**  `Arlib.exists_cut_chain_extent_halved` iterates cuts
orthogonal to *one* fixed `L`; the direction produced below depends on the current body (through
its two mass centres), so it does not discharge that theorem's `hstep` for a prescribed `L`.  What
it gives is one transverse two-sided cut per body, which is what a variable-direction chain needs.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Bornology

namespace Arlib

/-! ### The mass centre is a thick point -/

section MassCentre

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The mass centre of a nonnegative density is a thick point.**

If `g ≥ 0` on a bounded measurable `C` with `0 < ∫_C g`, there is a point `a` (the mass centre
`(∫_C g)⁻¹ • ∫_C g x • x`) such that for **every** nonzero direction `L` the *open* halfspace
`{x | L a < L x}` carries positive `g`-mass.

Proof: writing `t = L a`, the definition of the mass centre says `∫_C g x · (L x - t) dμ = 0`.
If the open halfspace above `t` were null for `g`, the integrand would be a.e. nonpositive, hence
a.e. zero, hence `g = 0` a.e. off the hyperplane `{L = t}`; that hyperplane is Haar-null
(`Arlib.measure_hyperplane_eq_zero`), so `∫_C g = 0`, contradicting positivity.

Applied to `-L` this also gives positive mass to `{x | L x < L a}`; that is how
`Arlib.setIntegral_halfSpace_pos_of_massCentre` gets both sides of the cut at once. -/
theorem exists_massCentre_halfSpace_pos {g : E → ℝ} {C : Set E}
    (hC : MeasurableSet C) (hCb : IsBounded C) (hgi : IntegrableOn g C μ)
    (hgnn : ∀ x ∈ C, 0 ≤ g x) (hgpos : 0 < ∫ x in C, g x ∂μ) :
    ∃ a : E, ∀ L : E →L[ℝ] ℝ, L ≠ 0 → 0 < ∫ x in C ∩ {x : E | L a < L x}, g x ∂μ := by
  obtain ⟨r, hr⟩ := hCb.subset_closedBall (0 : E)
  have hnorm : ∀ᵐ x ∂(μ.restrict C), ‖x‖ ≤ r := by
    filter_upwards [ae_restrict_mem hC] with x hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hr hx
  have hvec : IntegrableOn (fun x => g x • x) C μ := by
    have h := hgi.smul_bdd (f := fun x : E => x) r continuous_id.aestronglyMeasurable hnorm
    exact h.congr (Filter.Eventually.of_forall fun x => rfl)
  set G : ℝ := ∫ x in C, g x ∂μ with hGdef
  set m : E := ∫ x in C, g x • x ∂μ with hmdef
  refine ⟨G⁻¹ • m, fun L hL => ?_⟩
  set a : E := G⁻¹ • m with hadef
  set t : ℝ := L a with htdef
  -- The moment identity defining the mass centre.
  have hmom : ∫ x in C, g x * L x ∂μ = G * t := by
    have h1 : ∫ x in C, g x * L x ∂μ = L m := by
      have hpt : ∀ x : E, g x * L x = L (g x • x) := by
        intro x; rw [map_smul, smul_eq_mul]
      simp_rw [hpt, hmdef]
      exact ContinuousLinearMap.integral_comp_comm L hvec
    have h2 : t = G⁻¹ * L m := by rw [htdef, hadef, map_smul, smul_eq_mul]
    rw [h1, h2, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hgpos), one_mul]
  -- `g x * L x` is integrable on `C` because `L` is bounded there.
  have hgL : IntegrableOn (fun x => g x * L x) C μ := by
    refine hgi.mul_bdd (c := ‖L‖ * r) L.continuous.aestronglyMeasurable ?_
    filter_upwards [hnorm] with x hx
    calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ ‖L‖ * r := by
          exact mul_le_mul_of_nonneg_left hx (norm_nonneg L)
  by_contra hcon
  rw [not_lt] at hcon
  set S : Set E := {x : E | t < L x} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const L.continuous.measurable
  have hCS : MeasurableSet (C ∩ S) := hC.inter hSm
  have hzero : ∫ x in C ∩ S, g x ∂μ = 0 :=
    le_antisymm hcon (setIntegral_nonneg hCS fun x hx => hgnn x hx.1)
  -- `g` vanishes a.e. above the level `t`.
  have hgS : g =ᵐ[μ.restrict (C ∩ S)] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ (hgi.mono_set inter_subset_left)).mp hzero
    filter_upwards [ae_restrict_mem hCS] with x hx using hgnn x hx.1
  have hgS' : ∀ᵐ x ∂(μ.restrict C), x ∈ S → g x = 0 := by
    refine (ae_restrict_iff' hSm).mp ?_
    rw [Measure.restrict_restrict hSm, inter_comm]
    filter_upwards [hgS] with x hx using hx
  -- The mass-centre integrand.
  set F : E → ℝ := fun x => g x * (L x - t) with hFdef
  have hFint : IntegrableOn F C μ := by
    have hrw : F = fun x => g x * L x - t * g x := by
      funext x; rw [hFdef]; ring
    rw [hrw]
    exact hgL.sub (hgi.const_mul t)
  have hFzero : ∫ x in C, F x ∂μ = 0 := by
    have hrw : F = fun x => g x * L x - t * g x := by
      funext x; rw [hFdef]; ring
    rw [hrw, integral_sub hgL (hgi.const_mul t), integral_const_mul, hmom, ← hGdef]
    ring
  have hFnonpos : ∀ᵐ x ∂(μ.restrict C), F x ≤ 0 := by
    filter_upwards [hgS', ae_restrict_mem hC] with x hx hxC
    rcases le_or_gt (L x) t with hle | hlt
    · exact mul_nonpos_of_nonneg_of_nonpos (hgnn x hxC) (by linarith)
    · have : g x = 0 := hx hlt
      rw [hFdef]
      simp [this]
  have hFae : F =ᵐ[μ.restrict C] 0 := by
    have hneg : (0 : E → ℝ) ≤ᵐ[μ.restrict C] fun x => -F x := by
      filter_upwards [hFnonpos] with x hx
      simpa using hx
    have hint : ∫ x in C, -F x ∂μ = 0 := by rw [integral_neg, hFzero, neg_zero]
    have := (integral_eq_zero_iff_of_nonneg_ae hneg hFint.neg).mp hint
    filter_upwards [this] with x hx
    have : -F x = 0 := hx
    linarith
  -- The hyperplane through the mass centre is Haar-null.
  have hhyp : ∀ᵐ x ∂(μ.restrict C), L x ≠ t := by
    refine ae_restrict_of_ae ?_
    have := measure_eq_zero_iff_ae_notMem.mp (measure_hyperplane_eq_zero μ hL t)
    filter_upwards [this] with x hx using hx
  -- Hence `g` vanishes a.e. on `C`, contradicting `0 < ∫_C g`.
  have hgzero : g =ᵐ[μ.restrict C] 0 := by
    filter_upwards [hFae, hhyp] with x hF hne
    have hF' : g x * (L x - t) = 0 := hF
    rcases mul_eq_zero.mp hF' with h | h
    · exact h
    · exact absurd (by linarith : L x = t) hne
  have : G = 0 := by rw [hGdef]; exact integral_eq_zero_of_ae hgzero
  exact absurd this (ne_of_gt hgpos)

/-- **Both sides of the cut through a thick point carry positive mass.**

If `a` is thick for `g` in the sense of `Arlib.exists_massCentre_halfSpace_pos` — every open
halfspace with `a` on its boundary has positive `g`-mass — then for every nonzero `L` the cut at
level `L a` has positive `g`-mass on *both* sides.  The open side `{L a < L}` is the thickness
hypothesis at `L`; the closed side `{L ≤ L a}` contains the open side `{L < L a}`, which is the
thickness hypothesis at `-L`.

The thickness hypothesis is an ordinary ∀-statement about the set integrals of `g`; it is
discharged unconditionally by `Arlib.exists_massCentre_halfSpace_pos`. -/
theorem setIntegral_halfSpace_pos_of_massCentre {g : E → ℝ} {C : Set E} {a : E}
    (hC : MeasurableSet C) (hgi : IntegrableOn g C μ) (hgnn : ∀ x ∈ C, 0 ≤ g x)
    (hthick : ∀ L : E →L[ℝ] ℝ, L ≠ 0 → 0 < ∫ x in C ∩ {x : E | L a < L x}, g x ∂μ)
    {L : E →L[ℝ] ℝ} (hL : L ≠ 0) (side : Bool) :
    0 < ∫ x in C ∩ halfSpace L (L a) side, g x ∂μ := by
  cases side
  · simpa using hthick L hL
  · refine lt_of_lt_of_le (hthick (-L) (neg_ne_zero.mpr hL)) ?_
    refine setIntegral_mono_set (hgi.mono_set inter_subset_left) ?_ ?_
    · filter_upwards [ae_restrict_mem (hC.inter (measurableSet_halfSpace L (L a) true))]
        with x hx using hgnn x hx.1
    · refine LE.le.eventuallyLE ?_
      rintro x ⟨hx, hlt⟩
      refine ⟨hx, ?_⟩
      have hlt' : -(L a) < -(L x) := hlt
      show L x ≤ L a
      linarith

end MassCentre

/-! ### A nonzero direction annihilating a prescribed vector -/

section Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **In dimension `≥ 2`, every vector is annihilated by some nonzero functional.**

For `v ≠ 0` the orthogonal complement of `ℝ ∙ v` has dimension `finrank E - 1 ≥ 1`, so it
contains a nonzero `u`, and `⟪u, ·⟫` is the required functional; for `v = 0` any nonzero `u`
works.  This is the only place where `2 ≤ finrank E` is used, and it is exactly the statement
that the transverse directions of a segment form a nonempty family. -/
theorem exists_ne_zero_apply_eq_zero (h2 : 2 ≤ Module.finrank ℝ E) (v : E) :
    ∃ L : E →L[ℝ] ℝ, L ≠ 0 ∧ L v = 0 := by
  obtain ⟨u, hu0, huv⟩ : ∃ u : E, u ≠ 0 ∧ inner ℝ u v = (0 : ℝ) := by
    rcases eq_or_ne v 0 with rfl | hv
    · have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
      obtain ⟨u, hu⟩ := exists_ne (0 : E)
      exact ⟨u, hu, inner_zero_right u⟩
    · have hspan : Module.finrank ℝ (ℝ ∙ v : Submodule ℝ E) = 1 := finrank_span_singleton hv
      have hadd := (ℝ ∙ v : Submodule ℝ E).finrank_add_finrank_orthogonal (𝕜 := ℝ)
      have hne : (ℝ ∙ v : Submodule ℝ E)ᗮ ≠ ⊥ := by
        intro hbot
        rw [hbot, hspan, finrank_bot] at hadd
        omega
      obtain ⟨u, humem, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      refine ⟨u, hu0, ?_⟩
      have hmem := (Submodule.mem_orthogonal _ _).mp humem
      rw [real_inner_comm]
      exact hmem v (Submodule.mem_span_singleton_self v)
  refine ⟨innerSL ℝ u, ?_, by simpa using huv⟩
  intro hzero
  have huu : inner ℝ u u = (0 : ℝ) := by
    have := congrArg (fun T : E →L[ℝ] ℝ => T u) hzero
    simpa using this
  exact hu0 (inner_self_eq_zero.mp huu)

end Dual

/-! ### (P1) for nonnegative densities -/

section TwoSided

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The whole family of two-sided transverse directions.**

For nonnegative `g, h` with positive mass on a bounded measurable `C`, there are two points
`a, b` (the mass centres) such that **every** nonzero direction `L` equalising them, `L a = L b`,
cuts `C` at the level `L a` into two sides each of which carries positive `g`-mass *and* positive
`h`-mass.

`{L : L a = L b}` is a hyperplane of the dual space, i.e. an `(n-1)`-dimensional family of
admissible directions: in the needle picture of `Arlib.Convexity.PositionalCut` these are the
transverse directions, and the longitudinal one (where `L a ≠ L b`) is excluded, as
`Arlib.not_two_sided_of_sign_separated` says it must be. -/
theorem exists_massCentres_two_sided {g h : E → ℝ} {C : Set E}
    (hC : MeasurableSet C) (hCb : IsBounded C)
    (hgi : IntegrableOn g C μ) (hhi : IntegrableOn h C μ)
    (hgnn : ∀ x ∈ C, 0 ≤ g x) (hhnn : ∀ x ∈ C, 0 ≤ h x)
    (hgpos : 0 < ∫ x in C, g x ∂μ) (hhpos : 0 < ∫ x in C, h x ∂μ) :
    ∃ a b : E, ∀ L : E →L[ℝ] ℝ, L ≠ 0 → L a = L b → ∀ side : Bool,
      0 < ∫ x in C ∩ halfSpace L (L a) side, g x ∂μ ∧
      0 < ∫ x in C ∩ halfSpace L (L a) side, h x ∂μ := by
  obtain ⟨a, ha⟩ := exists_massCentre_halfSpace_pos hC hCb hgi hgnn hgpos
  obtain ⟨b, hb⟩ := exists_massCentre_halfSpace_pos hC hCb hhi hhnn hhpos
  refine ⟨a, b, fun L hL hab side => ⟨?_, ?_⟩⟩
  · exact setIntegral_halfSpace_pos_of_massCentre hC hgi hgnn ha hL side
  · rw [hab]
    exact setIntegral_halfSpace_pos_of_massCentre hC hhi hhnn hb hL side

/-- **(P1) for nonnegative integrands.**

Given a bounded measurable `C` carrying positive `g`-mass and positive `h`-mass, with
`g, h ≥ 0` on `C` and integrable there, and `μ` an additive Haar measure on a finite-dimensional
real inner-product space of dimension `≥ 2`, there are a nonzero direction `L` and a level `s`
such that **both** sides of the cut `{L ≤ s}`, `{s < L}` carry positive `g`-mass and positive
`h`-mass.

This is exactly the hypothesis `hpos` of `Arlib.exists_side_extent_halved_pos` and the
per-body content of the hypothesis `hstep` of `Arlib.exists_cut_chain_extent_halved`, i.e. the
statement labelled **(P1)** in `Arlib.Convexity.PositionalCut`, proved here for nonnegative
integrands with no ham-sandwich theorem and no Borsuk–Ulam: the direction is any one equalising
the two mass centres, and the level is their common value.

The nonnegativity of `g` and `h` is essential to the proof and is **not** removable by it: see the
module docstring for what is and is not known for signed integrands. -/
theorem exists_two_sided_halfSpace (h2 : 2 ≤ Module.finrank ℝ E) {g h : E → ℝ} {C : Set E}
    (hC : MeasurableSet C) (hCb : IsBounded C)
    (hgi : IntegrableOn g C μ) (hhi : IntegrableOn h C μ)
    (hgnn : ∀ x ∈ C, 0 ≤ g x) (hhnn : ∀ x ∈ C, 0 ≤ h x)
    (hgpos : 0 < ∫ x in C, g x ∂μ) (hhpos : 0 < ∫ x in C, h x ∂μ) :
    ∃ (L : E →L[ℝ] ℝ) (s : ℝ), L ≠ 0 ∧ ∀ side : Bool,
      0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ ∧
      0 < ∫ x in C ∩ halfSpace L s side, h x ∂μ := by
  obtain ⟨a, b, hab⟩ :=
    exists_massCentres_two_sided hC hCb hgi hhi hgnn hhnn hgpos hhpos
  obtain ⟨L, hL, hLab⟩ := exists_ne_zero_apply_eq_zero h2 (a - b)
  have hLeq : L a = L b := by
    have h0 : L a - L b = 0 := by rw [← map_sub]; exact hLab
    linarith
  exact ⟨L, L a, hL, hab L hL hLeq⟩

/-- **A transverse cut that halves an extent and keeps the localisation invariant.**

(P1) fed into `Arlib.exists_side_extent_halved_pos`: for nonnegative `g, h` there is a cut of `C`
in some nonzero direction `L`, both of whose sides keep positive `g`- and `h`-mass, and such that
for *every* bracketing `[p, q]` of the `L`-values on `C` one of the two sides has all its
`L`-values in a subinterval of length exactly `(q - p)/2` — while still carrying both masses.

This is one step of the transverse thinning of `Arlib.exists_cut_chain_extent_halved`, with the
two-sidedness hypothesis discharged.  The direction `L` depends on `C` (through its two mass
centres), so iterating it thins a *varying* direction, not the single fixed direction of that
theorem. -/
theorem exists_two_sided_halfSpace_extent_halved (h2 : 2 ≤ Module.finrank ℝ E) {g h : E → ℝ}
    {C : Set E} (hC : MeasurableSet C) (hCb : IsBounded C)
    (hgi : IntegrableOn g C μ) (hhi : IntegrableOn h C μ)
    (hgnn : ∀ x ∈ C, 0 ≤ g x) (hhnn : ∀ x ∈ C, 0 ≤ h x)
    (hgpos : 0 < ∫ x in C, g x ∂μ) (hhpos : 0 < ∫ x in C, h x ∂μ) :
    ∃ (L : E →L[ℝ] ℝ) (s : ℝ), L ≠ 0 ∧
      (∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ ∧
        0 < ∫ x in C ∩ halfSpace L s side, h x ∂μ) ∧
      ∀ p q : ℝ, p ≤ q → (∀ x ∈ C, L x ∈ Icc p q) →
        ∃ (side : Bool) (p' q' : ℝ), p ≤ p' ∧ q' ≤ q ∧ q' - p' = (q - p) / 2 ∧
          (∀ x ∈ C ∩ halfSpace L s side, L x ∈ Icc p' q') ∧
          0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ ∧
          0 < ∫ x in C ∩ halfSpace L s side, h x ∂μ := by
  obtain ⟨L, s, hL, hpos⟩ :=
    exists_two_sided_halfSpace h2 hC hCb hgi hhi hgnn hhnn hgpos hhpos
  exact ⟨L, s, hL, hpos, fun p q hpq hCpq => exists_side_extent_halved_pos hpq hCpq hpos⟩

/-- **Non-vacuity: the hypotheses are simultaneously satisfiable.**

A closed statement with no hypotheses at all: on the Euclidean plane, the unit ball with the
constant density `1` (for both `g` and `h`) admits a two-sided cut.  Its point is to certify that
the typeclass bundle and the analytic hypotheses of `Arlib.exists_two_sided_halfSpace` can all be
met at once, so that theorem is not vacuously true. -/
theorem exists_two_sided_halfSpace_ball :
    ∃ (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (s : ℝ), L ≠ 0 ∧ ∀ side : Bool,
      0 < ∫ _x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ halfSpace L s side,
            (1 : ℝ) ∧
      0 < ∫ _x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ halfSpace L s side,
            (1 : ℝ) := by
  have hC : MeasurableSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    measurableSet_closedBall
  have hCb : IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Metric.isBounded_closedBall
  have htop : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hi : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) volume := integrableOn_const htop
  have hpos : 0 < ∫ _x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, (1 : ℝ) := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    exact ENNReal.toReal_pos
      (Metric.measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin 2)) one_pos).ne' htop
  exact exists_two_sided_halfSpace (μ := volume) (by simp)
    hC hCb hi hi (fun _ _ => zero_le_one) (fun _ _ => zero_le_one) hpos hpos

end TwoSided

/-! ### What one function alone gives, in every direction -/

section Single

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **For a single integrand — signed, and in every direction — a two-sided level always exists.**

No sign hypothesis, no dimension hypothesis, and the direction `L ≠ 0` is prescribed: the
mass-bisecting hyperplane of `Arlib.exists_halfSpace_bisecting` puts exactly `(∫_C f)/2 > 0` on
each side.

This is the exact measure of what (P1) adds: the difficulty is never one function, nor the
choice of direction for one function, but making *two* functions two-sided at the *same*
hyperplane. -/
theorem exists_two_sided_halfSpace_single {f : E → ℝ} {C : Set E}
    (hC : MeasurableSet C) (hCb : IsBounded C) (hf : IntegrableOn f C μ)
    {L : E →L[ℝ] ℝ} (hL : L ≠ 0) (hpos : 0 < ∫ x in C, f x ∂μ) :
    ∃ s : ℝ, ∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, f x ∂μ := by
  obtain ⟨s, hs⟩ := exists_halfSpace_bisecting hf hCb hL
  have hsum := setIntegral_halfSpace_add hf hC L s
  refine ⟨s, fun side => ?_⟩
  cases side
  · have hfalse : ∫ x in C ∩ halfSpace L s false, f x ∂μ = (∫ x in C, f x ∂μ) / 2 := by
      linarith
    rw [hfalse]; linarith
  · rw [hs]; linarith

end Single

/-! ### The obstruction, sharpened to touching halfspaces -/

section Separated

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E}

/-- **No cut orthogonal to a separating direction is two-sided — even if the slab is degenerate.**

`Arlib.not_two_sided_of_sign_separated` assumes `a < b`; the same proof works for `a ≤ b`, i.e.
also when the two masses merely *touch* along the hyperplane `{L = a} = {L = b}`, because the two
escapes it plays off are `b ≤ s` and `s < a`, which are already incompatible at `a = b`.

The degenerate case is exactly the boundary case that `Arlib.exists_massCentres_two_sided` has to
avoid, and does: the cut it produces sits at the common level of the two mass centres, and
`Arlib.exists_massCentre_halfSpace_pos` puts positive mass strictly on both sides of it, so a
configuration with `g` and `h` in touching opposite halfspaces of `L` can never have
`L (massCentre g) = L (massCentre h)`. -/
theorem not_two_sided_of_sign_separated_le {g h : E → ℝ} {C : Set E} (hC : MeasurableSet C)
    {L : E →L[ℝ] ℝ} {a b : ℝ} (hab : a ≤ b) (hg : ∀ x, a < L x → g x ≤ 0)
    (hh : ∀ x, L x < b → h x ≤ 0) (s : ℝ) :
    ¬ (∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ ∧
        0 < ∫ x in C ∩ halfSpace L s side, h x ∂μ) := by
  intro hcon
  have h1 : b ≤ s := le_of_setIntegral_halfSpace_true_pos hC hh (hcon true).2
  have h2 : s < a := lt_of_setIntegral_halfSpace_false_pos hC hg (hcon false).1
  linarith

end Separated

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`.  There are
no `axiom` declarations, no `sorry` and no `native_decide` anywhere in this file. -/

#print axioms exists_massCentre_halfSpace_pos
#print axioms setIntegral_halfSpace_pos_of_massCentre
#print axioms exists_ne_zero_apply_eq_zero
#print axioms exists_massCentres_two_sided
#print axioms exists_two_sided_halfSpace
#print axioms exists_two_sided_halfSpace_extent_halved
#print axioms exists_two_sided_halfSpace_ball
#print axioms exists_two_sided_halfSpace_single
#print axioms not_two_sided_of_sign_separated_le

end Arlib
