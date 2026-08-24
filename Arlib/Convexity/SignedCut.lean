/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.Analysis.Normed.Module.Connected
import Arlib.Convexity.TransverseCut

/-!
# Two-sided transverse cuts for **signed** integrands

`Arlib.Convexity.TransverseCut` settles the open statement **(P1)** of
`Arlib.Convexity.PositionalCut` for *nonnegative* integrands, by the mass centre, and its module
docstring records that the mass centre is meaningless for a signed density: *"that is where
Borsuk–Ulam re-enters."*  This file attacks the signed case and gets a good part of the way:

* the difficulty is isolated, by an outright proof, in a **one-dimensional, direction-by-direction
  connectivity property of `g` alone** — no topology of spheres, no ham sandwich;
* under that property the two-sided cut is produced for a **completely arbitrary signed `h`**, and
  the cut even *bisects* `h` exactly;
* the property holds automatically when `g ≥ 0`, so the theorem below **strictly contains**
  `Arlib.exists_two_sided_halfSpace` (which needed `g ≥ 0` *and* `h ≥ 0`).

Nothing here is a named predicate: the extra property appears verbatim, as an `OrdConnected`
hypothesis on an explicit set of real numbers, in the statement of each theorem that uses it.

## The mechanism

Fix a bounded measurable `C` and an integrable, **signed** `g` with `A := ∫_C g > 0`.  Call a pair
`(u, s)` with `u ≠ 0` a *two-sided cut for `g`* when both `∫_{C ∩ {⟪u,·⟫ ≤ s}} g` and
`∫_{C ∩ {s < ⟪u,·⟫}} g` are positive; equivalently, writing `Φ (u,s)` for the first of them,
when `Φ (u,s) ∈ (0, A)`.  Let `T` be the set of two-sided cuts.

1. `Arlib.continuousOn_setIntegral_halfSpace_pair` — `Φ` is **jointly** continuous in the
   direction *and* the level (dominated convergence; the existing
   `Arlib.continuous_setIntegral_halfSpace` is the level-only case).  Hence `T` is **open**.
2. `Arlib.setIntegral_halfSpace_neg` — reversing the direction swaps the two sides, so
   `Φ (-u, -s) = A - Φ (u, s)`: `T` is invariant under `(u,s) ↦ (-u,-s)`, and `Φ` is *odd* about
   `A/2` along that involution.
3. `Arlib.exists_two_sided_halfSpace_single` (in `TransverseCut`) — every **fibre** of `T` over a
   fixed direction is **nonempty**, for signed `g`, by the one-dimensional intermediate value
   theorem.
4. `Arlib.isPreconnected_of_isOpen_of_fibers` — an open subset of `X × Y` whose fibres over a
   preconnected base are nonempty and preconnected is itself preconnected.  With the base
   `E ∖ {0}` (connected because `2 ≤ finrank ℝ E`) this turns *fibrewise* connectivity of `T`
   into connectivity of `T`.
5. `Arlib.exists_bisecting_of_preconnected_family` — on a preconnected family of cuts containing
   some cut **and its reverse**, the `h`-mass of one side is a continuous function taking the two
   values `t` and `(∫_C h) - t`, so by the intermediate value theorem it takes the value
   `(∫_C h)/2` somewhere on the family.  That cut is two-sided for `g` (it lies in `T`) and
   bisects `h`.

Step 5 is the point: **the second function needs no hypothesis whatsoever.**  What the argument
consumes about `g` is exactly the input to step 4.

## Main results

* `Arlib.isPreconnected_of_isOpen_of_fibers` — the fibrewise connectivity criterion (pure
  topology).
* `Arlib.continuousOn_setIntegral_halfSpace_pair` — joint continuity of the cut mass in
  `(direction, level)`.
* `Arlib.setIntegral_halfSpace_neg` — reversing a direction swaps the sides of a cut.
* `Arlib.exists_bisecting_of_preconnected_family` — IVT along a reverse-closed preconnected family.
* `Arlib.exists_bisecting_halfSpace_through_point` — **for a single signed integrand, through
  *every* point of the space there is a hyperplane bisecting it**, hence a two-sided cut
  (`Arlib.exists_two_sided_halfSpace_through_point`).  This is the honest signed replacement for
  `Arlib.exists_massCentre_halfSpace_pos`: for `g ≥ 0` the mass centre is two-sided in *every*
  direction; for signed `g` every point is two-sided in *some* direction.
* `Arlib.exists_two_sided_halfSpace_of_ordConnected` — **(P1) for a signed `g` whose two-sided
  levels are, in each direction, an interval, and a completely arbitrary signed `h`.**
* `Arlib.ordConnected_two_sided_levels_of_nonneg` — that hypothesis holds whenever `g ≥ 0` on `C`.
* `Arlib.exists_two_sided_halfSpace_signed_snd` — consequently: **(P1) for `g ≥ 0` and `h`
  signed**, strictly stronger than `Arlib.exists_two_sided_halfSpace`.

## What is assumed, stated plainly

`C` bounded measurable, `g, h` integrable on `C` with positive integrals, `μ` an additive Haar
measure on a finite-dimensional real inner-product space with `2 ≤ finrank ℝ E`, and — for the
signed theorem — for each nonzero direction `L`, that the set

  `{s | both sides of the cut {L ≤ s} carry positive g-mass}`

is `OrdConnected`, i.e. an interval.  That set is an explicit set of reals built from set integrals
of `g`; the hypothesis is a statement about the **one-dimensional marginal of `g` in each
direction** and involves `h` not at all.  It is *not* the conclusion of any theorem here: the
conclusion is about a *common* cut for `g` and `h`, which this hypothesis does not mention.

## What is *not* proved here, precisely

**The interval hypothesis for a general signed `g`.**  For `g ≥ 0` the map `s ↦ Φ (u,s)` is
nondecreasing, so `{s | 0 < Φ < A}` is an interval.  For signed `g` that map is only continuous:
in a fixed direction `u` it is the tail integral of the one-dimensional marginal of `g`, which is
an arbitrary integrable function of one variable, so `Φ (u, ·)` is an arbitrary continuous function
running from `0` at `-∞` to `A` at `+∞` — and such a function may leave `(0, A)` and come back, in
which case `{s | 0 < Φ (u,s) < A}` is a disjoint union of intervals whose components can appear and
disappear as `u` turns.  When that happens `T` can fail to be connected, and step 4 above — the
*only* step that uses anything about `g` — breaks.  (No counterexample is *formalised* here; what
is formalised is that this is the sole remaining gap in the argument.)

That failure is not repairable by the devices this repository already has:

* **Decomposition `g = g⁺ - g⁻` does not reduce the signed case to the nonnegative one.**  A cut
  is two-sided for `g` when `∫ g > 0` on both sides, and `∫_S g = ∫_S g⁺ - ∫_S g⁻`: positivity of
  `∫_S g⁺` carries *no* information about the sign of `∫_S g`.  A cut two-sided for the pair
  `(g⁺, h⁺)` is generally not two-sided for `(g, h)`, and the mass centres of `g⁺` and `g⁻` are
  unrelated to any cut property of `g`.
* **A single fixed direction never suffices**, signed or not:
  `Arlib.not_two_sided_of_sign_separated_le` exhibits, for every direction `L`, configurations in
  which *no* level orthogonal to `L` is two-sided.  So the direction must be chosen, and choosing
  it is the entire content of (P1).
* **`Arlib.exists_bisecting_halfSpace_through_point` chooses a direction for one function**, by the
  intermediate value theorem, at any prescribed point — but the direction it returns depends on the
  function, and the theorem gives no way to make the choices for `g` and for `h` agree.  Making two
  such circle-valued choices agree is precisely the Borsuk–Ulam step.

Compactifying the level variable in each direction turns the family of oriented cuts into a sphere
on which reversal is the antipodal map, and `(Φ - A/2, Ψ - B/2)` into an odd map to `ℝ²` whose
zeros are the simultaneous bisections; the two-measure ham sandwich is the statement that it has
one.  Under the interval hypothesis the present file finds the zero of the *second* coordinate on a
connected reversal-invariant piece of the zero set of the first, using only the intermediate value
theorem; without it, that piece need not exist, and no argument here supplies it.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Bornology Filter Topology

namespace Arlib

/-! ### A fibrewise criterion for connectedness -/

section Fibre

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **An open set with connected fibres over a connected base is connected.**

If `T ⊆ X × Y` is open, every point of `T` lies over `B`, and over every point of the preconnected
set `B` the fibre `{y | (x,y) ∈ T}` is nonempty and preconnected, then `T` is preconnected.

The proof is the standard one: given a separation `T ⊆ u ∪ v` with `T ∩ u ∩ v = ∅`, each fibre —
being preconnected and covered by the two open slices — lies entirely in `u` or entirely in `v`,
and `Prod.fst '' (T ∩ u)`, `Prod.fst '' (T ∩ v)` are then open (the projection is an open map) and
separate `B`.

This is what converts the *one-dimensional* interval hypothesis of
`Arlib.exists_two_sided_halfSpace_of_ordConnected` into connectivity of the whole family of
two-sided cuts. -/
theorem isPreconnected_of_isOpen_of_fibers {B : Set X} (hB : IsPreconnected B) {T : Set (X × Y)}
    (hT : IsOpen T) (hsub : ∀ p ∈ T, p.1 ∈ B) (hne : ∀ x ∈ B, ∃ y : Y, (x, y) ∈ T)
    (hfib : ∀ x ∈ B, IsPreconnected {y : Y | (x, y) ∈ T}) :
    IsPreconnected T := by
  rintro u v hu hv hTuv ⟨p, hpT, hpu⟩ ⟨q, hqT, hqv⟩
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hno : ∀ w : X × Y, w ∈ T → w ∈ u → w ∈ v → False := by
    intro w h1 h2 h3
    have hw : w ∈ T ∩ (u ∩ v) := ⟨h1, h2, h3⟩
    rw [hcon] at hw
    exact hw
  -- a fibre cannot meet both `u` and `v`
  have hdich : ∀ a b : X × Y, a ∈ T → a ∈ u → b ∈ T → b ∈ v → a.1 = b.1 → False := by
    intro a b haT hau hbT hbv hab
    have hb' : (a.1, b.2) ∈ T := by rw [hab]; exact hbT
    have hb'' : (a.1, b.2) ∈ v := by rw [hab]; exact hbv
    obtain ⟨w, hwT, hwu, hwv⟩ :=
      hfib a.1 (hsub a haT) (Prod.mk a.1 ⁻¹' u) (Prod.mk a.1 ⁻¹' v)
        (hu.preimage (Continuous.prodMk_right a.1)) (hv.preimage (Continuous.prodMk_right a.1))
        (fun t ht => hTuv ht) ⟨a.2, haT, hau⟩ ⟨b.2, hb', hb''⟩
    exact hno (a.1, w) hwT hwu hwv
  -- the two projections separate the base
  have hU1 : IsOpen (Prod.fst '' (T ∩ u)) := isOpenMap_fst _ (hT.inter hu)
  have hU2 : IsOpen (Prod.fst '' (T ∩ v)) := isOpenMap_fst _ (hT.inter hv)
  have hcover : B ⊆ Prod.fst '' (T ∩ u) ∪ Prod.fst '' (T ∩ v) := by
    intro x hx
    obtain ⟨y, hy⟩ := hne x hx
    rcases hTuv hy with hyu | hyv
    · exact Or.inl ⟨(x, y), ⟨hy, hyu⟩, rfl⟩
    · exact Or.inr ⟨(x, y), ⟨hy, hyv⟩, rfl⟩
  have h1 : (B ∩ Prod.fst '' (T ∩ u)).Nonempty := ⟨p.1, hsub p hpT, ⟨p, ⟨hpT, hpu⟩, rfl⟩⟩
  have h2 : (B ∩ Prod.fst '' (T ∩ v)).Nonempty := ⟨q.1, hsub q hqT, ⟨q, ⟨hqT, hqv⟩, rfl⟩⟩
  obtain ⟨x, -, ⟨a, ⟨haT, hau⟩, hax⟩, ⟨b, ⟨hbT, hbv⟩, hbx⟩⟩ := hB _ _ hU1 hU2 hcover h1 h2
  exact hdich a b haT hau hbT hbv (by rw [hax, hbx])

end Fibre

/-! ### Reversing a direction exchanges the two sides of a cut -/

section Neg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The cut `(-L, -s)` is the cut `(L, s)` with its two sides exchanged.**

`halfSpace (-L) (-s) true = {x | s ≤ L x}` differs from `halfSpace L s false = {x | s < L x}`
exactly by the hyperplane `{L = s}`, which is Haar-null (`Arlib.measure_hyperplane_eq_zero`), so
the two carry the same mass; symmetrically for the other side.  This is the involution that makes
the cut mass an *odd* function on the family of oriented cuts. -/
theorem setIntegral_halfSpace_neg {f : E → ℝ} {C : Set E} {L : E →L[ℝ] ℝ} (hL : L ≠ 0) (s : ℝ)
    (side : Bool) :
    ∫ x in C ∩ halfSpace (-L) (-s) side, f x ∂μ = ∫ x in C ∩ halfSpace L s (!side), f x ∂μ := by
  have hnull : μ {x : E | L x = s} = 0 := measure_hyperplane_eq_zero μ hL s
  refine setIntegral_congr_set ?_
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null (fun x hx => ?_) hnull
    obtain ⟨⟨hxC, hx1⟩, hx2⟩ := hx
    cases side
    · -- side `false`: `{-s < -L x}`, i.e. `L x < s`, against `{L x ≤ s}`
      have h1 : -s < -(L x) := hx1
      exact absurd (⟨hxC, by show L x ≤ s; linarith⟩ : x ∈ C ∩ halfSpace L s true) hx2
    · -- side `true`: `{-L x ≤ -s}`, i.e. `s ≤ L x`, against `{s < L x}`
      have h1 : -(L x) ≤ -s := hx1
      have h2 : ¬ (s < L x) := fun hlt => hx2 ⟨hxC, hlt⟩
      push_neg at h2
      show L x = s
      linarith
  · refine measure_mono_null (fun x hx => ?_) hnull
    obtain ⟨⟨hxC, hx1⟩, hx2⟩ := hx
    cases side
    · have h1 : L x ≤ s := hx1
      have h2 : ¬ (-s < -(L x)) := fun hlt => hx2 ⟨hxC, hlt⟩
      push_neg at h2
      show L x = s
      linarith
    · have h1 : s < L x := hx1
      exact absurd (⟨hxC, by show -(L x) ≤ -s; linarith⟩ :
        x ∈ C ∩ halfSpace (-L) (-s) true) hx2

end Neg

/-! ### Joint continuity of the cut mass in direction and level -/

section Continuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The mass on one side of a cut is continuous in the direction *and* the level, jointly.**

`Arlib.continuous_setIntegral_halfSpace` is the special case of a fixed direction.  The proof is
the same dominated convergence argument, run along `𝓝 p₀` in an arbitrary (first countable)
parameter space carrying continuous families of directions `L p` and levels `σ p`: for `x` off the
null hyperplane `{L p₀ = σ p₀}` the indicator of `{L p ≤ σ p}` at `x` is eventually constant.

Joint continuity is what makes the family of two-sided cuts an **open** set, and hence subject to
the fibrewise connectivity criterion `Arlib.isPreconnected_of_isOpen_of_fibers`. -/
theorem continuousOn_setIntegral_halfSpace_param {f : E → ℝ} {C : Set E} (hf : IntegrableOn f C μ)
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {L : P → (E →L[ℝ] ℝ)} {σ : P → ℝ} (hL : Continuous L) (hσ : Continuous σ) :
    ContinuousOn (fun p : P => ∫ x in C ∩ halfSpace (L p) (σ p) true, f x ∂μ)
      {p : P | L p ≠ 0} := by
  have hmeas : ∀ p : P, MeasurableSet (halfSpace (L p) (σ p) true) := fun p =>
    measurableSet_halfSpace (L p) (σ p) true
  have hrepr : ∀ p : P, ∫ x in C ∩ halfSpace (L p) (σ p) true, f x ∂μ
      = ∫ x in C, Set.indicator (halfSpace (L p) (σ p) true) f x ∂μ := fun p =>
    (setIntegral_indicator (hmeas p)).symm
  have hev : ∀ x : E, Continuous fun p : P => L p x - σ p := fun x =>
    ((ContinuousLinearMap.apply ℝ ℝ x).continuous.comp hL).sub hσ
  intro p₀ hp₀
  refine ContinuousAt.continuousWithinAt ?_
  have hp₀' : L p₀ ≠ 0 := hp₀
  simp_rw [ContinuousAt, hrepr]
  have hnull : (μ.restrict C) {x : E | L p₀ x = σ p₀} = 0 := by
    have h1 : (μ.restrict C) {x : E | L p₀ x = σ p₀} ≤ μ {x : E | L p₀ x = σ p₀} :=
      Measure.le_iff'.mp Measure.restrict_le_self _
    rw [measure_hyperplane_eq_zero μ hp₀' (σ p₀)] at h1
    exact nonpos_iff_eq_zero.mp h1
  have hae : ∀ᵐ x ∂(μ.restrict C), L p₀ x ≠ σ p₀ := by
    rw [ae_iff]; simpa using hnull
  refine tendsto_integral_filter_of_dominated_convergence (fun x => |f x|)
    (Eventually.of_forall fun p => hf.aestronglyMeasurable.indicator (hmeas p))
    (Eventually.of_forall fun p => Eventually.of_forall fun x => norm_indicator_le_abs _ _ x)
    hf.abs ?_
  filter_upwards [hae] with x hx
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have hmem : x ∈ halfSpace (L p₀) (σ p₀) true := le_of_lt hlt
    rw [Set.indicator_of_mem hmem]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    have hset : {p : P | L p x - σ p < 0} ∈ 𝓝 p₀ := by
      refine IsOpen.mem_nhds (isOpen_lt (hev x) continuous_const) ?_
      show L p₀ x - σ p₀ < 0
      linarith
    filter_upwards [hset] with p hp
    have hp' : L p x - σ p < 0 := hp
    have hmemp : x ∈ halfSpace (L p) (σ p) true := by show L p x ≤ σ p; linarith
    exact (Set.indicator_of_mem hmemp f).symm
  · have hnmem : x ∉ halfSpace (L p₀) (σ p₀) true := not_le.mpr hgt
    rw [Set.indicator_of_notMem hnmem]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    have hset : {p : P | 0 < L p x - σ p} ∈ 𝓝 p₀ := by
      refine IsOpen.mem_nhds (isOpen_lt continuous_const (hev x)) ?_
      show 0 < L p₀ x - σ p₀
      linarith
    filter_upwards [hset] with p hp
    have hp' : 0 < L p x - σ p := hp
    have hnmemp : x ∉ halfSpace (L p) (σ p) true := by
      show ¬ (L p x ≤ σ p)
      push_neg
      linarith
    exact (Set.indicator_of_notMem hnmemp f).symm

/-- The cut mass is jointly continuous on `(direction, level)` pairs with nonzero direction:
`Arlib.continuousOn_setIntegral_halfSpace_param` with the tautological family. -/
theorem continuousOn_setIntegral_halfSpace_pair {f : E → ℝ} {C : Set E} (hf : IntegrableOn f C μ) :
    ContinuousOn (fun p : (E →L[ℝ] ℝ) × ℝ => ∫ x in C ∩ halfSpace p.1 p.2 true, f x ∂μ)
      {p : (E →L[ℝ] ℝ) × ℝ | p.1 ≠ 0} :=
  continuousOn_setIntegral_halfSpace_param hf continuous_fst continuous_snd

end Continuity

/-! ### The intermediate value step along a family of cuts -/

section Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **A preconnected, reversal-closed family of cuts contains one that bisects any given
integrand.**

Let `T` be a family of oriented cuts `(L, s)`, all with `L ≠ 0`, which is preconnected and contains
some cut together with its reverse `(-L, -s)`.  Then some member of `T` splits `∫_C h` into two
exactly equal halves — for a **signed** `h`, with no hypothesis on `h` beyond integrability.

The proof is the intermediate value theorem: the mass `Ψ (L,s) = ∫_{C ∩ {L ≤ s}} h` is continuous
on `T` (`Arlib.continuousOn_setIntegral_halfSpace_pair`) and satisfies
`Ψ (-L,-s) = (∫_C h) - Ψ (L,s)` (`Arlib.setIntegral_halfSpace_neg`), so the two values `Ψ p₀` and
`Ψ (-p₀)` straddle `(∫_C h)/2`, which is therefore attained on the preconnected `T`.

This is the step that makes the *second* function free: everything the argument needs to know
about the *first* one is packed into the preconnectedness of `T`. -/
theorem exists_bisecting_of_preconnected_family {h : E → ℝ} {C : Set E}
    (hC : MeasurableSet C) (hhi : IntegrableOn h C μ)
    {T : Set ((E →L[ℝ] ℝ) × ℝ)} (hTpre : IsPreconnected T) (hTne : ∀ p ∈ T, p.1 ≠ 0)
    {p₀ : (E →L[ℝ] ℝ) × ℝ} (hp₀ : p₀ ∈ T) (hp₁ : (-p₀.1, -p₀.2) ∈ T) :
    ∃ p ∈ T, ∀ side : Bool,
      ∫ x in C ∩ halfSpace p.1 p.2 side, h x ∂μ = (∫ x in C, h x ∂μ) / 2 := by
  set B : ℝ := ∫ x in C, h x ∂μ with hB
  set Ψ : (E →L[ℝ] ℝ) × ℝ → ℝ := fun p => ∫ x in C ∩ halfSpace p.1 p.2 true, h x ∂μ with hΨ
  have hcont : ContinuousOn Ψ T :=
    (continuousOn_setIntegral_halfSpace_pair hhi).mono fun p hp => hTne p hp
  -- the reverse cut carries the complementary mass
  have hrev : Ψ (-p₀.1, -p₀.2) = B - Ψ p₀ := by
    have h1 : Ψ (-p₀.1, -p₀.2) = ∫ x in C ∩ halfSpace p₀.1 p₀.2 false, h x ∂μ :=
      setIntegral_halfSpace_neg (hTne p₀ hp₀) p₀.2 true
    have h2 := setIntegral_halfSpace_add hhi hC p₀.1 p₀.2
    rw [h1]
    linarith
  -- the intermediate value theorem on the preconnected family
  have hmem : ∃ p ∈ T, Ψ p = B / 2 := by
    rcases le_total (Ψ p₀) (B / 2) with hle | hle
    · have hIcc : B / 2 ∈ Icc (Ψ p₀) (Ψ (-p₀.1, -p₀.2)) := ⟨hle, by rw [hrev]; linarith⟩
      obtain ⟨p, hpT, hpv⟩ := hTpre.intermediate_value hp₀ hp₁ hcont hIcc
      exact ⟨p, hpT, hpv⟩
    · have hIcc : B / 2 ∈ Icc (Ψ (-p₀.1, -p₀.2)) (Ψ p₀) := ⟨by rw [hrev]; linarith, hle⟩
      obtain ⟨p, hpT, hpv⟩ := hTpre.intermediate_value hp₁ hp₀ hcont hIcc
      exact ⟨p, hpT, hpv⟩
  obtain ⟨p, hpT, hpv⟩ := hmem
  refine ⟨p, hpT, fun side => ?_⟩
  have hsum := setIntegral_halfSpace_add hhi hC p.1 p.2
  cases side
  · show ∫ x in C ∩ halfSpace p.1 p.2 false, h x ∂μ = B / 2
    have : Ψ p = ∫ x in C ∩ halfSpace p.1 p.2 true, h x ∂μ := rfl
    rw [this] at hpv
    linarith
  · exact hpv

end Family

/-! ### Through every point, in some direction — for a single signed integrand -/

section Pivot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The functional `⟪u, ·⟫` is nonzero as soon as `u` is. -/
theorem innerSL_ne_zero {u : E} (hu : u ≠ 0) : (innerSL ℝ u : E →L[ℝ] ℝ) ≠ 0 := by
  intro hz
  have huu : inner ℝ u u = (0 : ℝ) := by
    have := congrArg (fun T : E →L[ℝ] ℝ => T u) hz
    simpa using this
  exact hu (inner_self_eq_zero.mp huu)

/-- `2 ≤ finrank ℝ E` in the form Mathlib's connectedness lemmas want. -/
theorem one_lt_rank_of_two_le_finrank (h2 : 2 ≤ Module.finrank ℝ E) : 1 < Module.rank ℝ E := by
  have h : ((2 : ℕ) : Cardinal) ≤ ((Module.finrank ℝ E : ℕ) : Cardinal) := by exact_mod_cast h2
  have hrank : ((Module.finrank ℝ E : ℕ) : Cardinal) = Module.rank ℝ E :=
    Module.finrank_eq_rank' ℝ E
  rw [hrank] at h
  refine lt_of_lt_of_le ?_ h
  exact_mod_cast one_lt_two

/-- The map sending a nonzero vector to the corresponding direction is continuous. -/
theorem continuous_innerSL_prod :
    Continuous fun p : E × ℝ => ((innerSL ℝ p.1 : E →L[ℝ] ℝ), p.2) :=
  Continuous.prodMk ((innerSL ℝ (E := E)).continuous.comp continuous_fst) continuous_snd

/-- `Arlib.continuousOn_setIntegral_halfSpace_param` with the direction given by a vector. -/
theorem continuousOn_setIntegral_halfSpace_dir {f : E → ℝ} {C : Set E} (hf : IntegrableOn f C μ) :
    ContinuousOn (fun p : E × ℝ => ∫ x in C ∩ halfSpace (innerSL ℝ p.1) p.2 true, f x ∂μ)
      {p : E × ℝ | p.1 ≠ 0} :=
  ContinuousOn.mono
    (continuousOn_setIntegral_halfSpace_param hf
      ((innerSL ℝ (E := E)).continuous.comp continuous_fst) continuous_snd)
    (fun p hp => innerSL_ne_zero hp)

/-- `Arlib.exists_bisecting_of_preconnected_family` with directions given by vectors. -/
theorem exists_bisecting_of_preconnected_family_dir {h : E → ℝ} {C : Set E}
    (hC : MeasurableSet C) (hhi : IntegrableOn h C μ)
    {T : Set (E × ℝ)} (hTpre : IsPreconnected T) (hTne : ∀ p ∈ T, p.1 ≠ 0)
    {p₀ : E × ℝ} (hp₀ : p₀ ∈ T) (hp₁ : (-p₀.1, -p₀.2) ∈ T) :
    ∃ p ∈ T, ∀ side : Bool,
      ∫ x in C ∩ halfSpace (innerSL ℝ p.1) p.2 side, h x ∂μ = (∫ x in C, h x ∂μ) / 2 := by
  have himg : IsPreconnected ((fun p : E × ℝ => ((innerSL ℝ p.1 : E →L[ℝ] ℝ), p.2)) '' T) :=
    hTpre.image _ continuous_innerSL_prod.continuousOn
  have hne : ∀ q ∈ (fun p : E × ℝ => ((innerSL ℝ p.1 : E →L[ℝ] ℝ), p.2)) '' T, q.1 ≠ 0 := by
    rintro q ⟨r, hr, rfl⟩
    exact innerSL_ne_zero (hTne r hr)
  have hq₀ : ((innerSL ℝ p₀.1 : E →L[ℝ] ℝ), p₀.2)
      ∈ (fun p : E × ℝ => ((innerSL ℝ p.1 : E →L[ℝ] ℝ), p.2)) '' T := ⟨p₀, hp₀, rfl⟩
  have hq₁ : (-(innerSL ℝ p₀.1 : E →L[ℝ] ℝ), -p₀.2)
      ∈ (fun p : E × ℝ => ((innerSL ℝ p.1 : E →L[ℝ] ℝ), p.2)) '' T := by
    refine ⟨(-p₀.1, -p₀.2), hp₁, ?_⟩
    simp
  obtain ⟨q, hqmem, hqv⟩ :=
    exists_bisecting_of_preconnected_family hC hhi himg hne hq₀ hq₁
  obtain ⟨r, hr, rfl⟩ := hqmem
  exact ⟨r, hr, hqv⟩

/-- **Through every point of the space there is a bisecting hyperplane, for a signed integrand.**

Given a bounded measurable `C` and an integrable, possibly **signed**, `f`, and any prescribed
point `a`, there is a nonzero direction `L` such that the hyperplane `{L = L a}` — which passes
through `a` — splits `∫_C f` into two exactly equal halves.

This is the honest signed counterpart of `Arlib.exists_massCentre_halfSpace_pos`.  For `f ≥ 0` the
mass centre works in *every* direction; for signed `f` the statement below is what survives:
*every* point works in *some* direction.  The proof is
`Arlib.exists_bisecting_of_preconnected_family_dir` applied to the family of all cuts through `a`,
which is the continuous image of the connected punctured space `E ∖ {0}` and is closed under
reversal.

The direction produced depends on `f`, and nothing here makes the directions produced for two
different integrands agree — which is exactly the gap discussed in the module docstring. -/
theorem exists_bisecting_halfSpace_through_point (h2 : 2 ≤ Module.finrank ℝ E) {f : E → ℝ}
    {C : Set E} (hC : MeasurableSet C) (hfi : IntegrableOn f C μ) (a : E) :
    ∃ L : E →L[ℝ] ℝ, L ≠ 0 ∧ ∀ side : Bool,
      ∫ x in C ∩ halfSpace L (L a) side, f x ∂μ = (∫ x in C, f x ∂μ) / 2 := by
  classical
  have hconn : IsConnected ({(0 : E)}ᶜ : Set E) :=
    isConnected_compl_singleton_of_one_lt_rank (one_lt_rank_of_two_le_finrank h2) 0
  have hφc : Continuous fun u : E => (u, (inner ℝ u a : ℝ)) :=
    Continuous.prodMk continuous_id ((innerSL ℝ (E := E)).continuous.clm_apply continuous_const)
  have hTpre : IsPreconnected ((fun u : E => (u, (inner ℝ u a : ℝ))) '' ({(0 : E)}ᶜ)) :=
    hconn.isPreconnected.image _ hφc.continuousOn
  have hTne : ∀ p ∈ (fun u : E => (u, (inner ℝ u a : ℝ))) '' ({(0 : E)}ᶜ), p.1 ≠ 0 := by
    rintro p ⟨u, hu, rfl⟩
    exact hu
  obtain ⟨u₀, hu₀⟩ := hconn.nonempty
  have hu₀' : u₀ ≠ 0 := hu₀
  have hp₀ : (u₀, (inner ℝ u₀ a : ℝ)) ∈ (fun u : E => (u, (inner ℝ u a : ℝ))) '' ({(0 : E)}ᶜ) :=
    ⟨u₀, hu₀, rfl⟩
  have hp₁ : (-u₀, -(inner ℝ u₀ a : ℝ))
      ∈ (fun u : E => (u, (inner ℝ u a : ℝ))) '' ({(0 : E)}ᶜ) := by
    refine ⟨-u₀, ?_, ?_⟩
    · simpa using neg_ne_zero.mpr hu₀'
    · simp
  obtain ⟨p, hpmem, hpv⟩ :=
    exists_bisecting_of_preconnected_family_dir hC hfi hTpre hTne hp₀ hp₁
  obtain ⟨u, hu, rfl⟩ := hpmem
  refine ⟨innerSL ℝ u, innerSL_ne_zero hu, fun side => ?_⟩
  have hlev : (innerSL ℝ u : E →L[ℝ] ℝ) a = (inner ℝ u a : ℝ) := by simp
  rw [hlev]
  exact hpv side

/-- **Through every point there is a two-sided cut, for a single signed integrand.**

Immediate from `Arlib.exists_bisecting_halfSpace_through_point`: both sides carry exactly
`(∫_C f)/2 > 0`. -/
theorem exists_two_sided_halfSpace_through_point (h2 : 2 ≤ Module.finrank ℝ E) {f : E → ℝ}
    {C : Set E} (hC : MeasurableSet C) (hfi : IntegrableOn f C μ)
    (hpos : 0 < ∫ x in C, f x ∂μ) (a : E) :
    ∃ L : E →L[ℝ] ℝ, L ≠ 0 ∧ ∀ side : Bool,
      0 < ∫ x in C ∩ halfSpace L (L a) side, f x ∂μ := by
  obtain ⟨L, hL, hbis⟩ := exists_bisecting_halfSpace_through_point h2 hC hfi a
  exact ⟨L, hL, fun side => by rw [hbis side]; linarith⟩

end Pivot

/-! ### (P1) for a signed `g` with interval level sets, and an arbitrary signed `h` -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **(P1) for signed integrands, under an interval hypothesis on the first one.**

Let `C` be bounded and measurable, `g, h` integrable on `C` with `∫_C g > 0` and `∫_C h > 0`, and
`2 ≤ finrank ℝ E`.  Assume that for every nonzero direction `L` the set of levels at which the cut
`{L ≤ s}` is two-sided **for `g`** is an interval.  Then there are a nonzero direction `L` and a
level `s` such that both sides of `{L ≤ s}` carry positive `g`-mass, and both carry exactly half of
`∫_C h`.

Neither `g` nor `h` is assumed nonnegative, and `h` carries **no** hypothesis at all beyond
integrability and `∫_C h > 0`.  The interval hypothesis is a statement about the one-dimensional
marginals of `g` alone; `Arlib.ordConnected_two_sided_levels_of_nonneg` discharges it for `g ≥ 0`,
so the theorem is not vacuous and strictly contains `Arlib.exists_two_sided_halfSpace`.

Proof: the family `T` of two-sided cuts for `g` is open (joint continuity,
`Arlib.continuousOn_setIntegral_halfSpace_dir`), has nonempty fibres over every direction
(`Arlib.exists_two_sided_halfSpace_single`, an intermediate value theorem in one variable) and — by
hypothesis — preconnected ones, so it is preconnected over the connected punctured space `E ∖ {0}`
(`Arlib.isPreconnected_of_isOpen_of_fibers`); it is closed under reversal
(`Arlib.setIntegral_halfSpace_neg`); and then
`Arlib.exists_bisecting_of_preconnected_family_dir` finds a member bisecting `h`. -/
theorem exists_two_sided_halfSpace_of_ordConnected (h2 : 2 ≤ Module.finrank ℝ E) {g h : E → ℝ}
    {C : Set E} (hC : MeasurableSet C) (hCb : IsBounded C)
    (hgi : IntegrableOn g C μ) (hhi : IntegrableOn h C μ)
    (hgpos : 0 < ∫ x in C, g x ∂μ) (hhpos : 0 < ∫ x in C, h x ∂μ)
    (hord : ∀ L : E →L[ℝ] ℝ, L ≠ 0 →
      {s : ℝ | ∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ}.OrdConnected) :
    ∃ (L : E →L[ℝ] ℝ) (s : ℝ), L ≠ 0 ∧
      (∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ) ∧
      (∀ side : Bool, ∫ x in C ∩ halfSpace L s side, h x ∂μ = (∫ x in C, h x ∂μ) / 2) := by
  classical
  -- two-sidedness, in terms of the mass of the `true` side alone
  have hchar : ∀ (L : E →L[ℝ] ℝ) (s : ℝ),
      (∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ)
        ↔ (∫ x in C ∩ halfSpace L s true, g x ∂μ) ∈ Ioo 0 (∫ x in C, g x ∂μ) := by
    intro L s
    have hsum := setIntegral_halfSpace_add hgi hC L s
    constructor
    · intro hh
      have h1 := hh true
      have h2 := hh false
      exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩ side
      cases side
      · show 0 < ∫ x in C ∩ halfSpace L s false, g x ∂μ
        linarith
      · exact h1
  -- the family of two-sided cuts, as an opaque set with a membership equation
  obtain ⟨T, hTdef⟩ : ∃ T : Set (E × ℝ), T = {p : E × ℝ | p.1 ≠ 0 ∧
      ∀ side : Bool, 0 < ∫ x in C ∩ halfSpace (innerSL ℝ p.1) p.2 side, g x ∂μ} := ⟨_, rfl⟩
  have hTmem : ∀ p : E × ℝ, p ∈ T ↔ p.1 ≠ 0 ∧
      ∀ side : Bool, 0 < ∫ x in C ∩ halfSpace (innerSL ℝ p.1) p.2 side, g x ∂μ := by
    intro p; rw [hTdef]; exact Iff.rfl
  -- it is open
  have hTopen : IsOpen T := by
    have hTeq : T = {p : E × ℝ | p.1 ≠ 0} ∩
        (fun p : E × ℝ => ∫ x in C ∩ halfSpace (innerSL ℝ p.1) p.2 true, g x ∂μ) ⁻¹'
          (Ioo 0 (∫ x in C, g x ∂μ)) := by
      ext p
      rw [hTmem p]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hchar (innerSL ℝ p.1) p.2).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hchar (innerSL ℝ p.1) p.2).mpr h2⟩
    rw [hTeq]
    exact (continuousOn_setIntegral_halfSpace_dir hgi).isOpen_inter_preimage
      (isOpen_compl_singleton.preimage continuous_fst) isOpen_Ioo
  -- the base is connected, the fibres are nonempty and preconnected
  have hconn : IsConnected ({(0 : E)}ᶜ : Set E) :=
    isConnected_compl_singleton_of_one_lt_rank (one_lt_rank_of_two_le_finrank h2) 0
  have hne : ∀ u ∈ ({(0 : E)}ᶜ : Set E), ∃ s : ℝ, (u, s) ∈ T := by
    intro u hu
    have hu' : u ≠ 0 := hu
    obtain ⟨s, hs⟩ := exists_two_sided_halfSpace_single hC hCb hgi (innerSL_ne_zero hu') hgpos
    exact ⟨s, (hTmem (u, s)).mpr ⟨hu', hs⟩⟩
  have hfib : ∀ u ∈ ({(0 : E)}ᶜ : Set E), IsPreconnected {s : ℝ | (u, s) ∈ T} := by
    intro u hu
    have hu' : u ≠ 0 := hu
    have hset : {s : ℝ | (u, s) ∈ T}
        = {s : ℝ | ∀ side : Bool, 0 < ∫ x in C ∩ halfSpace (innerSL ℝ u) s side, g x ∂μ} := by
      ext s
      rw [Set.mem_setOf_eq, hTmem (u, s)]
      exact ⟨fun hp => hp.2, fun hp => ⟨hu', hp⟩⟩
    rw [hset]
    exact (hord (innerSL ℝ u) (innerSL_ne_zero hu')).isPreconnected
  have hTpre : IsPreconnected T :=
    isPreconnected_of_isOpen_of_fibers hconn.isPreconnected hTopen
      (fun p hp => ((hTmem p).mp hp).1) hne hfib
  -- it is closed under reversal
  obtain ⟨u₀, hu₀⟩ := hconn.nonempty
  have hu₀' : u₀ ≠ 0 := hu₀
  obtain ⟨s₀, hs₀⟩ := hne u₀ hu₀
  have hrev : ((-u₀, -s₀) : E × ℝ) ∈ T := by
    refine (hTmem (-u₀, -s₀)).mpr ⟨by simpa using neg_ne_zero.mpr hu₀', fun side => ?_⟩
    have hL : (innerSL ℝ (-u₀) : E →L[ℝ] ℝ) = -(innerSL ℝ u₀) := by simp
    show 0 < ∫ x in C ∩ halfSpace (innerSL ℝ (-u₀)) (-s₀) side, g x ∂μ
    rw [hL, setIntegral_halfSpace_neg (innerSL_ne_zero hu₀') s₀ side]
    exact ((hTmem (u₀, s₀)).mp hs₀).2 (!side)
  obtain ⟨p, hpT, hpv⟩ :=
    exists_bisecting_of_preconnected_family_dir hC hhi hTpre
      (fun q hq => ((hTmem q).mp hq).1) hs₀ hrev
  exact ⟨innerSL ℝ p.1, p.2, innerSL_ne_zero ((hTmem p).mp hpT).1,
    ((hTmem p).mp hpT).2, hpv⟩

/-- **An odd continuous selection of two-sided levels for `g` produces a common cut.**

This is the reduction in its sharpest form, and it is *not* a corollary of the interval hypothesis
— it is an alternative, and formally weaker-looking, input.  Suppose there is a function `lev`,
continuous on the nonzero vectors and **odd** (`lev (-u) = - lev u`), such that for every nonzero
`u` the cut at level `lev u` orthogonal to `u` is two-sided for `g`.  Then some member of that
one-parameter family bisects an arbitrary signed `h` exactly, and is two-sided for `g`.

No integrability, boundedness or positivity hypothesis on `g` is needed here: everything `g` has to
contribute is packed into `lev`.  The oddness is exactly the requirement that the family contain
each of its cuts with both orientations, which is what makes the `h`-mass an odd continuous
function on a connected set.

So the residual content of (P1) for signed integrands is: *does a signed `g` always admit an odd
continuous selection of two-sided levels?*  For `g ≥ 0` in a fixed direction the two-sided levels
form an interval and one may hope to select continuously; for signed `g` the two-sided levels form
an open set whose components appear and disappear as `u` turns, and a continuous selection may fail
to exist.  `Arlib.exists_bisecting_halfSpace_through_point` gives one family of such selections —
`lev u = ⟪u, a⟫` for a fixed point `a` — but only after `g` is fixed, and only for the *bisecting*
level, so it does not make the choices for two different integrands agree. -/
theorem exists_two_sided_halfSpace_of_odd_selection (h2 : 2 ≤ Module.finrank ℝ E) {g h : E → ℝ}
    {C : Set E} (hC : MeasurableSet C) (hhi : IntegrableOn h C μ)
    {lev : E → ℝ} (hlev : ContinuousOn lev {u : E | u ≠ 0})
    (hodd : ∀ u : E, u ≠ 0 → lev (-u) = - lev u)
    (hts : ∀ u : E, u ≠ 0 → ∀ side : Bool,
      0 < ∫ x in C ∩ halfSpace (innerSL ℝ u) (lev u) side, g x ∂μ) :
    ∃ (L : E →L[ℝ] ℝ) (s : ℝ), L ≠ 0 ∧
      (∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ) ∧
      (∀ side : Bool, ∫ x in C ∩ halfSpace L s side, h x ∂μ = (∫ x in C, h x ∂μ) / 2) := by
  classical
  have hconn : IsConnected ({(0 : E)}ᶜ : Set E) :=
    isConnected_compl_singleton_of_one_lt_rank (one_lt_rank_of_two_le_finrank h2) 0
  have hφ : ContinuousOn (fun u : E => (u, lev u)) ({(0 : E)}ᶜ : Set E) :=
    ContinuousOn.prodMk continuousOn_id hlev
  have hTpre : IsPreconnected ((fun u : E => (u, lev u)) '' ({(0 : E)}ᶜ : Set E)) :=
    hconn.isPreconnected.image _ hφ
  have hTne : ∀ p ∈ (fun u : E => (u, lev u)) '' ({(0 : E)}ᶜ : Set E), p.1 ≠ 0 := by
    rintro p ⟨u, hu, rfl⟩
    exact hu
  obtain ⟨u₀, hu₀⟩ := hconn.nonempty
  have hu₀' : u₀ ≠ 0 := hu₀
  have hp₀ : (u₀, lev u₀) ∈ (fun u : E => (u, lev u)) '' ({(0 : E)}ᶜ : Set E) := ⟨u₀, hu₀, rfl⟩
  have hp₁ : (-u₀, -lev u₀) ∈ (fun u : E => (u, lev u)) '' ({(0 : E)}ᶜ : Set E) := by
    refine ⟨-u₀, by simpa using neg_ne_zero.mpr hu₀', ?_⟩
    simp [hodd u₀ hu₀']
  obtain ⟨p, hpmem, hpv⟩ :=
    exists_bisecting_of_preconnected_family_dir hC hhi hTpre hTne hp₀ hp₁
  obtain ⟨u, hu, rfl⟩ := hpmem
  exact ⟨innerSL ℝ u, lev u, innerSL_ne_zero hu, hts u hu, hpv⟩

/-- **A nonnegative integrand has interval level sets, in every direction.**

For `g ≥ 0` on `C` the mass `s ↦ ∫_{C ∩ {L ≤ s}} g` is nondecreasing and the complementary mass is
nonincreasing, so the set of two-sided levels is an interval.  This discharges the hypothesis of
`Arlib.exists_two_sided_halfSpace_of_ordConnected`. -/
theorem ordConnected_two_sided_levels_of_nonneg {g : E → ℝ} {C : Set E}
    (hC : MeasurableSet C) (hgi : IntegrableOn g C μ) (hgnn : ∀ x ∈ C, 0 ≤ g x)
    (L : E →L[ℝ] ℝ) :
    {s : ℝ | ∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ}.OrdConnected := by
  have hmono : ∀ {a b : ℝ}, a ≤ b →
      ∫ x in C ∩ halfSpace L a true, g x ∂μ ≤ ∫ x in C ∩ halfSpace L b true, g x ∂μ := by
    intro a b hab
    refine setIntegral_mono_set (hgi.mono_set inter_subset_left) ?_ ?_
    · filter_upwards [ae_restrict_mem (hC.inter (measurableSet_halfSpace L b true))]
        with x hx using hgnn x hx.1
    · refine LE.le.eventuallyLE ?_
      rintro x ⟨hxC, hx⟩
      exact ⟨hxC, le_trans hx hab⟩
  have hanti : ∀ {a b : ℝ}, a ≤ b →
      ∫ x in C ∩ halfSpace L b false, g x ∂μ ≤ ∫ x in C ∩ halfSpace L a false, g x ∂μ := by
    intro a b hab
    refine setIntegral_mono_set (hgi.mono_set inter_subset_left) ?_ ?_
    · filter_upwards [ae_restrict_mem (hC.inter (measurableSet_halfSpace L a false))]
        with x hx using hgnn x hx.1
    · refine LE.le.eventuallyLE ?_
      rintro x ⟨hxC, hx⟩
      exact ⟨hxC, lt_of_le_of_lt hab hx⟩
  constructor
  rintro p hp q hq s ⟨hps, hsq⟩ side
  cases side
  · exact lt_of_lt_of_le (hq false) (hanti hsq)
  · exact lt_of_lt_of_le (hp true) (hmono hps)

/-- **(P1) with the second integrand signed.**

For `g ≥ 0` on `C` and a **completely arbitrary signed** `h`, there is a cut both of whose sides
carry positive `g`-mass and exactly half of `∫_C h`.

This strictly strengthens `Arlib.exists_two_sided_halfSpace`, which requires `h ≥ 0` as well; the
mass-centre argument there cannot give it, because the mass centre of a signed `h` is meaningless.
It is not, however, the signed statement the localisation argument needs, which has **both**
integrands signed; see the module docstring. -/
theorem exists_two_sided_halfSpace_signed_snd (h2 : 2 ≤ Module.finrank ℝ E) {g h : E → ℝ}
    {C : Set E} (hC : MeasurableSet C) (hCb : IsBounded C)
    (hgi : IntegrableOn g C μ) (hhi : IntegrableOn h C μ) (hgnn : ∀ x ∈ C, 0 ≤ g x)
    (hgpos : 0 < ∫ x in C, g x ∂μ) (hhpos : 0 < ∫ x in C, h x ∂μ) :
    ∃ (L : E →L[ℝ] ℝ) (s : ℝ), L ≠ 0 ∧
      (∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ) ∧
      (∀ side : Bool, ∫ x in C ∩ halfSpace L s side, h x ∂μ = (∫ x in C, h x ∂μ) / 2) :=
  exists_two_sided_halfSpace_of_ordConnected h2 hC hCb hgi hhi hgpos hhpos
    fun L _ => ordConnected_two_sided_levels_of_nonneg hC hgi hgnn L

/-- **Non-vacuity: the hypotheses of the signed theorem are simultaneously satisfiable.**

A closed statement with no hypotheses: on the Euclidean plane, the unit ball with `g = 1` satisfies
the interval hypothesis of `Arlib.exists_two_sided_halfSpace_of_ordConnected`, so that theorem is
not vacuously true.  (Compare `Arlib.exists_two_sided_halfSpace_ball`.) -/
theorem exists_two_sided_halfSpace_of_ordConnected_ball :
    ∃ (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (s : ℝ), L ≠ 0 ∧
      (∀ side : Bool,
        0 < ∫ _x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ halfSpace L s side,
              (1 : ℝ)) ∧
      (∀ side : Bool,
        ∫ _x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ halfSpace L s side, (1 : ℝ)
          = (∫ _x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, (1 : ℝ)) / 2) := by
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
  exact exists_two_sided_halfSpace_signed_snd (μ := volume) (by simp)
    hC hCb hi hi (fun _ _ => zero_le_one) hpos hpos

end Main

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`.  There are no
`axiom` declarations, no `sorry` and no `native_decide` anywhere in this file, and no `def`,
`structure`, `class` or `Prop` naming the statement that is not proved. -/

#print axioms isPreconnected_of_isOpen_of_fibers
#print axioms setIntegral_halfSpace_neg
#print axioms continuousOn_setIntegral_halfSpace_param
#print axioms continuousOn_setIntegral_halfSpace_pair
#print axioms continuousOn_setIntegral_halfSpace_dir
#print axioms exists_bisecting_of_preconnected_family
#print axioms exists_bisecting_of_preconnected_family_dir
#print axioms exists_bisecting_halfSpace_through_point
#print axioms exists_two_sided_halfSpace_through_point
#print axioms exists_two_sided_halfSpace_of_ordConnected
#print axioms exists_two_sided_halfSpace_of_odd_selection
#print axioms ordConnected_two_sided_levels_of_nonneg
#print axioms exists_two_sided_halfSpace_signed_snd
#print axioms exists_two_sided_halfSpace_of_ordConnected_ball

end Arlib
