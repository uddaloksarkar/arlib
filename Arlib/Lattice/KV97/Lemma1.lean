/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Lattice.Basic
import Arlib.Lattice.KV97.Inflate
import Arlib.Lattice.Rounding.ProdKernel
import Arlib.Lattice.Rounding.RoundLaw
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Kannan–Vempala, Lemma 1: the acceptance probability of the rejection step

Kannan–Vempala's lattice-point sampler draws a point `p` from an (approximately
uniform) distribution on the **inflated** polytope `P' = inflated A b c r`, rounds
it to a lattice point, and **repeats until `rnd p ∈ P`**.  This module proves that
loop is cheap: the acceptance probability

    Pr[rnd p ∈ P]  =  ∑_{x ∈ P ∩ ℤⁿ} Pr[rnd p = x]

is bounded below by an absolute constant, so the expected number of draws before
acceptance is `O(1)`.  The argument is the one written out at
`sections/proof-appendix.tex:181-185`:

    Pr[rnd p ∈ P]  ≥  (1−θ)N / Vol(P')  ≥  (1−θ) / ((1+η)(1 + κ/γ)ⁿ),

using `Vol(P') ≤ (1 + κ/γ)ⁿ Vol(P)` and `Vol(P) ≤ (1+η)N`, "which is bounded
below by a constant whenever `κ/γ = O(1/n)` — precisely what the choice of `ρ`
made by `GetPrecision` arranges".

## The seven steps

1. **The definition.**  `Arlib.KV97.acceptance pt w = ∑ i, w (pt i)`, the sum of
   the per-lattice-point weights over a `Fintype` index `ι` of lattice points,
   injected into space by `pt`.  `Arlib.KV97.acceptance_eq_sum_image` says that
   for injective `pt` this really is the sum over the *set* `pt '' ι`, i.e. over
   `P ∩ ℤⁿ`.
2. **The bridge — the sum is a probability.**  `Arlib.KV97.acceptance_eq_measure`
   and `Arlib.KV97.acceptance_eq_measure_apply` prove
   `Pr[rnd p ∈ P] = ∑_{x ∈ P ∩ ℤⁿ} Pr[rnd p = x] = acceptance pt w` for an actual
   measure, rather than asserting it in prose.  See "What the bridge needs".
3. **The bridge at the real kernel.**
   `Arlib.KV97.acceptance_eq_setIntegral_roundLaw` instantiates step 2 at
   `Arlib.Lattice.Rounding.roundLaw`, the law of the randomized rounding, and at
   Theorem 2's weight `w x = ∫_{P'} f p · prodTent x p dp`:
   `acceptance pt w = ∫_{P'} f p · Pr[rnd p ∈ P] dp`.
   `Arlib.KV97.toReal_roundedLaw_eq_acceptance` finishes the job against a single
   measure: `Arlib.KV97.roundedLaw`, the law of the rounded draw itself (the Giry
   bind of the kernel against the density, which needed
   `Arlib.KV97.measurable_roundLaw`), satisfies
   `Pr[rnd p ∈ P] = acceptance pt w` outright.
4. **The sum.**  `Arlib.KV97.acceptance_ge`: the per-point lower bound
   `(1−ε)(1−E)/V` summed over the `N` points gives `N(1−ε)(1−E)/V`.
5. **The geometry.**  `Arlib.KV97.acceptance_ge_const`: `V = Vol(P')` is
   eliminated with `Arlib.KV97.inv_pow_le_toReal_volume_ratio` and the
   lattice-point bound, leaving `(1−ε)(1−E) / ((1+η)(1 + κ/γ)ⁿ)`.
6. **The constant.**  `Arlib.KV97.one_add_div_pow_le_exp`: `(1 + t)ⁿ ≤ e` once
   `t ≤ 1/n`, so the bound becomes `(1−ε)(1−E)/((1+η)·e)`
   (`Arlib.KV97.acceptance_ge_exp`), and at `ε, E, η ≤ 1/4` it is the explicit
   number `9/(20e)` (`Arlib.KV97.acceptance_ge_nine_div_twenty_exp`).
7. **The headline, about a measure.**
   `Arlib.KV97.toReal_roundedLaw_ge_one_eighth` composes steps 3 and 6:
   `(roundedLaw P' f) {z | z ∈ P} ≥ 1/8`, a bound on a mass of the law of the
   rounded draw rather than on a sum of weights.

## The honest constant is `9/(20·e) ≈ 0.165546`, and it does clear the paper's `1/8`

At `ε, E, η ≤ 1/4` the bound is `(3/4)(3/4) / ((5/4)·e) = 9/(20e) ≈ 0.165546`,
which is what `Arlib.KV97.acceptance_ge_nine_div_twenty_exp` states.  It is
larger than the `1/8 = 0.125` the paper claims, so the paper's number follows
(`Arlib.KV97.acceptance_ge_one_eighth`, via
`Arlib.KV97.one_eighth_le_nine_div_twenty_exp`).  The `1/8` is *not* the sharp
constant of this argument — it is a round number below it.  Neither the `1/4`
budgets nor the `κ/γ ≤ 1/n` regime are forced by anything upstream; they are the
regime in which the paper's "bounded below by a constant" is being cashed out,
and different budgets give a different constant by the same two lemmas.

## What is assumed here, and where it is really proved

**`hlattice_nonconv : Vol(P).toReal ≤ (1+η)·N` is NOT proved in `Arlib`.**  It is
`lem:nonconv` / `lem:lattice` of the consuming paper, whose formal proof lives in
the `Ttc` project (`Ttc/Nonconv/Assembled.lean`, `Ttc/Lattice/Assembled.lean`).
No file under `Arlib/` may import `Ttc.*`, so it is carried as an explicit
hypothesis — deliberately given a long name — on every statement that uses it.
Do not mistake it for something this library establishes.

**`hlow` is Theorem 2's lower half.**  The hypothesis
`∀ i, (1−ε)(1−E)/Vol(P') ≤ w (pt i)` is exactly the conclusion of
`Arlib.KV97.theorem2_lower` with `w x = ∫ p in P', f p * prodTent x p`.  This
module does **not** import `Arlib/Lattice/KV97/Theorem2.lean`: the *bounds* need
only the real-number inequality, and a caller supplies `w` and discharges `hlow`
from `theorem2_lower`.  Step 3 of the outline does import the rounding kernel
itself (`Arlib.Lattice.Rounding.ProdKernel`, `.RoundLaw`) — but not Theorem 2 —
because identifying `acceptance` with a probability is impossible without the
object whose probability it is.

**Finiteness of `P ∩ ℤⁿ` is a hypothesis, not a theorem.**  The lattice points
enter as an abstract `[Fintype ι]` together with `pt : ι → EuclideanSpace ℝ (Fin n)`;
nothing here derives that `P ∩ ℤⁿ` is finite.  (`Arlib.Lattice.finite_inter_intLattice`
does derive it for a bounded region, and a caller may use it to build the
`Fintype`.)

## What the bridge needs (the honest form of `Pr[rnd p ∈ P] = ∑ₓ Pr[rnd p = x]`)

The equation in the header of this file — and in the docstring of
`Arlib.KV97.acceptance` — is not an identity between symbols; it is a claim that
needs **three** hypotheses, none of which the prose version states.
`Arlib.KV97.acceptance_eq_measure_apply` states and uses all three:

* **`pt` is injective.**  A repeated point is counted twice by the sum and once by
  the event.  This is not a technicality that can be waved away:
  `Arlib.KV97.measure_range_lt_acceptance_of_not_injective` exhibits a probability
  measure and a two-element constant `pt` with mass `1` but `acceptance = 2`.
  **Consequence for the audit:** the non-vacuity witness
  `Arlib.KV97.exp_neg_one_le_acceptance_cube` takes `pt` constant, so *for that
  witness `acceptance` is not a probability*.  It witnesses that the hypothesis
  bundle of the bounds is inhabited — nothing more.
* **`pt` is exhaustive**: `P ∩ ℤⁿ = Set.range pt`.  Otherwise the sum misses mass
  the event contains.  The bounds of steps 4–6 never need this, which is why it
  went unnoticed.
* **The law is carried by the lattice**: `μ (ℤⁿ)ᶜ = 0`.  Otherwise the event
  `{rnd p ∈ P}` contains non-lattice mass that no singleton accounts for.  For the
  rounding law this is free — `Arlib.Lattice.Rounding.roundLaw` is a measure on
  `ℤⁿ` to begin with — which is why step 3 states the event as
  `{z : ℤⁿ | latEmb z ∈ P}` and needs no support hypothesis at all.

A fourth, technical, side-condition: each point mass must be finite
(`μ {pt i} ≠ ⊤`), since `ENNReal.toReal ⊤ = 0`.  It is automatic for a probability
measure (`Arlib.KV97.acceptance_eq_measure_of_isProbabilityMeasure`).

**What step 3 does and does not close.**  The unconditional law of the rounded
draw did not exist as a `MeasureTheory.Measure` anywhere in this development — the
files only ever had the conditional kernel `Arlib.Lattice.Rounding.roundLaw p` and
the weight function — so `Arlib.KV97.roundedLaw` builds it here, as the Giry bind
of the kernel against the sampler's density.  That needed
`Arlib.KV97.measurable_roundLaw` (Giry-measurability of `p ↦ roundLaw p`), which
no file in `Arlib` had.  What is *not* claimed: that `roundedLaw` is a probability
measure.  `Arlib.KV97.toReal_roundedLaw_eq_acceptance` is an identity of masses
and does not assume `∫_{P'} f = 1`; a caller who wants "probability" rather than
"mass" supplies the normalisation of `f` separately.  Nor is it claimed that `f`
is the density of any *implementable* sampler — that is the standing residual
assumption of the whole KV97 development (`AUDIT-KV97.md` §2).

**`Arlib.Rejection.sum_bounds` does not apply directly.**  That lemma bundles the
lower bound with an upper bound `w i ≤ 1/V`, and Theorem 2 as formalised here
gives `w i ≤ (1+ε)/V`, not `1/V` (see `Theorem2.lean`, "The upper bound is
`(1+ε)/V`, not `1/V`").  Only the lower half is needed, and it is reproved in
three lines as `Arlib.KV97.acceptance_ge`; the two-sided
`Arlib.Rejection.ratio_bounds` machinery is for the *conditional* law, which is
`Corollary.lean`'s business, not this file's.

## Guards against vacuity (`CLAUDE.md` §11)

Divisions are guarded throughout: `Vol(P') > 0` comes from
`Arlib.KV97.toReal_volume_inflated_pos` (hence `0 < γ` and an inscribed ball are
hypotheses), and `(1+η)(1 + κ/γ)ⁿ > 0` from `0 ≤ η` and `0 ≤ c`.  Two specific
ways the conclusion could be trivially true are excluded:

* **`E ≥ 1`** would make `(1−ε)(1−E) ≤ 0` and the bound vacuous.
  `Arlib.KV97.acceptance_pos` assumes `ε < 1` and `E < 1` and concludes
  `0 < acceptance`, and the headline lemmas assume `ε, E ≤ 1/4`.
* **`N = 0`** would make the acceptance mass an empty sum.  It cannot happen:
  `Arlib.KV97.card_pos_of_lattice_bound` shows the hypotheses already force
  `0 < Fintype.card ι`, because `Vol(P) > 0` and `Vol(P) ≤ (1+η)N`.

`Arlib.KV97.exp_neg_one_le_acceptance_cube` is the concrete witness: for the cube
`{x : |xᵢ| ≤ 1}` in any dimension `d`, with `ε = E = η = 0`, `γ = 1`, `c = 0`,
`r = 1` (so `κ = 0` and `κ/γ ≤ 1/d`) and `N = ⌈Vol(P)⌉`, every hypothesis holds and
the conclusion is `acceptance ≥ e⁻¹ > 0` (`Arlib.KV97.exp_neg_one_pos`), not
`≥ 0`.  The witness's `pt` is constant.  That is harmless *for the bounds* —
injectivity is not a hypothesis of any of them — but it does mean the witness
does not satisfy the bridge of step 2, so for the witness `acceptance` is a sum of
`⌈Vol(P)⌉` equal weights and not a probability.  See "What the bridge needs".
-/

namespace Arlib.KV97

open MeasureTheory
open scoped BigOperators

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- **The acceptance mass of the rejection step**, `Pr[rnd p ∈ P]`.

`pt : ι → EuclideanSpace ℝ (Fin n)` enumerates the lattice points of `P` — the
finiteness of `P ∩ ℤⁿ` is *assumed*, as the `[Fintype ι]` instance, not derived —
and `w x` is the per-point weight `Pr[rnd p = x]`.

**The name is discharged, not asserted.**  That

    Pr[rnd p ∈ P]  =  ∑_{x ∈ P ∩ ℤⁿ} Pr[rnd p = x]  =  acceptance pt w

is `Arlib.KV97.acceptance_eq_measure_apply`, for an arbitrary measure, and
`Arlib.KV97.toReal_roundedLaw_eq_acceptance` for the actual law of the rounded
draw at Theorem 2's weight.  Both carry the hypotheses the informal equation needs and
the prose used to leave out: `pt` **injective**, `pt` **exhausting** `P ∩ ℤⁿ`, and
the law **carried by the lattice**.  Injectivity in particular is not a formality
— `Arlib.KV97.measure_range_lt_acceptance_of_not_injective` is a probability
measure with `acceptance = 2`.

None of the *bounds* below need any of this: they are inequalities between real
numbers, and remain true (but no longer statements about a probability) for a
`pt` that repeats points.  The reading of the sum as a sum over the *set* of
lattice points is `Arlib.KV97.acceptance_eq_sum_image`. -/
noncomputable def acceptance (pt : ι → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∑ i, w (pt i)

/-- Unfolding lemma for `Arlib.KV97.acceptance`. -/
theorem acceptance_def (pt : ι → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) : acceptance pt w = ∑ i, w (pt i) := rfl

/-- **The sum really is over `P ∩ ℤⁿ`.**  When `pt` is injective, the indexed sum
defining `Arlib.KV97.acceptance` equals the sum over the *set* of enumerated
lattice points, with no double counting.  This is the only place injectivity is
used. -/
theorem acceptance_eq_sum_image {pt : ι → EuclideanSpace ℝ (Fin n)}
    (hpt : Function.Injective pt) (w : EuclideanSpace ℝ (Fin n) → ℝ) :
    acceptance pt w = ∑ x ∈ Finset.univ.image pt, w x := by
  classical
  rw [acceptance_def, Finset.sum_image fun a _ b _ h => hpt h]

/-! ## The bridge: the sum really is `Pr[rnd p ∈ P]`

`Arlib.KV97.acceptance pt w` is, by its body, a finite sum of numbers; its *name*
claims it is the acceptance probability.  The lemmas in this section prove that
identification rather than asserting it, and in doing so pin down the three
hypotheses the informal equation `Pr[rnd p ∈ P] = ∑_{x ∈ P ∩ ℤⁿ} Pr[rnd p = x]`
silently uses.  See the module docstring, "What the bridge needs".
-/

section Bridge

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Finite additivity over the enumerated points.**

For an *injective* `pt` the singletons `{pt i}` are pairwise disjoint, and there
are finitely many of them (`[Fintype ι]`), so the mass of their union is the
finite sum of the point masses.  Injectivity is exactly what rules out double
counting; without it the right-hand side over-counts (see
`Arlib.KV97.measure_range_lt_acceptance_of_not_injective`). -/
theorem measure_range_eq_sum_singleton (μ : Measure α) {pt : ι → α}
    (hpt : Function.Injective pt) : μ (Set.range pt) = ∑ i, μ {pt i} := by
  classical
  have hcov : Set.range pt = ⋃ i ∈ (Finset.univ : Finset ι), ({pt i} : Set α) := by
    simp
  rw [hcov, measure_biUnion_finset
    (fun i _ j _ hij => Set.disjoint_singleton.2 (hpt.ne hij))
    (fun i _ => measurableSet_singleton _)]

/-- The real-valued form of `Arlib.KV97.measure_range_eq_sum_singleton`.  The
finiteness side-condition `μ {pt i} ≠ ⊤` is genuinely needed: `ENNReal.toReal`
sends `⊤` to `0`, so for an infinite point mass the two sides differ. -/
theorem toReal_measure_range_eq_sum_singleton {μ : Measure α} {pt : ι → α}
    (hpt : Function.Injective pt) (hfin : ∀ i, μ {pt i} ≠ ⊤) :
    (μ (Set.range pt)).toReal = ∑ i, (μ {pt i}).toReal := by
  rw [measure_range_eq_sum_singleton μ hpt, ENNReal.toReal_sum fun i _ => hfin i]

omit [Fintype ι] [MeasurableSingletonClass α] in
/-- **The enumerated points carry all of `P`.**

If `pt` enumerates `P ∩ L` — think of `L` as the lattice — and the measure gives
no mass off `L`, then `P` and the enumerated set have the same mass.  This is the
"the events `{rnd p = x}` *exhaust* `{rnd p ∈ P}`" half of the informal argument,
and it is the half the docstring's `Pr[rnd p ∈ P] = ∑_x Pr[rnd p = x]` hides:
without `hsupp` the measure could put mass on non-lattice points of `P`, and
without `henum` the enumeration could miss lattice points of `P`. -/
theorem measure_eq_measure_range (μ : Measure α) {pt : ι → α} {P L : Set α}
    (henum : P ∩ L = Set.range pt) (hsupp : μ Lᶜ = 0) :
    μ P = μ (Set.range pt) := by
  have hsub : Set.range pt ⊆ P := henum ▸ Set.inter_subset_left
  have hnull : μ (P \ Set.range pt) = 0 := by
    refine measure_mono_null (t := Lᶜ) ?_ hsupp
    intro x hx hxL
    have hxPL : x ∈ P ∩ L := ⟨hx.1, hxL⟩
    rw [henum] at hxPL
    exact hx.2 hxPL
  refine le_antisymm ?_ (measure_mono hsub)
  calc μ P = μ (Set.range pt ∪ (P \ Set.range pt)) := by rw [Set.union_sdiff_cancel hsub]
    _ ≤ μ (Set.range pt) + μ (P \ Set.range pt) := measure_union_le _ _
    _ = μ (Set.range pt) := by rw [hnull, add_zero]

end Bridge

/-- **`acceptance` is the mass of the union of the enumerated points.**

This is the shape asked for in `AUDIT-KV97.md` §4h: with `w x = (μ {x}).toReal`
the per-point mass, `acceptance pt w` is exactly `μ (⋃ i, {pt i})`.  Two
hypotheses, both real:

* `hpt` — **injectivity**.  A repeated point is counted twice by the sum and once
  by the union.  `Arlib.KV97.measure_range_lt_acceptance_of_not_injective`
  exhibits a `pt`, a probability measure and a strict inequality, so this cannot
  be dropped.
* `hfin` — each point mass is finite.  Automatic for a probability measure; see
  `Arlib.KV97.acceptance_eq_measure_of_isProbabilityMeasure`. -/
theorem acceptance_eq_measure {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {pt : ι → EuclideanSpace ℝ (Fin n)} (hpt : Function.Injective pt)
    (hfin : ∀ i, μ {pt i} ≠ ⊤) :
    (μ (⋃ i, {pt i})).toReal = acceptance pt fun x => (μ {x}).toReal := by
  rw [Set.iUnion_singleton_eq_range, acceptance_def,
    toReal_measure_range_eq_sum_singleton hpt hfin]

/-- `Arlib.KV97.acceptance_eq_measure` with `hfin` discharged: every point mass of
a probability measure is at most `1`. -/
theorem acceptance_eq_measure_of_isProbabilityMeasure
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
    {pt : ι → EuclideanSpace ℝ (Fin n)} (hpt : Function.Injective pt) :
    (μ (⋃ i, {pt i})).toReal = acceptance pt fun x => (μ {x}).toReal :=
  acceptance_eq_measure hpt fun _ => measure_ne_top μ _

/-- **`Pr[rnd p ∈ P] = acceptance pt w`, in full.**

The docstring of `Arlib.KV97.acceptance` claims exactly this equation.  Here it
is, with every hypothesis it needs made explicit:

* `hpt` — `pt` is injective (no double counting);
* `henum` — `pt` enumerates **all** of `P ∩ L`, so the events exhaust `{rnd p ∈ P}`;
* `hsupp` — the law is carried by the lattice `L`, so nothing in `P \ L` is missed;
* `hfin` — the point masses are finite.

`L` is left abstract; for the rounding law it is `Arlib.Lattice.intLattice n`
(see `Arlib.KV97.acceptance_eq_setIntegral_roundLaw`). -/
theorem acceptance_eq_measure_apply {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {pt : ι → EuclideanSpace ℝ (Fin n)} {P L : Set (EuclideanSpace ℝ (Fin n))}
    (hpt : Function.Injective pt) (hfin : ∀ i, μ {pt i} ≠ ⊤)
    (henum : P ∩ L = Set.range pt) (hsupp : μ Lᶜ = 0) :
    (μ P).toReal = acceptance pt fun x => (μ {x}).toReal := by
  rw [measure_eq_measure_range μ henum hsupp, acceptance_def,
    toReal_measure_range_eq_sum_singleton hpt hfin]

/-- **A probability is at most `1`, and so, under the bridge, is `acceptance`.**

A sanity check the un-bridged development could not state: once `acceptance` is
identified with a mass, the bounds of this file are bounds on a number in `[0,1]`.
Injectivity is again essential —
`Arlib.KV97.measure_range_lt_acceptance_of_not_injective` gives an `acceptance` of
`2` for a probability measure. -/
theorem acceptance_le_one {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
    {pt : ι → EuclideanSpace ℝ (Fin n)} (hpt : Function.Injective pt) :
    acceptance pt (fun x => (μ {x}).toReal) ≤ 1 := by
  rw [acceptance_def, ← toReal_measure_range_eq_sum_singleton hpt fun _ => measure_ne_top μ _]
  calc (μ (Set.range pt)).toReal
      ≤ (μ Set.univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.subset_univ _))
    _ = 1 := by simp

/-- **Injectivity is not optional.**

The docstring of `Arlib.KV97.acceptance` used to say that the reading of the sum
as a sum over `P ∩ ℤⁿ` "needs `pt` injective; none of the bounds below need it".
That is true of the *bounds*, but the identification of `acceptance` with a
probability needs it too, and this is the counterexample: for the constant map
`Fin 2 → ℝⁿ` and the Dirac measure at the same point, the enumerated set has mass
`1` while `acceptance` is `2`.

This matters concretely: the non-vacuity witness
`Arlib.KV97.exp_neg_one_le_acceptance_cube` takes `pt` constant, so for that
witness `acceptance` is **not** a probability — it is `⌈Vol(P)⌉` copies of one
weight.  The witness certifies that the hypothesis bundle of the *bounds* is
inhabited, nothing more. -/
theorem measure_range_lt_acceptance_of_not_injective (n : ℕ) :
    ((Measure.dirac (0 : EuclideanSpace ℝ (Fin n)))
        (Set.range (fun _ : Fin 2 => (0 : EuclideanSpace ℝ (Fin n))))).toReal
      < acceptance (fun _ : Fin 2 => (0 : EuclideanSpace ℝ (Fin n)))
          (fun x => ((Measure.dirac (0 : EuclideanSpace ℝ (Fin n))) {x}).toReal) := by
  rw [acceptance_def, Set.range_const]
  simp

/-! ## The bridge, specialised to the actual rounding kernel

The section above is about an arbitrary measure.  This one instantiates it at the
object the development really uses: `Arlib.Lattice.Rounding.roundLaw`, the law of
the randomized rounding `rnd p` for a fixed continuous draw `p`, whose point
masses are `Arlib.Lattice.Rounding.prodTent`.

What comes out is `Arlib.KV97.acceptance_eq_setIntegral_roundLaw`:

    acceptance pt (fun x => ∫ p in S, f p * prodTent x p)
      = ∫ p in S, f p * Pr[rnd p ∈ P]

whose left-hand side is `acceptance` at **exactly** Theorem 2's weight
(`Arlib.KV97.theorem2_lower`'s `w x = ∫ p in P', f p * prodTent x p`) and whose
right-hand side is the average of the *honest* conditional acceptance probability
`Pr[rnd p ∈ P] = roundLaw p {z | z ∈ P}` over the continuous draw.  So the chain
Theorem 2 → Lemma 1 is closed, not merely type-compatible.

The second block of the section removes the `∫ … dp` from the right-hand side.
The law of the rounded draw *unconditionally* — the Giry bind
`((volume.restrict P').withDensity (ENNReal.ofReal ∘ f)).bind roundLaw` — did not
exist anywhere in this development; `Arlib.KV97.roundedLaw` builds it, on the
strength of `Arlib.KV97.measurable_roundLaw`, and
`Arlib.KV97.toReal_roundedLaw_eq_acceptance` gives

    (roundedLaw P' f) {z | z ∈ P}  =  acceptance pt (fun x => ∫ p in P', f p * prodTent x p),

an identity between a mass of one honest measure and `acceptance` at Theorem 2's
weight.  It is an identity of *masses*: normalisation of `f` is not assumed, so
the word "probability" is the caller's to earn.
-/

section RoundingKernel

open Arlib.Lattice Arlib.Lattice.Rounding

/-- The lattice embedding `ℤⁿ ↪ ℝⁿ`: `Arlib.Lattice.Rounding.roundLaw` lives on
`Fin n → ℤ`, while `Arlib.KV97.acceptance` indexes weights by points of
`EuclideanSpace ℝ (Fin n)`.  Its range is `Arlib.Lattice.intLattice n`
(`Arlib.KV97.range_latEmb`). -/
noncomputable def latEmb (n : ℕ) (z : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => (z i : ℝ)

@[simp] theorem latEmb_apply (z : Fin n → ℤ) (i : Fin n) : latEmb n z i = (z i : ℝ) := rfl

theorem injective_latEmb (n : ℕ) : Function.Injective (latEmb n) := by
  intro z w h
  funext i
  have : ((z i : ℤ) : ℝ) = ((w i : ℤ) : ℝ) := by
    rw [← latEmb_apply z i, ← latEmb_apply w i, h]
  exact_mod_cast this

/-- The embedded copy of `ℤⁿ` is the integer lattice of `Arlib.Lattice.Basic`. -/
theorem range_latEmb (n : ℕ) : Set.range (latEmb n) = intLattice n :=
  (intLattice_eq_range n).symm

/-- **`Pr[rnd p = x]` really is `prodTent x p`.**  This is
`Arlib.Lattice.Rounding.roundLaw_singleton` read in `ℝⁿ` and in `ℝ` rather than
`ℝ≥0∞`: the per-point weight that Theorem 2 integrates is the point mass of the
rounding law. -/
theorem toReal_roundLaw_singleton (q : EuclideanSpace ℝ (Fin n)) (z : Fin n → ℤ) :
    (roundLaw (WithLp.ofLp q) {z}).toReal = prodTent (latEmb n z) q := by
  rw [roundLaw_singleton,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => tent_nonneg _)]
  rfl

/-- **The conditional acceptance probability is an `acceptance` sum.**

For a *fixed* continuous draw `q`, `Pr[rnd q ∈ P]` — the mass the rounding law
gives to the set of lattice points landing in `P` — is `acceptance` at the
conditional weights `w x = prodTent x q`.  The hypotheses are the honest ones:
`lat` enumerates the lattice points of `P` **injectively** (`hlat`) and
**exhaustively** (`henum`).  No measurability hypothesis on `P` is needed: the
event is rewritten to a finite union of singletons before any measure is
computed. -/
theorem toReal_roundLaw_eq_acceptance {P : Set (EuclideanSpace ℝ (Fin n))}
    {lat : ι → (Fin n → ℤ)} (hlat : Function.Injective lat)
    (henum : ∀ z, latEmb n z ∈ P ↔ ∃ i, lat i = z) (q : EuclideanSpace ℝ (Fin n)) :
    (roundLaw (WithLp.ofLp q) {z | latEmb n z ∈ P}).toReal
      = acceptance (fun i => latEmb n (lat i)) (fun x => prodTent x q) := by
  have hset : {z : Fin n → ℤ | latEmb n z ∈ P} = Set.range lat := by
    ext z; exact henum z
  rw [hset, measure_range_eq_sum_singleton _ hlat,
    ENNReal.toReal_sum fun _ _ => measure_ne_top _ _, acceptance_def]
  exact Finset.sum_congr rfl fun i _ => toReal_roundLaw_singleton q (lat i)

omit [Fintype ι] in
/-- **`henum` in the paper's shape.**  Saying "`lat` enumerates `P ∩ ℤⁿ`" as the
set equation `P ∩ intLattice n = Set.range (latEmb ∘ lat)` gives the pointwise
hypothesis `Arlib.KV97.toReal_roundLaw_eq_acceptance` consumes.  Note the
direction that needs `Arlib.KV97.injective_latEmb`: a point of `P` that happens to
be a lattice point is `latEmb` of a *unique* integer vector. -/
theorem enum_iff_of_inter_intLattice {P : Set (EuclideanSpace ℝ (Fin n))}
    {lat : ι → (Fin n → ℤ)}
    (h : P ∩ intLattice n = Set.range fun i => latEmb n (lat i)) :
    ∀ z, latEmb n z ∈ P ↔ ∃ i, lat i = z := by
  intro z
  constructor
  · intro hz
    have hmem : latEmb n z ∈ P ∩ intLattice n :=
      ⟨hz, by rw [← range_latEmb n]; exact ⟨z, rfl⟩⟩
    rw [h] at hmem
    obtain ⟨i, hi⟩ := hmem
    exact ⟨i, injective_latEmb n hi⟩
  · rintro ⟨i, rfl⟩
    have : latEmb n (lat i) ∈ P ∩ intLattice n := by rw [h]; exact ⟨i, rfl⟩
    exact this.1

/-- **Pulling the finite sum through the integral over the continuous draw.**

`acceptance` at Theorem 2's weights is the integral over `p` of `f p` times
`acceptance` at the conditional weights.  This is the only exchange of `∑` and `∫`
in the argument, and it is the finite one, so it needs nothing beyond
integrability of each summand — which is exactly the hypothesis `hint` that
`Arlib.KV97.theorem2_lower` already requires. -/
theorem acceptance_setIntegral_eq_setIntegral_acceptance
    {S : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (pt : ι → EuclideanSpace ℝ (Fin n))
    (hint : ∀ i, IntegrableOn (fun p => f p * prodTent (pt i) p) S) :
    acceptance pt (fun x => ∫ p in S, f p * prodTent x p)
      = ∫ p in S, f p * acceptance pt (fun x => prodTent x p) := by
  simp only [acceptance_def, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint i]

/-- **The chain from Theorem 2 to Lemma 1, closed.**

    acceptance pt (fun x => ∫ p in S, f p * prodTent x p)
      =  ∫ p in S, f p * Pr[rnd p ∈ P].

The left-hand side is `Arlib.KV97.acceptance` at literally the weight Theorem 2
bounds (`Arlib.KV97.theorem2_lower`: `w x = ∫ p in P', f p * prodTent x p`).  The
right-hand side is the average, over the continuous draw `p ~ f·1_S`, of the true
conditional acceptance probability of the rounding step.  So every bound in this
file — `Arlib.KV97.acceptance_ge_one_eighth` included — is a bound on that
average, i.e. on a probability, and not merely on a sum of numbers.

Hypotheses: `hlat` (injective enumeration), `henum` (exhaustive enumeration; use
`Arlib.KV97.enum_iff_of_inter_intLattice` to supply it from `P ∩ ℤⁿ = range pt`),
and `hint` (integrability, already required by Theorem 2). -/
theorem acceptance_eq_setIntegral_roundLaw {P S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {lat : ι → (Fin n → ℤ)}
    (hlat : Function.Injective lat)
    (henum : ∀ z, latEmb n z ∈ P ↔ ∃ i, lat i = z)
    (hint : ∀ i, IntegrableOn (fun p => f p * prodTent (latEmb n (lat i)) p) S) :
    acceptance (fun i => latEmb n (lat i)) (fun x => ∫ p in S, f p * prodTent x p)
      = ∫ p in S, f p * (roundLaw (WithLp.ofLp p) {z | latEmb n z ∈ P}).toReal := by
  rw [acceptance_setIntegral_eq_setIntegral_acceptance _ hint]
  simp only [toReal_roundLaw_eq_acceptance hlat henum]

/-! ### The unconditional law of the rounded draw

The lemmas above average the *conditional* acceptance probability over `p`.  This
last block builds the object that average is an average of: the law of the rounded
draw itself, as a single `MeasureTheory.Measure` on `ℤⁿ`.  It is the Giry bind of
the rounding kernel against the sampler's density, so the only genuinely new
ingredient is Giry-measurability of `p ↦ roundLaw p`
(`Arlib.KV97.measurable_roundLaw`).
-/

/-- **The rounding kernel is a kernel**: `p ↦ roundLaw p` is measurable for the
Giry σ-algebra on measures.  `ℤⁿ` is countable and discrete, so every measurable
set is a countable disjoint union of singletons and the mass of each singleton,
`∏ᵢ tent(pᵢ − zᵢ)`, is continuous in `p`. -/
theorem measurable_roundLaw (n : ℕ) :
    Measurable (roundLaw : (Fin n → ℝ) → Measure (Fin n → ℤ)) := by
  refine Measure.measurable_of_measurable_coe _ fun s _ => ?_
  have hcov : ∀ p : Fin n → ℝ, roundLaw p s = ∑' z : ↥s, roundLaw p {(z : Fin n → ℤ)} := by
    intro p
    conv_lhs => rw [← Set.biUnion_of_singleton s]
    exact measure_biUnion s.to_countable
      (fun a _ b _ hab => Set.disjoint_singleton.2 hab) fun b _ => measurableSet_singleton b
  simp only [hcov]
  refine Measurable.tsum fun z => ?_
  simp only [roundLaw_singleton]
  have hcont : Continuous fun p : Fin n → ℝ => ∏ i, tent (p i - ((z : Fin n → ℤ) i : ℝ)) :=
    continuous_finsetProd _ fun i _ =>
      continuous_tent.comp ((continuous_apply i).sub continuous_const)
  exact hcont.measurable.ennreal_ofReal

/-- The coordinate forgetting map `ℝⁿ → (Fin n → ℝ)` is measurable: each
coordinate of `EuclideanSpace` is continuous. -/
theorem measurable_ofLp (n : ℕ) :
    Measurable fun p : EuclideanSpace ℝ (Fin n) => (WithLp.ofLp p : Fin n → ℝ) :=
  measurable_pi_lambda _ fun i => (PiLp.continuous_apply _ _ i).measurable

/-- **The law of the rounded draw**, unconditionally: draw `p` from the density
`f` on `S = P'`, then round.  This is the measure whose mass on `P ∩ ℤⁿ` the whole
of Lemma 1 is about, and `Arlib.KV97.toReal_roundedLaw_eq_acceptance` identifies
that mass with `Arlib.KV97.acceptance` at Theorem 2's weight. -/
noncomputable def roundedLaw (S : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Measure (Fin n → ℤ) :=
  ((volume.restrict S).withDensity fun p => ENNReal.ofReal (f p)).bind
    fun p => roundLaw (WithLp.ofLp p)

/-- `Arlib.KV97.roundedLaw` evaluated on a set: the law of the rounded draw is the
`f`-average of the conditional laws.  This is `MeasureTheory.Measure.bind_apply`,
i.e. the definition of a mixture, with the two measurability side-conditions
discharged. -/
theorem roundedLaw_apply {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (A : Set (Fin n → ℤ)) :
    roundedLaw S f A = ∫⁻ p in S, ENNReal.ofReal (f p) * roundLaw (WithLp.ofLp p) A := by
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have hmeas : Measurable fun p : EuclideanSpace ℝ (Fin n) => roundLaw (WithLp.ofLp p) :=
    (measurable_roundLaw n).comp (measurable_ofLp n)
  have hker : Measurable fun p : EuclideanSpace ℝ (Fin n) => roundLaw (WithLp.ofLp p) A :=
    (Measure.measurable_coe hA).comp hmeas
  have hdens : Measurable fun p : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (f p) :=
    ENNReal.measurable_ofReal.comp hf
  rw [roundedLaw, Measure.bind_apply hA hmeas.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hdens hker]
  rfl

/-- **The chain from Theorem 2 to Lemma 1, closed against an actual measure.**

    Pr[rnd p ∈ P]  =  acceptance pt (fun x => ∫ p in S, f p * prodTent x p),

where the left-hand side is the mass the *unconditional* law of the rounded draw
(`Arlib.KV97.roundedLaw`) gives to the event "the rounded point lies in `P`", and
the right-hand side is `Arlib.KV97.acceptance` at literally the weight
`Arlib.KV97.theorem2_lower` bounds.  Together with
`Arlib.KV97.acceptance_ge_one_eighth` this says the *probability* — not a sum of
numbers — is at least `1/8`.

The hypotheses are the ones a density and an enumeration really have: `f`
measurable and nonnegative, each `f · prodTent (pt i) ·` integrable on `S` (which
`Arlib.KV97.theorem2_lower` already requires), and `lat` an injective, exhaustive
enumeration of `P ∩ ℤⁿ` (`Arlib.KV97.enum_iff_of_inter_intLattice` supplies
`henum` from `P ∩ intLattice n = Set.range (latEmb ∘ lat)`).  Note that `f` is
*not* required to integrate to `1`: the identity is an identity of masses, and a
caller who wants `Pr` to be a probability supplies that separately. -/
theorem toReal_roundedLaw_eq_acceptance {P S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {lat : ι → (Fin n → ℤ)}
    (hlat : Function.Injective lat)
    (henum : ∀ z, latEmb n z ∈ P ↔ ∃ i, lat i = z)
    (hf : Measurable f) (hf0 : ∀ p, 0 ≤ f p)
    (hint : ∀ i, IntegrableOn (fun p => f p * prodTent (latEmb n (lat i)) p) S) :
    (roundedLaw S f {z | latEmb n z ∈ P}).toReal
      = acceptance (fun i => latEmb n (lat i)) (fun x => ∫ p in S, f p * prodTent x p) := by
  have hacc0 : ∀ p : EuclideanSpace ℝ (Fin n),
      0 ≤ acceptance (fun i => latEmb n (lat i)) (fun x => prodTent x p) :=
    fun _ => Finset.sum_nonneg fun _ _ => prodTent_nonneg _ _
  have hcond : ∀ p : EuclideanSpace ℝ (Fin n),
      roundLaw (WithLp.ofLp p) {z | latEmb n z ∈ P}
        = ENNReal.ofReal
            (acceptance (fun i => latEmb n (lat i)) (fun x => prodTent x p)) := by
    intro p
    rw [← toReal_roundLaw_eq_acceptance hlat henum p,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hintacc : IntegrableOn
      (fun p => f p * acceptance (fun i => latEmb n (lat i)) (fun x => prodTent x p)) S := by
    have hEq :
        (fun p => f p * acceptance (fun i => latEmb n (lat i)) (fun x => prodTent x p))
          = fun p => ∑ i, f p * prodTent (latEmb n (lat i)) p := by
      funext p; rw [acceptance_def, Finset.mul_sum]
    rw [hEq]
    exact integrable_finsetSum _ fun i _ => hint i
  have hmass : roundedLaw S f {z | latEmb n z ∈ P}
      = ENNReal.ofReal (∫ p in S, f p *
          acceptance (fun i => latEmb n (lat i)) (fun x => prodTent x p)) := by
    rw [roundedLaw_apply hf]
    simp only [hcond, ← ENNReal.ofReal_mul (hf0 _)]
    exact (ofReal_integral_eq_lintegral_ofReal hintacc
      (Filter.Eventually.of_forall fun p => mul_nonneg (hf0 p) (hacc0 p))).symm
  rw [hmass, ENNReal.toReal_ofReal
      (integral_nonneg fun p => mul_nonneg (hf0 p) (hacc0 p)),
    acceptance_setIntegral_eq_setIntegral_acceptance (fun i => latEmb n (lat i)) hint]

end RoundingKernel

/-- **Step 2: summing Theorem 2's lower bound over the `N` lattice points.**

If every weight is at least `(1−ε)(1−E)/V` — which is exactly the conclusion of
`Arlib.KV97.theorem2_lower` at `V = Vol(P')` — then the acceptance mass is at
least `N(1−ε)(1−E)/V`, where `N = Fintype.card ι`.  This is the paper's
`Pr[rnd p ∈ P] ≥ (1−θ)N/Vol(P')`.

`Arlib.Rejection.sum_bounds` proves the same inequality but bundled with an upper
bound `w i ≤ 1/V`, which Theorem 2 does not supply (it gives `(1+ε)/V`), so it is
not usable here; only the lower half is needed and it is three lines.

No positivity hypothesis on `V` is required: the statement is a sum of `N` copies
of one real number, and if `V ≤ 0` (or `V = 0`, where `x / 0 = 0`) both sides
degrade together.  The callers below supply `V = Vol(P') > 0`. -/
theorem acceptance_ge (pt : ι → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) {V ε E : ℝ}
    (hlow : ∀ i, (1 - ε) * (1 - E) / V ≤ w (pt i)) :
    (Fintype.card ι : ℝ) * ((1 - ε) * (1 - E)) / V ≤ acceptance pt w := by
  rw [acceptance_def]
  calc (Fintype.card ι : ℝ) * ((1 - ε) * (1 - E)) / V
      = ∑ _i : ι, (1 - ε) * (1 - E) / V := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ ∑ i, w (pt i) := Finset.sum_le_sum fun i _ => hlow i

/-- **Step 3: eliminating `Vol(P')`, which is the point of the lemma.**

    acceptance  ≥  (1−ε)(1−E) / ((1+η) (1 + κ/γ)ⁿ).

The volume of the inflated polytope is removed by two inputs:

* `Arlib.KV97.inv_pow_le_toReal_volume_ratio`, i.e. `Vol(P)/Vol(P') ≥ (1+κ/γ)^{-n}`,
  which needs the inscribed ball (`hball`, `0 < γ`), `0 ≤ c`, and finiteness of
  `Vol(P)` (`hfin` — an unbounded polytope really does have infinite volume);
* `hlattice_nonconv`, `Vol(P) ≤ (1+η)N`.

**`hlattice_nonconv` is not proved in `Arlib`.**  It is `lem:nonconv`/`lem:lattice`
of the paper, formalised in the `Ttc` project (`Ttc/Nonconv/Assembled.lean`,
`Ttc/Lattice/Assembled.lean`), which this library may not import.  It is carried
as an explicit hypothesis and named accordingly.

`hlow` is Theorem 2's lower half at `V = Vol(P')`; see the module docstring for
why `Theorem2.lean` is not imported. -/
theorem acceptance_ge_const {F : Type*} {A : F → EuclideanSpace ℝ (Fin n)} {b : F → ℝ}
    {cen : EuclideanSpace ℝ (Fin n)} {γ c r ε E η : ℝ}
    (pt : ι → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤)
    (hη : 0 ≤ η) (hε : ε ≤ 1) (hE : E ≤ 1)
    (hlow : ∀ i, (1 - ε) * (1 - E) / (volume (inflated A b c r)).toReal ≤ w (pt i))
    (hlattice_nonconv :
      (volume (Arlib.Polytope.body A b)).toReal ≤ (1 + η) * (Fintype.card ι : ℝ)) :
    (1 - ε) * (1 - E) / ((1 + η) * (1 + kappaOf c r / γ) ^ n) ≤ acceptance pt w := by
  set V := (volume (inflated A b c r)).toReal with hVdef
  set W := (volume (Arlib.Polytope.body A b)).toReal with hWdef
  set K := (1 + kappaOf c r / γ) ^ n with hKdef
  have hV : 0 < V := toReal_volume_inflated_pos hγ hc hball hfin
  have hkg : (0:ℝ) ≤ kappaOf c r / γ := div_nonneg (kappaOf_nonneg hc) hγ.le
  have hK : 0 < K := pow_pos (by linarith) n
  have hη1 : (0:ℝ) < 1 + η := by linarith
  have hAnn : (0:ℝ) ≤ (1 - ε) * (1 - E) := mul_nonneg (by linarith) (by linarith)
  have hratio : K⁻¹ ≤ W / V := inv_pow_le_toReal_volume_ratio hγ hc hball hfin
  rw [le_div_iff₀ hV] at hratio
  have hVKW : V ≤ K * W := by
    calc V = K * (K⁻¹ * V) := by field_simp
      _ ≤ K * W := mul_le_mul_of_nonneg_left hratio hK.le
  have hVN : V ≤ K * ((1 + η) * (Fintype.card ι : ℝ)) :=
    hVKW.trans (mul_le_mul_of_nonneg_left hlattice_nonconv hK.le)
  have key : 1 / ((1 + η) * K) ≤ (Fintype.card ι : ℝ) / V := by
    rw [div_le_div_iff₀ (by positivity) hV]
    nlinarith [hVN]
  calc (1 - ε) * (1 - E) / ((1 + η) * K)
      = ((1 - ε) * (1 - E)) * (1 / ((1 + η) * K)) := by ring
    _ ≤ ((1 - ε) * (1 - E)) * ((Fintype.card ι : ℝ) / V) :=
        mul_le_mul_of_nonneg_left key hAnn
    _ = (Fintype.card ι : ℝ) * ((1 - ε) * (1 - E)) / V := by ring
    _ ≤ acceptance pt w := acceptance_ge pt w hlow

/-- **Step 4: `(1 + t)ᵐ ≤ e` whenever `t ≤ 1/m`.**

`1 + t ≤ e^t` (`Real.add_one_le_exp`) raised to the `m`-th power gives
`(1+t)ᵐ ≤ e^{mt}`, and `mt ≤ 1`.  Stated with the hypothesis in the paper's shape
`t ≤ 1/m`; at `m = 0` Lean's `1/0 = 0` forces `t = 0` and the claim degenerates to
`1 ≤ e`, which is still true, so no `m ≠ 0` side condition is needed. -/
theorem one_add_div_pow_le_exp {t : ℝ} {m : ℕ} (ht : 0 ≤ t) (htn : t ≤ 1 / (m : ℝ)) :
    (1 + t) ^ m ≤ Real.exp 1 := by
  have hexp1 : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm, pow_zero]; exact hexp1
  · have hm' : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmt : (m : ℝ) * t ≤ 1 := by
      rw [le_div_iff₀ hm'] at htn; linarith
    have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    calc (1 + t) ^ m ≤ (Real.exp t) ^ m := by gcongr
      _ = Real.exp ((m : ℝ) * t) := (Real.exp_nat_mul t m).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hmt

/-- **The bound with the dimension eliminated.**

    acceptance  ≥  (1−ε)(1−E) / ((1+η)·e)

as soon as `κ/γ ≤ 1/n` — the `κ/γ = O(1/n)` regime the paper says `GetPrecision`
arranges.  This is `Arlib.KV97.acceptance_ge_const` with
`Arlib.KV97.one_add_div_pow_le_exp` applied to the denominator; `e` is now the
only trace left of the dimension. -/
theorem acceptance_ge_exp {F : Type*} {A : F → EuclideanSpace ℝ (Fin n)} {b : F → ℝ}
    {cen : EuclideanSpace ℝ (Fin n)} {γ c r ε E η : ℝ}
    (pt : ι → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤)
    (hη : 0 ≤ η) (hε : ε ≤ 1) (hE : E ≤ 1)
    (hlow : ∀ i, (1 - ε) * (1 - E) / (volume (inflated A b c r)).toReal ≤ w (pt i))
    (hlattice_nonconv :
      (volume (Arlib.Polytope.body A b)).toReal ≤ (1 + η) * (Fintype.card ι : ℝ))
    (hthin : kappaOf c r / γ ≤ 1 / (n : ℝ)) :
    (1 - ε) * (1 - E) / ((1 + η) * Real.exp 1) ≤ acceptance pt w := by
  have hkg : (0:ℝ) ≤ kappaOf c r / γ := div_nonneg (kappaOf_nonneg hc) hγ.le
  have hKle : (1 + kappaOf c r / γ) ^ n ≤ Real.exp 1 := one_add_div_pow_le_exp hkg hthin
  have hKpos : (0:ℝ) < (1 + kappaOf c r / γ) ^ n := pow_pos (by linarith) n
  have hη1 : (0:ℝ) < 1 + η := by linarith
  have hAnn : (0:ℝ) ≤ (1 - ε) * (1 - E) := mul_nonneg (by linarith) (by linarith)
  refine le_trans ?_
    (acceptance_ge_const pt w hγ hc hball hfin hη hε hE hlow hlattice_nonconv)
  gcongr

/-- **`1/8 ≤ 9/(20e)`.**  `9/(20e) ≈ 0.165546` and `1/8 = 0.125`; the gap is what
lets the sharp constant of this development imply the paper's round one.  Proved
from `Real.exp_one_lt_d9`. -/
theorem one_eighth_le_nine_div_twenty_exp : (1:ℝ) / 8 ≤ 9 / (20 * Real.exp 1) := by
  have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [h]

/-- **The headline, with the constant this argument actually gives.**

With all three error budgets at most `1/4` and `κ/γ ≤ 1/n`,

    Pr[rnd p ∈ P]  ≥  (3/4)(3/4) / ((5/4)·e)  =  9/(20e)  ≈  0.165546.

So the rejection loop accepts with probability bounded below by an absolute
constant.  **This is a one-round probability, not a bound on the number of draws.**
The paper reads off `E[draws] = O(1)` from it; that step is *not* formalised here
and would need a round count defined as a random variable plus the mean of a
geometric law — which Mathlib does not provide (`Probability/Distributions/
Geometric.lean` has `geometricMeasure` and its integral, but no mean lemma).  No
round count, random variable or expectation exists anywhere in this development.
The paper's `1/8` follows
(`Arlib.KV97.acceptance_ge_one_eighth`) but is not sharp — see the module
docstring.  Nonnegativity of `ε` and `E` is not needed: making them negative only
enlarges `(1−ε)(1−E)`. -/
theorem acceptance_ge_nine_div_twenty_exp {F : Type*}
    {A : F → EuclideanSpace ℝ (Fin n)} {b : F → ℝ}
    {cen : EuclideanSpace ℝ (Fin n)} {γ c r ε E η : ℝ}
    (pt : ι → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4) (hε : ε ≤ 1 / 4) (hE : E ≤ 1 / 4)
    (hlow : ∀ i, (1 - ε) * (1 - E) / (volume (inflated A b c r)).toReal ≤ w (pt i))
    (hlattice_nonconv :
      (volume (Arlib.Polytope.body A b)).toReal ≤ (1 + η) * (Fintype.card ι : ℝ))
    (hthin : kappaOf c r / γ ≤ 1 / (n : ℝ)) :
    9 / (20 * Real.exp 1) ≤ acceptance pt w := by
  have hexp : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : (3:ℝ) / 4 ≤ 1 - ε := by linarith
  have h2 : (3:ℝ) / 4 ≤ 1 - E := by linarith
  have hnum : (9:ℝ) / 16 ≤ (1 - ε) * (1 - E) := by nlinarith
  have hrw : (9:ℝ) / (20 * Real.exp 1) = (9 / 16) / ((5 / 4) * Real.exp 1) := by
    field_simp; ring
  refine le_trans ?_
    (acceptance_ge_exp pt w hγ hc hball hfin hη0 (by linarith) (by linarith) hlow
      hlattice_nonconv hthin)
  rw [hrw]
  gcongr
  all_goals linarith

/-- **The headline in the paper's numbers**: under the same hypotheses the
acceptance probability is at least `1/8`.  This is `sections/proof-appendix.tex`'s
"bounded below by a constant", cashed out.  The constant actually proved is
`9/(20e) ≈ 0.165546` (`Arlib.KV97.acceptance_ge_nine_div_twenty_exp`); `1/8` is the
weaker round number below it. -/
theorem acceptance_ge_one_eighth {F : Type*}
    {A : F → EuclideanSpace ℝ (Fin n)} {b : F → ℝ}
    {cen : EuclideanSpace ℝ (Fin n)} {γ c r ε E η : ℝ}
    (pt : ι → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4) (hε : ε ≤ 1 / 4) (hE : E ≤ 1 / 4)
    (hlow : ∀ i, (1 - ε) * (1 - E) / (volume (inflated A b c r)).toReal ≤ w (pt i))
    (hlattice_nonconv :
      (volume (Arlib.Polytope.body A b)).toReal ≤ (1 + η) * (Fintype.card ι : ℝ))
    (hthin : kappaOf c r / γ ≤ 1 / (n : ℝ)) :
    (1:ℝ) / 8 ≤ acceptance pt w :=
  one_eighth_le_nine_div_twenty_exp.trans
    (acceptance_ge_nine_div_twenty_exp pt w hγ hc hball hfin hη0 hη hε hE hlow
      hlattice_nonconv hthin)

/-! ## Non-vacuity -/

/-- **`N = 0` is excluded by the hypotheses, not assumed away.**

An empty index would make the acceptance mass an empty sum and every bound above
vacuous.  It cannot happen: `Vol(P) > 0` (the inscribed ball) together with
`Vol(P) ≤ (1+η)N` forces `0 < Fintype.card ι`.  No sign hypothesis on `η` is
needed — `N = 0` kills the right-hand side whatever `η` is. -/
theorem card_pos_of_lattice_bound {F : Type*} {A : F → EuclideanSpace ℝ (Fin n)}
    {b : F → ℝ} {cen : EuclideanSpace ℝ (Fin n)} {γ η : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤)
    (hlattice_nonconv :
      (volume (Arlib.Polytope.body A b)).toReal ≤ (1 + η) * (Fintype.card ι : ℝ)) :
    0 < Fintype.card ι := by
  have hW : 0 < (volume (Arlib.Polytope.body A b)).toReal :=
    toReal_volume_body_pos hγ hball hfin
  have hprod : (0:ℝ) < (1 + η) * (Fintype.card ι : ℝ) :=
    lt_of_lt_of_le hW hlattice_nonconv
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · rw [h] at hprod; norm_num at hprod
  · exact h

/-- **The bound is a genuinely positive number, not `≥ 0`.**

With `ε < 1` and `E < 1` — in particular the loss `E` must be a real loss, not a
vacuous `E ≥ 1` — the right-hand side of `Arlib.KV97.acceptance_ge_const` is
strictly positive, so the acceptance probability is too and the rejection loop
terminates with probability `1`. -/
theorem acceptance_pos {F : Type*} {A : F → EuclideanSpace ℝ (Fin n)} {b : F → ℝ}
    {cen : EuclideanSpace ℝ (Fin n)} {γ c r ε E η : ℝ}
    (pt : ι → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤)
    (hη : 0 ≤ η) (hε : ε < 1) (hE : E < 1)
    (hlow : ∀ i, (1 - ε) * (1 - E) / (volume (inflated A b c r)).toReal ≤ w (pt i))
    (hlattice_nonconv :
      (volume (Arlib.Polytope.body A b)).toReal ≤ (1 + η) * (Fintype.card ι : ℝ)) :
    0 < acceptance pt w := by
  have hkg : (0:ℝ) ≤ kappaOf c r / γ := div_nonneg (kappaOf_nonneg hc) hγ.le
  have hKpos : (0:ℝ) < (1 + kappaOf c r / γ) ^ n := pow_pos (by linarith) n
  have hpos : 0 < (1 - ε) * (1 - E) / ((1 + η) * (1 + kappaOf c r / γ) ^ n) :=
    div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  exact hpos.trans_le
    (acceptance_ge_const pt w hγ hc hball hfin hη hε.le hE.le hlow hlattice_nonconv)

/-- **The exact case: `ε = E = η = 0` gives `acceptance ≥ e⁻¹`.**

A perfectly uniform sampler with no escape mass and an exact lattice-point count
accepts with probability at least `1/e ≈ 0.367879`, provided `κ/γ ≤ 1/n`.  This is
the non-vacuity statement of `CLAUDE.md` §11 for the bound: with every error
coefficient zeroed the conclusion is a positive number
(`Arlib.KV97.exp_neg_one_pos`), not `≥ 0`. -/
theorem acceptance_ge_exp_neg_one {F : Type*} {A : F → EuclideanSpace ℝ (Fin n)}
    {b : F → ℝ} {cen : EuclideanSpace ℝ (Fin n)} {γ c r : ℝ}
    (pt : ι → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤)
    (hlow : ∀ i, 1 / (volume (inflated A b c r)).toReal ≤ w (pt i))
    (hlattice_nonconv :
      (volume (Arlib.Polytope.body A b)).toReal ≤ (Fintype.card ι : ℝ))
    (hthin : kappaOf c r / γ ≤ 1 / (n : ℝ)) :
    Real.exp (-1) ≤ acceptance pt w := by
  have h := acceptance_ge_exp (ε := 0) (E := 0) (η := 0) pt w hγ hc hball hfin
    le_rfl zero_le_one zero_le_one (by simpa using hlow)
    (by simpa using hlattice_nonconv) hthin
  simpa [Real.exp_neg] using h

/-! ## A concrete witness -/

section Witness

open scoped InnerProductSpace

/-- **The witness polytope's facet normals**: `±eᵢ` for each coordinate `i`, so
that `Arlib.Polytope.body (cubeA d) (cubeb d)` is the cube `{x : |xᵢ| ≤ 1 ∀ i}`. -/
noncomputable def cubeA (d : ℕ) : Fin d × Bool → EuclideanSpace ℝ (Fin d) :=
  fun p => if p.2 then EuclideanSpace.single p.1 (1:ℝ)
    else -EuclideanSpace.single p.1 (1:ℝ)

/-- The witness polytope's offsets, all `1`. -/
def cubeb (d : ℕ) : Fin d × Bool → ℝ := fun _ => 1

/-- Each facet normal of the witness cube is a unit vector. -/
theorem norm_cubeA (d : ℕ) (p : Fin d × Bool) : ‖cubeA d p‖ = 1 := by
  rcases p with ⟨i, s⟩
  cases s <;> simp [cubeA, PiLp.norm_single]

/-- **The unit ball is inscribed in the witness cube**, which discharges the
`hball` hypothesis at `γ = 1`, `cen = 0`.  Only `‖cubeA d j‖ = 1` and
Cauchy–Schwarz are used. -/
theorem ball_subset_cube (d : ℕ) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ Arlib.Polytope.body (cubeA d) (cubeb d) := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  intro j
  calc ⟪cubeA d j, x⟫_ℝ ≤ ‖cubeA d j‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ 1 := by rw [norm_cubeA]; simpa [cubeb] using hx.le

/-- **The witness cube is bounded**, sitting inside the closed ball of radius
`√d`: each `|xᵢ| ≤ 1`, so `‖x‖² = ∑ xᵢ² ≤ d`. -/
theorem cube_subset_closedBall (d : ℕ) :
    Arlib.Polytope.body (cubeA d) (cubeb d)
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt d) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hco : ∀ i : Fin d, |x i| ≤ 1 := by
    intro i
    have h1 : ⟪cubeA d (i, true), x⟫_ℝ ≤ cubeb d (i, true) := hx (i, true)
    have h2 : ⟪cubeA d (i, false), x⟫_ℝ ≤ cubeb d (i, false) := hx (i, false)
    simp [cubeA, cubeb, EuclideanSpace.inner_single_left] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc (∑ i, ‖x i‖ ^ 2) ≤ ∑ _i : Fin d, (1:ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := hco i
        rw [Real.norm_eq_abs]
        nlinarith [abs_nonneg (x i)]
    _ = (d : ℝ) := by simp

/-- **The witness cube has finite volume**, which discharges `hfin`.  Boundedness
is what does it: closed balls in a finite-dimensional space have finite measure. -/
theorem volume_cube_ne_top (d : ℕ) :
    volume (Arlib.Polytope.body (cubeA d) (cubeb d)) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono (cube_subset_closedBall d))

/-- At `c = 0` and `r = 1` the facet displacement vanishes, `κ = 0 + √(2 log 1) = 0`,
so the witness may take `κ/γ = 0 ≤ 1/d` in every dimension. -/
theorem kappaOf_zero_one : kappaOf 0 1 = 0 := by simp [kappaOf]

/-- The witness lattice-point count, `N = ⌈Vol(P)⌉`, chosen so that
`Vol(P) ≤ (1+0)·N` holds by `Nat.le_ceil`. -/
noncomputable def cubeCard (d : ℕ) : ℕ :=
  ⌈(volume (Arlib.Polytope.body (cubeA d) (cubeb d))).toReal⌉₊

/-- **Non-vacuity witness (`CLAUDE.md` §11).**

Every hypothesis of `Arlib.KV97.acceptance_ge_exp_neg_one` is satisfiable, in
every dimension `d`: take `P` to be the cube `{x : |xᵢ| ≤ 1}` (bounded, with the
unit ball inscribed at `γ = 1`), `c = 0` and `r = 1` (so `κ = 0 ≤ 1/d`), the exact
weights `w ≡ 1/Vol(P')`, and `N = ⌈Vol(P)⌉` lattice points.  The conclusion is then
`acceptance ≥ e⁻¹ > 0`, so neither the hypothesis bundle nor the bound is empty.

The witness's `pt` is the constant map; injectivity is not a hypothesis of any
bound in this file (only of `Arlib.KV97.acceptance_eq_sum_image`). -/
theorem exp_neg_one_le_acceptance_cube (d : ℕ) :
    Real.exp (-1) ≤
      acceptance (n := d) (ι := Fin (cubeCard d)) (fun _ => 0)
        (fun _ => 1 / (volume (inflated (cubeA d) (cubeb d) 0 1)).toReal) := by
  refine acceptance_ge_exp_neg_one (cen := 0) (γ := 1) _ _ one_pos le_rfl
    (ball_subset_cube d) (volume_cube_ne_top d) (fun _ => le_rfl) ?_ ?_
  · rw [Fintype.card_fin]
    exact Nat.le_ceil _
  · rw [kappaOf_zero_one, zero_div]
    positivity

/-- `e⁻¹ > 0`: the witness bound is a genuine positive number, so
`Arlib.KV97.exp_neg_one_le_acceptance_cube` is not the trivial `≥ 0`. -/
theorem exp_neg_one_pos : (0:ℝ) < Real.exp (-1) := Real.exp_pos _

end Witness

/-! ## The headline, about an actual measure

`Arlib.KV97.acceptance_ge_one_eighth` bounds a sum of numbers.  Composing it with
the bridge of step 3 bounds a **mass of the law of the rounded draw**, which is
what Lemma 1 of Kannan–Vempala actually claims.
-/

section Headline

open Arlib.Lattice Arlib.Lattice.Rounding

/-- **Lemma 1, stated about the object it is about.**

    (roundedLaw P' f) {z : ℤⁿ | z ∈ P}  ≥  1/8.

The left-hand side is the mass the law of the rounded draw
(`Arlib.KV97.roundedLaw`) gives to the acceptance event, not a sum of weights.
The hypotheses are those of `Arlib.KV97.acceptance_ge_one_eighth` — with `w`
instantiated at Theorem 2's weight, so `hlow` is discharged verbatim by
`Arlib.KV97.theorem2_lower` — plus the four the bridge needs: `lat` injective and
exhaustive (`Arlib.KV97.enum_iff_of_inter_intLattice` builds `henum` from
`P ∩ ℤⁿ = range pt`), and `f` measurable and nonnegative.

As everywhere in this file, `hlattice_nonconv` is `lem:nonconv`/`lem:lattice`,
proved in `Ttc`, not here. -/
theorem toReal_roundedLaw_ge_one_eighth {F : Type*}
    {A : F → EuclideanSpace ℝ (Fin n)} {b : F → ℝ}
    {cen : EuclideanSpace ℝ (Fin n)} {γ c r ε E η : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {lat : ι → (Fin n → ℤ)}
    {P : Set (EuclideanSpace ℝ (Fin n))}
    (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4) (hε : ε ≤ 1 / 4) (hE : E ≤ 1 / 4)
    (hlow : ∀ i, (1 - ε) * (1 - E) / (volume (inflated A b c r)).toReal
      ≤ ∫ p in inflated A b c r, f p * prodTent (latEmb n (lat i)) p)
    (hlattice_nonconv :
      (volume (Arlib.Polytope.body A b)).toReal ≤ (1 + η) * (Fintype.card ι : ℝ))
    (hthin : kappaOf c r / γ ≤ 1 / (n : ℝ))
    (hlat : Function.Injective lat)
    (henum : ∀ z, latEmb n z ∈ P ↔ ∃ i, lat i = z)
    (hf : Measurable f) (hf0 : ∀ p, 0 ≤ f p)
    (hint : ∀ i, IntegrableOn (fun p => f p * prodTent (latEmb n (lat i)) p)
      (inflated A b c r)) :
    (1 : ℝ) / 8 ≤ (roundedLaw (inflated A b c r) f {z | latEmb n z ∈ P}).toReal := by
  rw [toReal_roundedLaw_eq_acceptance hlat henum hf hf0 hint]
  exact acceptance_ge_one_eighth _ _ hγ hc hball hfin hη0 hη hε hE hlow
    hlattice_nonconv hthin

end Headline

end Arlib.KV97



