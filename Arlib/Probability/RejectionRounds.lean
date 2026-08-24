/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Arlib.Lattice.KV97.Lemma1
import Arlib.Probability.Geometric
import Arlib.Probability.RunPlumbing

/-!
# The number of rounds of a rejection loop, as a random variable

A rejection sampler draws a candidate, tests it, and **repeats until the test
passes**.  This module builds the number of rounds such a loop runs as a genuine
random variable on an explicit probability space, and computes its mean exactly:

    E[rounds]  =  1 / Pr[accept].

## What is constructed, and what is merely assumed

The i.i.d. structure of the rounds is **constructed, not posited**.  The sample
space is the trajectory space `ℕ → E` of one candidate per round, carrying
`MeasureTheory.Measure.infinitePi (fun _ => ν)` for the one-round law `ν`
(`Arlib.Probability.roundsMeasure`).  That the rounds are identically distributed
(`Arlib.Probability.measurePreserving_draw`) and independent
(`Arlib.Probability.iIndepFun_draw`) are then *theorems* about that measure, not
fields of a structure.  The only hypotheses in the abstract development are
`[MeasurableSpace E]`, `IsProbabilityMeasure ν`, measurability of the acceptance
event `A`, and — for the final bounds — a lower bound on `ν A`.  (The `Arlib.KV97`
instantiation at the end carries Lemma 1's own hypothesis bundle, plus `hnorm`,
that the sampler's density integrates to `1`; without `hnorm`,
`Arlib.KV97.roundedLaw` is not known to be a probability measure and there is no
process to build.  That is the only assumption this file adds to Lemma 1's.)

## Main definitions

* `Arlib.Probability.roundsMeasure ν : Measure (ℕ → E)` — the law of the
  trajectory of candidates, `Measure.infinitePi fun _ : ℕ => ν`.
* `Arlib.Probability.roundCount A ω : ℝ≥0∞` — one more than the first index at
  which `ω` is accepted, and `⊤` on the (null, once `ν A > 0`) event that no
  candidate is ever accepted.  It is an `⨅` over the accepted indices, i.e. the
  `sInf` the task description asks for; `Arlib.Probability.roundCount_eq_find`
  identifies it with `Nat.find + 1` whenever some candidate is accepted.  The
  `⊤` value is deliberate: a loop that never terminates costs infinitely many
  rounds, and pinning a finite junk value there would silently *undercount* and
  make the upper bounds below cheaper than they should be.
* `Arlib.Probability.roundCountNat A ω : ℕ` — the same count as a `ℕ`-valued
  random variable, for the Bochner integral.  Its value on a never-accepting
  trajectory is the junk `1`; that junk *undercounts*, so it is fenced off rather
  than waved away — see the "`ℕ`-valued round count" section docstring.
* `Arlib.Probability.survives A n` — the event that rounds `0, …, n-1` were all
  rejected; `Arlib.Probability.neverAccepts A` — the event that no round ever
  accepts.

## Main results

* `Arlib.Probability.roundCount_eq_tsum` — the tail identity
  `roundCount A ω = ∑' n, 1[ω survives n rounds]`, which is what makes both the
  measurability and the mean computation routine.
* `Arlib.Probability.measurable_roundCount`, `measurable_roundCountNat` — both
  counts are measurable, for `A` measurable.
* `Arlib.Probability.roundsMeasure_survives` — `Pr[survive n rounds] = ν(Aᶜ)ⁿ`.
  This is the i.i.d. content, and it is `MeasureTheory.Measure.infinitePi_pi`
  applied to the cylinder `Set.pi (range n) (fun _ => Aᶜ)`.
* `Arlib.Probability.lintegral_roundCount` — **the mean, exactly**:
  `∫⁻ ω, roundCount A ω = (ν A)⁻¹`.
* `Arlib.Probability.lintegral_roundCount_le` — the bound
  `E[rounds] ≤ p⁻¹` from `p ≤ ν A`.
* `Arlib.Probability.measure_neverAccepts` — **almost sure termination** when
  `0 < ν A`; with `coe_roundCountNat_ae_eq` this is what makes the `ℕ`-valued
  count's junk value harmless.
* `Arlib.Probability.integral_roundCountNat_le` — `E[rounds] ≤ 1/p` as a genuine
  **Bochner integral** of a real-valued random variable, with
  `integrable_roundCountNat` for finiteness.
* `Arlib.Probability.lintegral_roundCount_le_twentyExpDivNine`,
  `integral_roundCountNat_le_twentyExpDivNine`, `lintegral_roundCount_le_eight`
  and `integral_roundCountNat_le_eight` — the instantiations at the constants of
  `Arlib.KV97`: `E[rounds] ≤ 20e/9 ≈ 6.0405` (`< 6.041`) from acceptance
  `≥ 9/(20e)`, and `E[rounds] ≤ 8` from acceptance `≥ 1/8`.
* `Arlib.Probability.integral_roundCountNat_kv97` and
  `lintegral_roundCount_kv97` — the same over the **real** Kannan–Vempala
  objects: `ν` is `Arlib.KV97.roundedLaw P' f`, `A` is `{z : ℤⁿ | z ∈ P}`.
* `Arlib.Probability.coin_lintegral_roundCount` — non-vacuity: for a fair coin
  the space is genuinely random (`coin_survives`: `Pr[survive n] = 2⁻ⁿ`) and
  `E[rounds] = 2`, neither `0` nor `⊤`.

## Relation to `Arlib.Probability.RunPlumbing` and `Arlib.Geometric`

`RunPlumbing` is the repo's other i.i.d.-over-`Measure.infinitePi` development.
Its **probability spaces did not fit** and were not reused: both are doubly
indexed (`Fin r → Fin m → E` and `ℕ → ℕ → E`, a run/phase grid) and its API is
about scores, products over phases, and medians.  A rejection loop needs a single
`ℕ`-indexed trajectory and cylinder masses on it, and computing those masses
through the nested `infinitePi` of `natRunMeasure` is strictly harder than
through the flat one.  `Arlib.Probability.roundsMeasure` therefore goes straight
to the same Mathlib primitive `MeasureTheory.Measure.infinitePi` that
`RunPlumbing` uses, at the flat index — a one-line definition, duplicating
nothing.  Its **fair-coin witness `Arlib.Probability.coin` is reused**, in the
non-vacuity section.

`Arlib.Geometric` **is** consumed, for the geometric-mean step: this file proves
the tail bound `Pr[N > n] ≤ ν(Aᶜ)ⁿ` from the product structure, and
`Arlib.Geometric.lintegral_natCast_le_inv_of_geometric_tail`,
`Arlib.Geometric.integrable_natCast_of_geometric_tail` and
`Arlib.Geometric.integral_natCast_le_inv` turn it into `E[N] ≤ 1/p`.  (The
`ℝ≥0∞` route `Arlib.Probability.lintegral_roundCount` does not need it: there the
tail identity plus `ENNReal.tsum_geometric` gives the mean *exactly*, not merely
a bound.)

## Honesty: this result is an orphan

**This theorem is not on any path to the capstone, and a commit that lands it
while implying otherwise would misrepresent the development.**  Two independent,
*measured* reasons:

1. **`Arlib.KV97` Lemma 1 is off the capstone's dependency path.**  The
   transitive reachability walk recorded in `AUDIT-KV97.md` reports
   `Arlib.KV97.acceptance_ge_const` as `false` — unreached.  Everything
   downstream of it, including `acceptance_ge_nine_div_twenty_exp`,
   `acceptance_ge_one_eighth` and `toReal_roundedLaw_ge_one_eighth`, is
   therefore off the path too, and so is this file, which exists only to consume
   those constants.

2. **`Ttc` has no rejection loop to count.**  `Ttc.kv97SampD` models rejection by
   its **limit law** — conditioning on the acceptance event — rather than by an
   operational retry process.  There is consequently no loop anywhere in `Ttc`
   whose rounds `roundCount` could be counting, and no place for this bound to
   be plugged in.

What this file *is*: a true theorem about the Kannan–Vempala algorithm, namely
that its rejection loop runs `O(1)` expected rounds, with the constant `20e/9`
that `Arlib.KV97`'s acceptance bound actually gives.  What it is **not**: a step
toward pricing `Ttc`'s `cSample`.  A separate scoping run established that no
complexity result can price `cSample` in the absence of an operational cost
model, and no such model exists in this development.  Expected round count is a
statement about a probability space; `cSample` is a symbol in a cost expression;
nothing here connects them.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Arlib.Probability

section Core

variable {E : Type*} [MeasurableSpace E]

/-! ## The probability space: one candidate per round -/

/-- **The trajectory space of a rejection loop**: `ω k` is the candidate drawn in
round `k`.  Rounds are indexed from `0`, so the loop that stops at the first
accepted candidate runs `k + 1` rounds when `k` is that candidate's index. -/
abbrev RoundSpace (E : Type*) := ℕ → E

/-- **The law of the trajectory**: infinitely many i.i.d. copies of the one-round
law `ν`, as `MeasureTheory.Measure.infinitePi`.  The independence and the
identical distribution are *proved* below
(`Arlib.Probability.iIndepFun_draw`, `Arlib.Probability.measurePreserving_draw`);
neither is a field of anything. -/
noncomputable def roundsMeasure (ν : Measure E) : Measure (RoundSpace E) :=
  Measure.infinitePi fun _ : ℕ => ν

instance isProbabilityMeasure_roundsMeasure (ν : Measure E) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (roundsMeasure ν) := by
  rw [roundsMeasure]; infer_instance

/-- **The candidate drawn in round `k`.** -/
def draw (k : ℕ) (ω : RoundSpace E) : E := ω k

omit [MeasurableSpace E] in
@[simp] theorem draw_apply (k : ℕ) (ω : RoundSpace E) : draw k ω = ω k := rfl

theorem measurable_draw (k : ℕ) : Measurable (draw (E := E) k) := measurable_pi_apply k

/-- **The rounds are identically distributed**: each `Arlib.Probability.draw k`
pushes `roundsMeasure ν` forward to `ν`.  A theorem about the constructed
measure, not an assumption. -/
theorem measurePreserving_draw (ν : Measure E) [IsProbabilityMeasure ν] (k : ℕ) :
    MeasurePreserving (draw (E := E) k) (roundsMeasure ν) ν :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => ν) k

/-- **The rounds are independent.**  Again a theorem about the constructed
measure: `ProbabilityTheory.iIndepFun_infinitePi` at the identity coordinate
maps. -/
theorem iIndepFun_draw (ν : Measure E) [IsProbabilityMeasure ν] :
    iIndepFun (fun k (ω : RoundSpace E) => draw k ω) (roundsMeasure ν) :=
  iIndepFun_infinitePi (X := fun _ : ℕ => (id : E → E)) fun _ => measurable_id

/-! ## The round count -/

/-- **The set of rounds at which the trajectory is accepted.** -/
def acceptedAt (A : Set E) (ω : RoundSpace E) : Set ℕ := {k | ω k ∈ A}

/-- **The event that the first `n` rounds were all rejected.**  `survives A 0` is
everything: no round has happened yet. -/
def survives (A : Set E) (n : ℕ) : Set (RoundSpace E) := {ω | ∀ i < n, ω i ∉ A}

/-- **The number of rounds the loop runs**: one more than the first accepted
index, and `⊤` if no candidate is ever accepted.

The `⨅` over `Arlib.Probability.acceptedAt` is the `sInf`-over-the-trajectory
definition; `Arlib.Probability.roundCount_eq_find` shows it agrees with
`Nat.find + 1` on the event that acceptance happens at all. -/
noncomputable def roundCount (A : Set E) (ω : RoundSpace E) : ℝ≥0∞ :=
  ⨅ k ∈ acceptedAt A ω, ((k : ℝ≥0∞) + 1)

omit [MeasurableSpace E] in
/-- **The loop that never accepts costs `⊤` rounds.**  No finite junk value is
substituted: an upper bound on the mean must pay for non-termination. -/
theorem roundCount_eq_top_iff {A : Set E} {ω : RoundSpace E} :
    roundCount A ω = ⊤ ↔ ∀ k, ω k ∉ A := by
  constructor
  · intro h k hk
    have : roundCount A ω ≤ (k : ℝ≥0∞) + 1 :=
      iInf₂_le (f := fun k (_ : k ∈ acceptedAt A ω) => ((k : ℝ≥0∞) + 1)) k hk
    rw [h] at this
    exact absurd (top_le_iff.mp this) (by simp)
  · intro h
    have : acceptedAt A ω = (∅ : Set ℕ) := by
      ext k; simp [acceptedAt, h k]
    simp [roundCount, this]

omit [MeasurableSpace E] in
/-- **The round count is `Nat.find + 1`** whenever some candidate is accepted:
the loop stops at the *first* accepted index, and the count includes that
round. -/
theorem roundCount_eq_find {A : Set E} {ω : RoundSpace E} [DecidablePred fun k => ω k ∈ A]
    (h : ∃ k, ω k ∈ A) : roundCount A ω = (Nat.find h : ℝ≥0∞) + 1 := by
  refine le_antisymm ?_ ?_
  · exact iInf₂_le (f := fun k (_ : k ∈ acceptedAt A ω) => ((k : ℝ≥0∞) + 1))
      (Nat.find h) (Nat.find_spec h)
  · refine le_iInf₂ fun k hk => ?_
    have hle : Nat.find h ≤ k := Nat.find_le hk
    have hcast : ((Nat.find h : ℕ) : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by exact_mod_cast hle
    gcongr

omit [MeasurableSpace E] in
/-- **The tail identity.**  `roundCount = ∑ₙ 1[survive n rounds]`: the loop runs
more than `n` rounds exactly when the first `n` were all rejected, and summing
those indicators recovers the count.  Both the measurability of the count and its
mean are read off this. -/
theorem roundCount_eq_tsum (A : Set E) (ω : RoundSpace E) :
    roundCount A ω = ∑' n : ℕ, (survives A n).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  by_cases h : ∃ k, ω k ∈ A
  · rw [roundCount_eq_find h]
    have hmem : ∀ n : ℕ, ω ∈ survives A n ↔ n ≤ Nat.find h := by
      intro n
      constructor
      · intro hn
        by_contra hlt
        exact hn (Nat.find h) (by omega) (Nat.find_spec h)
      · intro hn i hi
        exact Nat.find_min h (by omega)
    have hzero : ∀ n ∉ Finset.range (Nat.find h + 1),
        (survives A n).indicator (fun _ => (1 : ℝ≥0∞)) ω = 0 := by
      intro n hn
      rw [Set.indicator_of_notMem]
      rw [hmem n]
      simp only [Finset.mem_range, not_lt] at hn
      omega
    rw [tsum_eq_sum hzero]
    have : ∀ n ∈ Finset.range (Nat.find h + 1),
        (survives A n).indicator (fun _ => (1 : ℝ≥0∞)) ω = 1 := by
      intro n hn
      refine Set.indicator_of_mem ?_ _
      rw [hmem n]
      simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hn
    rw [Finset.sum_congr rfl this]
    simp
  · simp only [not_exists] at h
    rw [roundCount_eq_top_iff.mpr h]
    have hall : ∀ n : ℕ, (survives A n).indicator (fun _ => (1 : ℝ≥0∞)) ω = 1 :=
      fun n => Set.indicator_of_mem (show ω ∈ survives A n from fun i _ => h i) _
    simp only [hall]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm

/-! ## Measurability -/

omit [MeasurableSpace E] in
/-- The survival event is the cylinder `Set.pi (range n) (fun _ => Aᶜ)`. -/
theorem survives_eq_pi (A : Set E) (n : ℕ) :
    survives A n = Set.pi (↑(Finset.range n)) (fun _ : ℕ => Aᶜ) := by
  ext ω
  simp [survives, Set.mem_pi]

theorem measurableSet_survives {A : Set E} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet (survives A n) := by
  rw [survives_eq_pi]
  exact MeasurableSet.pi (Finset.range n).countable_toSet fun _ _ => hA.compl

/-- **The round count is measurable.**  It is a countable sum of indicators of
the survival cylinders, each of which is measurable; the state is `ℕ`-indexed and
`ℝ≥0∞`-valued, so no countable-determination argument is needed. -/
theorem measurable_roundCount {A : Set E} (hA : MeasurableSet A) :
    Measurable (roundCount (E := E) A) := by
  have : roundCount (E := E) A
      = fun ω => ∑' n : ℕ, (survives A n).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
    funext (roundCount_eq_tsum A)
  rw [this]
  exact Measurable.tsum fun n =>
    measurable_const.indicator (measurableSet_survives hA n)

/-! ## The mean -/

/-- **The survival probability is `ν(Aᶜ)ⁿ`.**

This is the i.i.d. content of the construction, and it is not assumed: the
survival event is a cylinder, and `MeasureTheory.Measure.infinitePi_pi` evaluates
the product measure on a cylinder as the product of the coordinate masses, each
of which is `ν Aᶜ`. -/
theorem roundsMeasure_survives (ν : Measure E) [IsProbabilityMeasure ν] {A : Set E}
    (hA : MeasurableSet A) (n : ℕ) : roundsMeasure ν (survives A n) = ν Aᶜ ^ n := by
  rw [survives_eq_pi, roundsMeasure,
    Measure.infinitePi_pi _ (fun _ _ => hA.compl)]
  simp

/-- **The mean number of rounds, exactly**: `E[rounds] = 1 / Pr[accept]`.

No inequality, no hypothesis on `ν A` beyond measurability of `A`: when
`ν A = 0` both sides are `⊤`, which is the honest reading — a loop that never
accepts never stops.  The proof is the tail identity, `Tonelli` for a countable
sum of indicators, `Arlib.Probability.roundsMeasure_survives`, and
`ENNReal.tsum_geometric`. -/
theorem lintegral_roundCount (ν : Measure E) [IsProbabilityMeasure ν] {A : Set E}
    (hA : MeasurableSet A) :
    ∫⁻ ω, roundCount A ω ∂(roundsMeasure ν) = (ν A)⁻¹ := by
  calc ∫⁻ ω, roundCount A ω ∂(roundsMeasure ν)
      = ∫⁻ ω, ∑' n : ℕ, (survives A n).indicator (fun _ => (1 : ℝ≥0∞)) ω
          ∂(roundsMeasure ν) := by
        exact lintegral_congr fun ω => roundCount_eq_tsum A ω
    _ = ∑' n : ℕ, ∫⁻ ω, (survives A n).indicator (fun _ => (1 : ℝ≥0∞)) ω
          ∂(roundsMeasure ν) :=
        lintegral_tsum fun n =>
          (measurable_const.indicator (measurableSet_survives hA n)).aemeasurable
    _ = ∑' n : ℕ, roundsMeasure ν (survives A n) := by
        exact tsum_congr fun n => lintegral_indicator_one (measurableSet_survives hA n)
    _ = ∑' n : ℕ, ν Aᶜ ^ n := tsum_congr fun n => roundsMeasure_survives ν hA n
    _ = (1 - ν Aᶜ)⁻¹ := ENNReal.tsum_geometric _
    _ = (ν A)⁻¹ := by
        rw [prob_compl_eq_one_sub hA, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]

/-- **`E[rounds] ≤ 1/p` from a per-round acceptance bound `p ≤ Pr[accept]`.**

The whole point of the file, in one line off the exact mean.  The only hypotheses
are `IsProbabilityMeasure ν`, `MeasurableSet A`, and `p ≤ ν A`. -/
theorem lintegral_roundCount_le (ν : Measure E) [IsProbabilityMeasure ν] {A : Set E}
    (hA : MeasurableSet A) {p : ℝ≥0∞} (hp : p ≤ ν A) :
    ∫⁻ ω, roundCount A ω ∂(roundsMeasure ν) ≤ p⁻¹ := by
  rw [lintegral_roundCount ν hA]
  exact ENNReal.inv_le_inv.mpr hp

/-! ## A `ℕ`-valued round count, and the Bochner expectation

`Arlib.Probability.roundCount` is `ℝ≥0∞`-valued so that non-termination can cost
`⊤`.  A Bochner integral wants a real-valued — here `ℕ`-valued — random variable,
and that is `Arlib.Probability.roundCountNat`, whose value on a trajectory that
never accepts is the junk `1`.

That junk **undercounts**, which is the dangerous direction for an upper bound,
so it is fenced off rather than waved away: `roundCountNat` and `roundCount`
agree wherever acceptance happens at all
(`Arlib.Probability.coe_roundCountNat_eq_roundCount`), the never-accepting event
is null as soon as `0 < ν A` (`Arlib.Probability.measure_neverAccepts`, i.e. the
loop terminates almost surely), and so the two agree almost everywhere
(`Arlib.Probability.coe_roundCountNat_ae_eq`).  Every bound in this subsection
carries a strictly positive acceptance probability, so the junk value is never
load-bearing.

The geometric-mean step is `Arlib.Geometric` (a separate module): the tail bound
`Pr[N > n] ≤ (1-p)ⁿ` is proved here from
`Arlib.Probability.roundsMeasure_survives`, and
`Arlib.Geometric.lintegral_natCast_le_inv_of_geometric_tail` /
`Arlib.Geometric.integral_natCast_le_inv` turn it into `E[N] ≤ 1/p`. -/

/-- A `Measurable` criterion for a `ℕ`-valued map from its tail sets. -/
private theorem measurable_of_measurableSet_lt {Ω : Type*} [MeasurableSpace Ω] {N : Ω → ℕ}
    (h : ∀ n : ℕ, MeasurableSet {ω | n < N ω}) : Measurable N := by
  refine measurable_to_countable' fun m => ?_
  match m with
  | 0 =>
      have : N ⁻¹' {0} = {ω | 0 < N ω}ᶜ := by ext ω; simp
      rw [this]; exact (h 0).compl
  | (m + 1) =>
      have : N ⁻¹' {m + 1} = {ω | m < N ω} \ {ω | m + 1 < N ω} := by
        ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff,
          Set.mem_setOf_eq, not_lt]; omega
      rw [this]; exact (h m).diff (h (m + 1))

/-- **The round count as a `ℕ`-valued random variable**: `sInf` of the accepted
indices, plus one.  On a trajectory that never accepts, `Nat.sInf ∅ = 0` makes
this `1` — a junk value; see the section docstring for how it is fenced off. -/
noncomputable def roundCountNat (A : Set E) (ω : RoundSpace E) : ℕ :=
  sInf {k | ω k ∈ A} + 1

omit [MeasurableSpace E] in
/-- Running past round `n` implies surviving the first `n` rounds.  (The converse
fails only on the never-accepting trajectories, where the junk value bites; that
is exactly why this is an inclusion and not an equality.) -/
theorem lt_roundCountNat_subset_survives (A : Set E) (n : ℕ) :
    {ω | n < roundCountNat A ω} ⊆ survives A n := by
  intro ω hω i hi hmem
  have hle : n ≤ sInf {k | ω k ∈ A} := Nat.lt_succ_iff.mp hω
  have : sInf {k | ω k ∈ A} ≤ i := Nat.sInf_le hmem
  omega

/-- **The trajectories that never accept.** -/
def neverAccepts (A : Set E) : Set (RoundSpace E) := {ω | ∀ k, ω k ∉ A}

omit [MeasurableSpace E] in
theorem neverAccepts_eq_iInter (A : Set E) : neverAccepts A = ⋂ n : ℕ, survives A n := by
  ext ω
  simp only [neverAccepts, Set.mem_setOf_eq, Set.mem_iInter, survives]
  exact ⟨fun h n i _ => h i, fun h k => h (k + 1) k (Nat.lt_succ_self k)⟩

theorem measurableSet_neverAccepts {A : Set E} (hA : MeasurableSet A) :
    MeasurableSet (neverAccepts A) := by
  rw [neverAccepts_eq_iInter]
  exact MeasurableSet.iInter fun n => measurableSet_survives hA n

omit [MeasurableSpace E] in
/-- The exact description of the tail sets of `Arlib.Probability.roundCountNat`:
surviving `n` rounds *and* accepting eventually. -/
theorem lt_roundCountNat_eq (A : Set E) (n : ℕ) :
    {ω | n < roundCountNat A ω}
      = if n = 0 then Set.univ else survives A n \ neverAccepts A := by
  split_ifs with hn
  · subst hn
    ext ω; simp [roundCountNat]
  · ext ω
    constructor
    · intro hω
      have hle : n ≤ sInf {k | ω k ∈ A} := Nat.lt_succ_iff.mp hω
      have hne : {k | ω k ∈ A}.Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        rw [hemp] at hle
        simp only [Nat.sInf_empty, Nat.le_zero] at hle
        exact hn hle
      exact ⟨lt_roundCountNat_subset_survives A n hω, fun hnv => by
        obtain ⟨k, hk⟩ := hne; exact hnv k hk⟩
    · rintro ⟨hsurv, hnv⟩
      have hne : {k | ω k ∈ A}.Nonempty := by
        simp only [neverAccepts, Set.mem_setOf_eq, not_forall, not_not] at hnv
        obtain ⟨k, hk⟩ := hnv
        exact ⟨k, hk⟩
      have hmem : sInf {k | ω k ∈ A} ∈ {k | ω k ∈ A} := Nat.sInf_mem hne
      have : n ≤ sInf {k | ω k ∈ A} := by
        by_contra hlt
        exact hsurv _ (not_le.mp hlt) hmem
      exact Nat.lt_succ_iff.mpr this

theorem measurableSet_lt_roundCountNat {A : Set E} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet {ω : RoundSpace E | n < roundCountNat A ω} := by
  rw [lt_roundCountNat_eq]
  split_ifs
  · exact MeasurableSet.univ
  · exact (measurableSet_survives hA n).diff (measurableSet_neverAccepts hA)

theorem measurable_roundCountNat {A : Set E} (hA : MeasurableSet A) :
    Measurable (roundCountNat (E := E) A) :=
  measurable_of_measurableSet_lt fun n => measurableSet_lt_roundCountNat hA n

omit [MeasurableSpace E] in
/-- **The two counts agree wherever the loop terminates.** -/
theorem coe_roundCountNat_eq_roundCount {A : Set E} {ω : RoundSpace E}
    (h : ∃ k, ω k ∈ A) : (roundCountNat A ω : ℝ≥0∞) = roundCount A ω := by
  have hne : {k | ω k ∈ A}.Nonempty := h
  have hmem : sInf {k | ω k ∈ A} ∈ {k | ω k ∈ A} := Nat.sInf_mem hne
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun k hk => ?_
    have hle : sInf {k | ω k ∈ A} ≤ k := Nat.sInf_le hk
    have : ((sInf {k | ω k ∈ A} : ℕ) : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by exact_mod_cast hle
    simpa [roundCountNat] using add_le_add_right this 1
  · refine le_trans (iInf₂_le (f := fun k (_ : k ∈ acceptedAt A ω) => ((k : ℝ≥0∞) + 1))
      (sInf {k | ω k ∈ A}) hmem) ?_
    simp [roundCountNat]

/-- **The loop terminates almost surely** when the acceptance probability is
positive.  Nothing is assumed about `ν A` beyond `0 < ν A`; the proof is that the
never-accepting event sits inside every `survives A n`, whose masses `ν(Aᶜ)ⁿ`
tend to `0`. -/
theorem measure_neverAccepts (ν : Measure E) [IsProbabilityMeasure ν] {A : Set E}
    (hA : MeasurableSet A) (hpos : 0 < ν A) : roundsMeasure ν (neverAccepts A) = 0 := by
  have hlt : ν Aᶜ < 1 := by
    rw [prob_compl_eq_one_sub hA]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'
  have hle : ∀ n : ℕ, roundsMeasure ν (neverAccepts A) ≤ ν Aᶜ ^ n := by
    intro n
    rw [← roundsMeasure_survives ν hA n]
    refine measure_mono ?_
    rw [neverAccepts_eq_iInter]
    exact Set.iInter_subset _ n
  have hzero : roundsMeasure ν (neverAccepts A) ≤ 0 :=
    ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hle
  exact nonpos_iff_eq_zero.mp hzero

/-- **The two counts agree almost everywhere** when the acceptance probability is
positive: the `ℕ`-valued count's junk value lives on a null set. -/
theorem coe_roundCountNat_ae_eq (ν : Measure E) [IsProbabilityMeasure ν] {A : Set E}
    (hA : MeasurableSet A) (hpos : 0 < ν A) :
    (fun ω => (roundCountNat A ω : ℝ≥0∞)) =ᵐ[roundsMeasure ν] roundCount A := by
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_neverAccepts ν hA hpos)
  simp only [Set.mem_setOf_eq] at hω
  show ∀ k, ω k ∉ A
  intro k hk
  exact hω (coe_roundCountNat_eq_roundCount ⟨k, hk⟩)

/-- **The geometric tail**: `Pr[still running after n rounds] ≤ ν(Aᶜ)ⁿ`.  This is
the hypothesis `Arlib.Geometric`'s expectation bounds consume. -/
theorem measure_lt_roundCountNat_le (ν : Measure E) [IsProbabilityMeasure ν] {A : Set E}
    (hA : MeasurableSet A) (n : ℕ) :
    roundsMeasure ν {ω | n < roundCountNat A ω} ≤ ν Aᶜ ^ n :=
  (measure_mono (lt_roundCountNat_subset_survives A n)).trans
    (roundsMeasure_survives ν hA n).le

/-- **`E[rounds] ≤ 1/p` for the `ℕ`-valued count**, in `ℝ≥0∞`, via
`Arlib.Geometric.lintegral_natCast_le_inv_of_geometric_tail`. -/
theorem lintegral_roundCountNat_le (ν : Measure E) [IsProbabilityMeasure ν] {A : Set E}
    (hA : MeasurableSet A) {p : ℝ≥0∞} (hp : p ≤ ν A) :
    ∫⁻ ω, (roundCountNat A ω : ℝ≥0∞) ∂(roundsMeasure ν) ≤ p⁻¹ := by
  refine Arlib.Geometric.lintegral_natCast_le_inv_of_geometric_tail
    (measurable_roundCountNat hA) (hp.trans prob_le_one) fun n => ?_
  refine (measure_lt_roundCountNat_le ν hA n).trans ?_
  gcongr
  rw [prob_compl_eq_one_sub hA]
  exact tsub_le_tsub_left hp 1

/-- The real-`p` form of the tail, as `Arlib.Geometric`'s Bochner bounds want
it. -/
theorem measure_lt_roundCountNat_le_ofReal (ν : Measure E) [IsProbabilityMeasure ν]
    {A : Set E} (hA : MeasurableSet A) {p : ℝ} (hp0 : 0 < p)
    (hp : ENNReal.ofReal p ≤ ν A) (n : ℕ) :
    roundsMeasure ν {ω | n < roundCountNat A ω} ≤ ENNReal.ofReal ((1 - p) ^ n) := by
  have hp1 : p ≤ 1 := by
    by_contra hgt
    have : (1 : ℝ≥0∞) < ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one |>.mpr (not_le.mp hgt)
    exact absurd (this.trans_le (hp.trans prob_le_one)) (lt_irrefl 1)
  have h1p : (0 : ℝ) ≤ 1 - p := by linarith
  refine (measure_lt_roundCountNat_le ν hA n).trans ?_
  rw [ENNReal.ofReal_pow h1p]
  gcongr
  rw [prob_compl_eq_one_sub hA, ENNReal.ofReal_sub _ hp0.le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hp 1

/-- **The round count is integrable**, so the Bochner integral below is a real
mean and not the junk value `0`. -/
theorem integrable_roundCountNat (ν : Measure E) [IsProbabilityMeasure ν] {A : Set E}
    (hA : MeasurableSet A) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hp : ENNReal.ofReal p ≤ ν A) :
    Integrable (fun ω => (roundCountNat A ω : ℝ)) (roundsMeasure ν) :=
  Arlib.Geometric.integrable_natCast_of_geometric_tail (measurable_roundCountNat hA)
    hp0 hp1 (measure_lt_roundCountNat_le_ofReal ν hA hp0 hp)

/-- **`E[rounds] ≤ 1/p` as a Bochner integral of a real-valued random variable.**

This is the statement a reader of Kannan–Vempala would recognise as "the expected
number of draws".  It is `Arlib.Geometric.integral_natCast_le_inv` fed the tail
bound proved here. -/
theorem integral_roundCountNat_le (ν : Measure E) [IsProbabilityMeasure ν] {A : Set E}
    (hA : MeasurableSet A) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hp : ENNReal.ofReal p ≤ ν A) :
    ∫ ω, (roundCountNat A ω : ℝ) ∂(roundsMeasure ν) ≤ 1 / p :=
  Arlib.Geometric.integral_natCast_le_inv (measurable_roundCountNat hA) hp0 hp1
    (measure_lt_roundCountNat_le_ofReal ν hA hp0 hp)

/-! ## The two constants of `Arlib.KV97`

Neither of the two theorems below imports anything from `Arlib.KV97`: they take
the acceptance bound as a hypothesis, which is exactly what
`Arlib.KV97.acceptance_ge_nine_div_twenty_exp` and
`Arlib.KV97.acceptance_ge_one_eighth` (or, against an actual measure,
`Arlib.KV97.toReal_roundedLaw_ge_one_eighth`) supply.  See the module docstring
for why that composition is *not* a step toward any runtime claim. -/

/-- The reciprocal of the sharp constant, in `ℝ≥0∞`: `(9/(20e))⁻¹ = 20e/9`. -/
theorem inv_ofReal_nine_div_twenty_exp :
    (ENNReal.ofReal (9 / (20 * Real.exp 1)))⁻¹
      = ENNReal.ofReal (20 * Real.exp 1 / 9) := by
  have hpos : (0 : ℝ) < 9 / (20 * Real.exp 1) := by positivity
  rw [← ENNReal.ofReal_inv_of_pos hpos]
  congr 1
  rw [inv_div]

/-- **`E[rounds] ≤ 20e/9 ≈ 6.0405`** when the one-round acceptance probability is
at least `9/(20e)` — the constant `Arlib.KV97.acceptance_ge_nine_div_twenty_exp`
actually proves. -/
theorem lintegral_roundCount_le_twentyExpDivNine (ν : Measure E) [IsProbabilityMeasure ν]
    {A : Set E} (hA : MeasurableSet A) (hp : ENNReal.ofReal (9 / (20 * Real.exp 1)) ≤ ν A) :
    ∫⁻ ω, roundCount A ω ∂(roundsMeasure ν) ≤ ENNReal.ofReal (20 * Real.exp 1 / 9) :=
  inv_ofReal_nine_div_twenty_exp ▸ lintegral_roundCount_le ν hA hp

/-- **`E[rounds] ≤ 8`**, the paper's round number, from acceptance `≥ 1/8`
(`Arlib.KV97.acceptance_ge_one_eighth`). -/
theorem lintegral_roundCount_le_eight (ν : Measure E) [IsProbabilityMeasure ν]
    {A : Set E} (hA : MeasurableSet A) (hp : (8 : ℝ≥0∞)⁻¹ ≤ ν A) :
    ∫⁻ ω, roundCount A ω ∂(roundsMeasure ν) ≤ 8 := by
  have := lintegral_roundCount_le ν hA hp
  rwa [inv_inv] at this

/-- The real-valued form of `Arlib.Probability.lintegral_roundCount_le_twentyExpDivNine`.
`ENNReal.toReal` is honest here because the left-hand side is finite: it is
bounded by the finite `ENNReal.ofReal (20e/9)`. -/
theorem toReal_lintegral_roundCount_le_twentyExpDivNine (ν : Measure E)
    [IsProbabilityMeasure ν] {A : Set E} (hA : MeasurableSet A)
    (hp : ENNReal.ofReal (9 / (20 * Real.exp 1)) ≤ ν A) :
    (∫⁻ ω, roundCount A ω ∂(roundsMeasure ν)).toReal ≤ 20 * Real.exp 1 / 9 := by
  have h := lintegral_roundCount_le_twentyExpDivNine ν hA hp
  have hpos : (0 : ℝ) ≤ 20 * Real.exp 1 / 9 := by positivity
  calc (∫⁻ ω, roundCount A ω ∂(roundsMeasure ν)).toReal
      ≤ (ENNReal.ofReal (20 * Real.exp 1 / 9)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = 20 * Real.exp 1 / 9 := ENNReal.toReal_ofReal hpos

/-- The real-valued form of `Arlib.Probability.lintegral_roundCount_le_eight`. -/
theorem toReal_lintegral_roundCount_le_eight (ν : Measure E) [IsProbabilityMeasure ν]
    {A : Set E} (hA : MeasurableSet A) (hp : (8 : ℝ≥0∞)⁻¹ ≤ ν A) :
    (∫⁻ ω, roundCount A ω ∂(roundsMeasure ν)).toReal ≤ 8 := by
  have h := lintegral_roundCount_le_eight ν hA hp
  calc (∫⁻ ω, roundCount A ω ∂(roundsMeasure ν)).toReal
      ≤ ((8 : ℝ≥0∞)).toReal := ENNReal.toReal_mono (by simp) h
    _ = 8 := by simp

/-- `9/(20e) ≤ 1`: the sharp constant really is a probability. -/
theorem nine_div_twenty_exp_le_one : 9 / (20 * Real.exp 1) ≤ 1 := by
  have h : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) (by norm_num)
    linarith
  rw [div_le_one (by positivity)]
  linarith

/-- **`E[rounds] ≤ 20e/9` as a Bochner integral** — the sharp constant, over the
`ℕ`-valued round count.  This is the form closest to the sentence "the rejection
loop makes `O(1)` expected draws". -/
theorem integral_roundCountNat_le_twentyExpDivNine (ν : Measure E) [IsProbabilityMeasure ν]
    {A : Set E} (hA : MeasurableSet A)
    (hp : ENNReal.ofReal (9 / (20 * Real.exp 1)) ≤ ν A) :
    ∫ ω, (roundCountNat A ω : ℝ) ∂(roundsMeasure ν) ≤ 20 * Real.exp 1 / 9 := by
  have hp0 : (0 : ℝ) < 9 / (20 * Real.exp 1) := by positivity
  refine (integral_roundCountNat_le ν hA hp0 nine_div_twenty_exp_le_one hp).trans_eq ?_
  rw [one_div, inv_div]

/-- **`E[rounds] ≤ 8` as a Bochner integral** — the paper's round number. -/
theorem integral_roundCountNat_le_eight (ν : Measure E) [IsProbabilityMeasure ν]
    {A : Set E} (hA : MeasurableSet A) (hp : ENNReal.ofReal (1 / 8) ≤ ν A) :
    ∫ ω, (roundCountNat A ω : ℝ) ∂(roundsMeasure ν) ≤ 8 := by
  refine (integral_roundCountNat_le ν hA (by norm_num) (by norm_num) hp).trans_eq ?_
  norm_num

/-- `20e/9 < 6.041`: the sharp bound is a genuine, small, absolute constant, not a
vacuous `≤ ⊤`. -/
theorem twentyExpDivNine_lt : 20 * Real.exp 1 / 9 < 6.041 := by
  have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  nlinarith [h]

end Core

/-! ## Non-vacuity: a loop that really does run a random number of rounds

`CLAUDE.md` §11 asks for a witness.  Everything above is trivially satisfied by a
`ν` with `ν A = 1` (the loop always stops on round one) or by a degenerate sample
space; the instance below is neither.  It reuses `Arlib.Probability.coin`, the
fair coin `½·δ₀ + ½·δ₁` of `Arlib.Probability.RunPlumbing`, with the acceptance
event `{1}`: the acceptance probability is strictly between `0` and `1`, the
survival probabilities `2⁻ⁿ` decay geometrically and are never `0` or `1` for
`n ≥ 1`, and the mean is exactly `2`. -/

section Witness

/-- The acceptance event of the witness: the coin came up `1`. -/
theorem coin_one : coin {(1 : ℝ)} = 2⁻¹ := by
  rw [coin_apply (measurableSet_singleton _)]
  simp

/-- **The witness is genuinely random**: surviving `n` rounds has probability
`2⁻ⁿ`, which for `n ≥ 1` is neither `0` nor `1`.  So neither the round count nor
the survival events are degenerate. -/
theorem coin_survives (n : ℕ) :
    roundsMeasure coin (survives {(1 : ℝ)} n) = (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [roundsMeasure_survives coin (measurableSet_singleton _) n]
  congr 1
  rw [prob_compl_eq_one_sub (measurableSet_singleton _), coin_one]
  rw [ENNReal.sub_eq_of_eq_add (by simp) (by rw [ENNReal.inv_two_add_inv_two])]

/-- **The mean is exactly `2`** for the fair coin: not `0`, not `⊤`.  So
`Arlib.Probability.lintegral_roundCount` is not the trivial identity `⊤ = ⊤`, and
the bounds above are not vacuous. -/
theorem coin_lintegral_roundCount :
    ∫⁻ ω, roundCount {(1 : ℝ)} ω ∂(roundsMeasure coin) = 2 := by
  rw [lintegral_roundCount coin (measurableSet_singleton _), coin_one, inv_inv]

/-- The `ℕ`-valued count has the same mean, as a Bochner integral: the fair-coin
loop makes `2` expected draws. -/
theorem coin_integral_roundCountNat_le :
    ∫ ω, (roundCountNat {(1 : ℝ)} ω : ℝ) ∂(roundsMeasure coin) ≤ 2 := by
  have hp : ENNReal.ofReal (1 / 2 : ℝ) ≤ coin {(1 : ℝ)} := by
    rw [coin_one]
    rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have := integral_roundCountNat_le coin (measurableSet_singleton _)
    (p := 1 / 2) (by norm_num) (by norm_num) hp
  norm_num at this ⊢
  exact this

end Witness

/-! ## The Kannan–Vempala rejection loop itself

Everything above is about an abstract one-round law `ν` and an abstract
acceptance event `A`.  This last section instantiates it at the *actual* objects
of `Arlib.Lattice.KV97.Lemma1`: `ν` is `Arlib.KV97.roundedLaw P' f`, the law of
the rounded draw, and `A` is `{z : ℤⁿ | z ∈ P}`, the event that the rounded point
lands in the polytope.  The conclusion is a bound on the expected number of
draws Kannan–Vempala's sampler makes.

Re-read the module docstring before quoting any of this: the result is an orphan
in both of the senses recorded there. -/

section KV97

open Arlib.KV97 Arlib.Lattice Arlib.Lattice.Rounding

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- **When the law of the rounded draw is a probability measure.**

`Arlib.KV97.roundedLaw` is deliberately *not* claimed to be one — see the
docstring of `Arlib.KV97.roundedLaw_apply`, "the word *probability* is the
caller's to earn".  It is one exactly when `f` is a genuine probability density
on `S`, since the rounding kernel `Arlib.Lattice.Rounding.roundLaw` is already a
probability measure at every point (`isProbabilityMeasure_roundLaw`).  This lemma
earns the word, from that one hypothesis and no other. -/
theorem isProbabilityMeasure_roundedLaw {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    (hnorm : ∫⁻ p in S, ENNReal.ofReal (f p) = 1) :
    IsProbabilityMeasure (roundedLaw S f) := by
  constructor
  rw [roundedLaw_apply hf]
  simpa using hnorm

/-- The acceptance event lives on the countable, discrete space `ℤⁿ`, so it is
measurable with no hypothesis on `P` at all. -/
theorem measurableSet_latMem (P : Set (EuclideanSpace ℝ (Fin n))) :
    MeasurableSet {z : Fin n → ℤ | latEmb n z ∈ P} :=
  (Set.to_countable _).measurableSet

/-- **Lemma 1's bound, in `ℝ≥0∞` and at the sharp constant.**

`Arlib.KV97.toReal_roundedLaw_ge_one_eighth` gives the paper's `1/8` about
`(roundedLaw …).toReal`.  This is the same composition at the constant the
argument actually yields, `9/(20e) ≈ 0.1655`, and stated about the mass itself
rather than its `toReal`, which is the form the round-count machinery consumes.
`IsProbabilityMeasure` enters only to know the mass is not `⊤`. -/
theorem ofReal_nine_div_twenty_exp_le_roundedLaw {F : Type*}
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
      (inflated A b c r))
    (hnorm : ∫⁻ p in inflated A b c r, ENNReal.ofReal (f p) = 1) :
    ENNReal.ofReal (9 / (20 * Real.exp 1))
      ≤ roundedLaw (inflated A b c r) f {z | latEmb n z ∈ P} := by
  haveI := isProbabilityMeasure_roundedLaw (S := inflated A b c r) hf hnorm
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _),
    toReal_roundedLaw_eq_acceptance hlat henum hf hf0 hint]
  exact acceptance_ge_nine_div_twenty_exp _ _ hγ hc hball hfin hη0 hη hε hE hlow
    hlattice_nonconv hthin

/-- **The expected number of draws Kannan–Vempala's sampler makes is at most
`20e/9 ≈ 6.04`.**

This is the file's headline over the real objects: the rounds are i.i.d. draws
from `Arlib.KV97.roundedLaw P' f` (constructed, not assumed — see
`Arlib.Probability.roundsMeasure`, `Arlib.Probability.iIndepFun_draw`), the loop
stops at the first round whose rounded point lies in `P`
(`Arlib.Probability.roundCount`), and the mean of that count is at most `20e/9`.

The hypotheses are exactly those of `Arlib.KV97.toReal_roundedLaw_ge_one_eighth`,
plus one: `hnorm`, that `f` integrates to `1` on `P'`.  That extra hypothesis is
not decorative — without it `roundedLaw` need not be a probability measure and
there is no process to build.  It is satisfiable (any normalised density), and it
is the only thing this file adds to Lemma 1's assumption bundle.

**This does not price `Ttc`'s `cSample`.**  See the module docstring. -/
theorem lintegral_roundCount_kv97 {F : Type*}
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
      (inflated A b c r))
    (hnorm : ∫⁻ p in inflated A b c r, ENNReal.ofReal (f p) = 1) :
    ∫⁻ ω, roundCount {z | latEmb n z ∈ P} ω
        ∂(roundsMeasure (roundedLaw (inflated A b c r) f))
      ≤ ENNReal.ofReal (20 * Real.exp 1 / 9) := by
  haveI := isProbabilityMeasure_roundedLaw (S := inflated A b c r) hf hnorm
  exact lintegral_roundCount_le_twentyExpDivNine _ (measurableSet_latMem P)
    (ofReal_nine_div_twenty_exp_le_roundedLaw hγ hc hball hfin hη0 hη hε hE hlow
      hlattice_nonconv hthin hlat henum hf hf0 hint hnorm)

/-- The same, as a real number: **at most `20e/9 < 6.041` expected draws**. -/
theorem toReal_lintegral_roundCount_kv97 {F : Type*}
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
      (inflated A b c r))
    (hnorm : ∫⁻ p in inflated A b c r, ENNReal.ofReal (f p) = 1) :
    (∫⁻ ω, roundCount {z | latEmb n z ∈ P} ω
        ∂(roundsMeasure (roundedLaw (inflated A b c r) f))).toReal
      ≤ 20 * Real.exp 1 / 9 := by
  haveI := isProbabilityMeasure_roundedLaw (S := inflated A b c r) hf hnorm
  exact toReal_lintegral_roundCount_le_twentyExpDivNine _ (measurableSet_latMem P)
    (ofReal_nine_div_twenty_exp_le_roundedLaw hγ hc hball hfin hη0 hη hε hE hlow
      hlattice_nonconv hthin hlat henum hf hf0 hint hnorm)

/-- **The headline, as a Bochner expectation of a `ℕ`-valued random variable.**

    ∫ ω, (number of draws Kannan–Vempala's sampler makes on ω : ℝ)  ≤  20e/9 < 6.041.

Same hypotheses as `Arlib.Probability.lintegral_roundCount_kv97`.  This is the
form that reads as "the rejection loop makes `O(1)` expected draws", which is
what Kannan–Vempala assert and never prove; the count is
`Arlib.Probability.roundCountNat` and it is integrable
(`Arlib.Probability.integrable_roundCountNat`), so the integral is a genuine mean
and not Bochner's junk value `0`.

**Still an orphan** — see the module docstring.  Nothing downstream in `Ttc`
consumes this, and it prices nothing. -/
theorem integral_roundCountNat_kv97 {F : Type*}
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
      (inflated A b c r))
    (hnorm : ∫⁻ p in inflated A b c r, ENNReal.ofReal (f p) = 1) :
    ∫ ω, (roundCountNat {z | latEmb n z ∈ P} ω : ℝ)
        ∂(roundsMeasure (roundedLaw (inflated A b c r) f))
      ≤ 20 * Real.exp 1 / 9 := by
  haveI := isProbabilityMeasure_roundedLaw (S := inflated A b c r) hf hnorm
  exact integral_roundCountNat_le_twentyExpDivNine _ (measurableSet_latMem P)
    (ofReal_nine_div_twenty_exp_le_roundedLaw hγ hc hball hfin hη0 hη hε hE hlow
      hlattice_nonconv hthin hlat henum hf hf0 hint hnorm)

end KV97

end Arlib.Probability
