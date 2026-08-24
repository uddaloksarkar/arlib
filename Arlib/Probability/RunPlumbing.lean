/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Probability.Independence.InfinitePi
import Arlib.Convexity.GaussianCooling.Estimator

/-!
# Independent runs of a product estimator: the probability space

This file builds the **probabilistic scaffolding** an estimator of the
Cousins–Vempala shape needs: `r` independent *runs*, each run a product of `m`
independent *phase scores*, together with a measurable median of the runs.

Everything here is stated over an *abstract* score: the randomness of run `j`,
phase `i` is one coordinate of an **arbitrary measurable space** `E`, and the
score is an arbitrary measurable `E → ℝ`.  No geometry, no sampler, no convex
body.

The coordinate space `E` carries **no assumption beyond `MeasurableSpace E`** —
no topology, no `BorelSpace`, no second countability, no standard-Borel
hypothesis, no `MeasurableSingletonClass`.  Only the coordinate *measures* are
constrained, and only by `IsProbabilityMeasure`.  So `E` may be a trajectory
space such as `ℕ → EuclideanSpace ℝ (Fin n)`; see the `traj*` declarations at the
end of the file for a worked non-`ℝ` instance.  The *scores* stay real-valued:
the median needs a linear order on the values, and `memLp_two_runProd` needs
`|·|` and `L²` on them.

## Two spaces

* **Finite.** `RunSpace E r m := Fin r → Fin m → E`, carrying `runMeasure ν :=
  Measure.pi fun j => Measure.pi fun i => ν j i` for an arbitrary family `ν` of
  probability measures on `E`.  A probability space by
  `MeasureTheory.Measure.pi.instIsProbabilityMeasure`.
* **Universal.** `NatRunSpace E := ℕ → ℕ → E` with
  `natRunMeasure ν := Measure.infinitePi fun j => Measure.infinitePi fun i => ν j i`.
  **This is the one a consumer wants**: an estimator interface fixes a single
  `Ω` and `μ` up front while the repetition count `r` and phase count `m` vary
  with the problem instance, so `r` and `m` must be arguments of the *theorems*,
  not of the space.  Every result below is proved in both forms; the universal
  ones carry the `nat` prefix.

Both are genuinely random, not a one-point space in disguise: see the
non-vacuity section.

## Main results

(each also in a `nat`-prefixed universal-space form)

* `Arlib.Probability.measurable_score` — each score is measurable.
* `Arlib.Probability.iIndepFun_score_phases` — for each run index `j`, the `m`
  phase scores of that run are independent.  This is the *within-block*
  independence; it is obtained by transporting `ProbabilityTheory.iIndepFun_pi`
  along the measure-preserving coordinate projection
  `MeasureTheory.measurePreserving_eval`.
* `Arlib.Probability.iIndepFun_runs` — the `r` runs, each the constant `c` times
  the product of its `m` phase scores, are independent.  This is the *grouping*
  step, and on this space it is `ProbabilityTheory.iIndepFun_pi` applied at the
  outer index, with the whole product over phases absorbed into the coordinate
  function.
* `Arlib.Probability.memLp_two_runProd` — the product over phases is in `L²`,
  from a uniform bound on the scores.
* `Arlib.Probability.medianSel`, `medianSel_isMedian`, `measurable_medianSel` —
  an explicit, measurable median selector for a finite family of reals, matching
  `Arlib.GaussianCooling.IsMedian`.  Shared by both spaces.
* `Arlib.Probability.not_ae_const_of_coin_coord` and the `wit*` / `natWit*`
  declarations — the **non-vacuity** witness: two runs of two phases (resp. every
  `(r, m)`) of independent fair coins, with a non-constant score, and a proof
  that no score is almost-everywhere constant.
* The `traj*` declarations — a second non-vacuity witness whose coordinate space
  is **not** `ℝ` but the trajectory space `ℕ → ℝ`, exhibiting that the results
  above really are available at an abstract `E`.

## Auxiliary results proved here that Mathlib appears to lack

* `Arlib.Probability.measurable_finset_inf'` — the `inf'` dual of
  `Finset.measurable_sup'`.
* `Arlib.Probability.iIndepFun_comp_measurePreserving` — independence is
  transported by a measure-preserving map (precomposition on the sample space).
* `Arlib.Probability.iIndepFun_const` — a family of constants is independent.
  (Mathlib has the two-variable `ProbabilityTheory.indepFun_const_left/right`
  but no `iIndepFun` version.)
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Arlib.Probability

/-! ## An `inf'` companion to `Finset.measurable_sup'` -/

/-- **`Finset.inf'` of measurable functions is measurable.**  The exact dual of
`Finset.measurable_sup'`, which Mathlib has; the `inf'` form does not appear to
be there.  Assumes measurability of the whole family (not merely on `s`), which
is all the uses below need. -/
theorem measurable_finset_inf' {δ ι α : Type*} [MeasurableSpace δ] [MeasurableSpace α]
    [Lattice α] [MeasurableInf₂ α] {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ i, Measurable (f i)) :
    Measurable fun x => s.inf' hs fun i => f i x := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hf a
  | cons a s ha hs ih =>
      have : (fun x => (Finset.cons a s ha).inf' (by simp) fun i => f i x)
          = fun x => (f a x) ⊓ (s.inf' hs fun i => f i x) := by
        funext x; rw [Finset.inf'_cons]
      rw [this]
      exact (hf a).inf ih

/-! ## An explicit measurable median selector -/

/-- **A median of a finite family of reals, chosen explicitly.**

`medianSel v` is the largest entry `v i` that is `≤` at least half the family
(`r ≤ 2 · #{j | v i ≤ v j}`); entries failing that test are replaced by the
minimum of the family, which never raises the maximum because at least one entry
— the minimum — passes the test.  On the empty family it is `0`.

Written with `sup'`/`inf'` rather than by sorting, because that makes
`Arlib.Probability.measurable_medianSel` a two-line consequence of
`Finset.measurable_sup'`, whereas measurability of an order statistic obtained
from `Tuple.sort` is not available. -/
noncomputable def medianSel {r : ℕ} (v : Fin r → ℝ) : ℝ :=
  if h : 0 < r then
    Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩ fun i =>
      if r ≤ 2 * (Finset.univ.filter fun j => v i ≤ v j).card then v i
      else Finset.univ.inf' ⟨⟨0, h⟩, Finset.mem_univ _⟩ v
  else 0

/-- The median property of `Arlib.Probability.medianSel`, stated for an opaque
`F` satisfying the defining equation.  Factored out only so that the proof can
rewrite with `hF` instead of unfolding a `dite`. -/
private theorem medianSel_aux {r : ℕ} (hr : 0 < r) (v : Fin r → ℝ)
    (hne : (Finset.univ : Finset (Fin r)).Nonempty) (F : Fin r → ℝ)
    (hF : ∀ i, F i = if r ≤ 2 * (Finset.univ.filter fun j => v i ≤ v j).card then v i
      else Finset.univ.inf' hne v) :
    Arlib.GaussianCooling.IsMedian v (Finset.univ.sup' hne F) := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' hne v
  have hi₀le : ∀ j, v i₀ ≤ v j := fun j => by
    rw [← hi₀]; exact Finset.inf'_le _ (Finset.mem_univ j)
  have hPi₀ : r ≤ 2 * (Finset.univ.filter fun j => v i₀ ≤ v j).card := by
    rw [Finset.filter_true_of_mem fun j _ => hi₀le j, Finset.card_univ, Fintype.card_fin]
    omega
  have hle : ∀ j, F j ≤ Finset.univ.sup' hne F := fun j =>
    Finset.le_sup' F (Finset.mem_univ j)
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_mem_eq_sup' hne F
  set Z : ℝ := Finset.univ.sup' hne F with hZdef
  obtain ⟨i, hPi, hzi⟩ :
      ∃ i, r ≤ 2 * (Finset.univ.filter fun j => v i ≤ v j).card ∧ Z = v i := by
    by_cases hP1 : r ≤ 2 * (Finset.univ.filter fun j => v i₁ ≤ v j).card
    · exact ⟨i₁, hP1, by rw [hi₁, hF i₁, if_pos hP1]⟩
    · exact ⟨i₀, hPi₀, by rw [hi₁, hF i₁, if_neg hP1, hi₀]⟩
  refine ⟨?_, ?_⟩
  · by_cases hSe : (Finset.univ.filter fun j => Z < v j).Nonempty
    · obtain ⟨j₀, hj₀S, hj₀min⟩ := Finset.exists_min_image _ v hSe
      rw [Finset.mem_filter] at hj₀S
      have hfail : ¬ r ≤ 2 * (Finset.univ.filter fun k => v j₀ ≤ v k).card := by
        intro hPj₀
        have h1 : v j₀ ≤ Z := by have := hle j₀; rwa [hF j₀, if_pos hPj₀] at this
        exact absurd hj₀S.2 (not_lt.mpr h1)
      have hsub : (Finset.univ.filter fun j => Z < v j) ⊆
          (Finset.univ.filter fun k => v j₀ ≤ v k) := by
        intro k hk
        rw [Finset.mem_filter] at hk ⊢
        exact ⟨hk.1, hj₀min k (Finset.mem_filter.mpr hk)⟩
      have hcard := Finset.card_le_card hsub
      have hsplit : (Finset.univ.filter fun j => v j ≤ Z).card
          + (Finset.univ.filter fun j => Z < v j).card = r := by
        have h := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin r))) (p := fun j => v j ≤ Z)
        simp only [not_le, Finset.card_univ, Fintype.card_fin] at h
        exact h
      omega
    · have hall : ∀ j ∈ (Finset.univ : Finset (Fin r)), v j ≤ Z := by
        intro j _
        by_contra hcon
        exact hSe ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, not_le.mp hcon⟩⟩
      rw [Finset.filter_true_of_mem hall, Finset.card_univ, Fintype.card_fin]
      omega
  · rw [hzi]; exact hPi

/-- **`medianSel` really is a median.**  Unconditional: no hypothesis on `v`, and
the empty family is covered (`Arlib.GaussianCooling.IsMedian` is vacuous there).

Proof.  Write `z = medianSel v`.  First, `z = v i` for some `i` passing the test
`r ≤ 2 · #{j | v i ≤ v j}` — either the maximum is attained at a passing entry,
or it is attained at the substituted minimum, and the minimum itself passes.
That gives the "at least half weakly above `z`" half.  For "at least half weakly
below": any `j` with `z < v j` must *fail* the test (a passing entry is `≤` the
maximum `z`), and the `v`-smallest such `j` is `≤` all of them, so
`2 · #{j | z < v j} < r`; the complement then has more than `r/2` elements. -/
theorem medianSel_isMedian {r : ℕ} (v : Fin r → ℝ) :
    Arlib.GaussianCooling.IsMedian v (medianSel v) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  rw [medianSel, dif_pos hr]
  exact medianSel_aux hr v _ _ fun i => rfl

/-- **The median selector of a measurable family is measurable.**  Assumes each
entry `v j` is measurable; concludes `ω ↦ medianSel (v · ω)` is.

The count in the test is measurable because `∑ⱼ 1[v i ω ≤ v j ω]` is a finite sum
of indicators of the measurable sets `{ω | v i ω ≤ v j ω}`; the outer `sup'`/`inf'`
are `Finset.measurable_sup'` and `Arlib.Probability.measurable_finset_inf'`. -/
theorem measurable_medianSel {r : ℕ} {Ω : Type*} [MeasurableSpace Ω] {v : Fin r → Ω → ℝ}
    (hv : ∀ j, Measurable (v j)) :
    Measurable fun ω => medianSel fun j => v j ω := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have h0 : (fun ω => medianSel fun j => v j ω) = fun _ : Ω => (0 : ℝ) := by
      funext ω; rw [medianSel, dif_neg (by omega)]
    rw [h0]; exact measurable_const
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  have hinf : Measurable fun ω => Finset.univ.inf' hne fun j => v j ω :=
    measurable_finset_inf' hne hv
  have hcond : ∀ i : Fin r,
      MeasurableSet {ω | r ≤ 2 * (Finset.univ.filter fun j => v i ω ≤ v j ω).card} := by
    intro i
    have hsum : Measurable fun ω => ∑ j : Fin r, if v i ω ≤ v j ω then (1 : ℝ) else 0 :=
      Finset.measurable_fun_sum _ fun j _ =>
        Measurable.ite (measurableSet_le (hv i) (hv j)) measurable_const measurable_const
    have hEq : {ω | r ≤ 2 * (Finset.univ.filter fun j => v i ω ≤ v j ω).card}
        = {ω | (r : ℝ) ≤ 2 * ∑ j : Fin r, if v i ω ≤ v j ω then (1 : ℝ) else 0} := by
      ext ω
      simp only [Set.mem_setOf_eq, Finset.sum_boole]
      norm_cast
    rw [hEq]
    exact measurableSet_le measurable_const (hsum.const_mul 2)
  have key : (fun ω => medianSel fun j => v j ω)
      = Finset.univ.sup' hne (fun (i : Fin r) (ω : Ω) =>
          if r ≤ 2 * (Finset.univ.filter fun j => v i ω ≤ v j ω).card then v i ω
          else Finset.univ.inf' hne fun j => v j ω) := by
    funext ω
    rw [medianSel, dif_pos hr, Finset.sup'_apply]
  rw [key]
  exact Finset.measurable_sup' hne fun i _ =>
    Measurable.ite (hcond i) (hv i) hinf

/-! ## Two independence lemmas Mathlib does not seem to have -/

/-- **Independence is transported by a measure-preserving map.**  If `f` is an
independent family on `(Ω', μ')` and `T : Ω → Ω'` pushes `μ` forward to `μ'`,
then `fun i ω => f i (T ω)` is independent on `(Ω, μ)`.

Mathlib has `ProbabilityTheory.iIndepFun.precomp` (reindexing the *family*) and
`ProbabilityTheory.iIndepFun.comp` (postcomposing on the *values*), but no
precomposition on the *sample space*; this is that lemma. -/
theorem iIndepFun_comp_measurePreserving {Ω Ω' ι : Type*} {_ : MeasurableSpace Ω}
    {_ : MeasurableSpace Ω'} {μ : Measure Ω} {μ' : Measure Ω'} {β : ι → Type*}
    {_ : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω' → β i} {T : Ω → Ω'}
    (hT : MeasurePreserving T μ μ') (hf : ∀ i, Measurable (f i))
    (h : iIndepFun f μ') :
    iIndepFun (fun i ω => f i (T ω)) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hs
  have hmeas : ∀ i ∈ S, MeasurableSet (f i ⁻¹' sets i) := fun i hi => hf i (hs i hi)
  have hbi : MeasurableSet (⋂ i ∈ S, f i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet hmeas
  have hpre : (⋂ i ∈ S, (fun ω => f i (T ω)) ⁻¹' sets i)
      = T ⁻¹' ⋂ i ∈ S, f i ⁻¹' sets i := by
    ext ω; simp only [Set.mem_iInter, Set.mem_preimage]
  calc μ (⋂ i ∈ S, (fun ω => f i (T ω)) ⁻¹' sets i)
      = μ (T ⁻¹' ⋂ i ∈ S, f i ⁻¹' sets i) := by rw [hpre]
    _ = μ' (⋂ i ∈ S, f i ⁻¹' sets i) := hT.measure_preimage hbi.nullMeasurableSet
    _ = ∏ i ∈ S, μ' (f i ⁻¹' sets i) := h S hs
    _ = ∏ i ∈ S, μ ((fun ω => f i (T ω)) ⁻¹' sets i) :=
        Finset.prod_congr rfl fun i hi =>
          (hT.measure_preimage (hmeas i hi).nullMeasurableSet).symm

/-- **A family of constants is independent.**  Mathlib has the two-variable
`ProbabilityTheory.indepFun_const_left` / `indepFun_const_right`; this is the
`iIndepFun` version.  Needed because the score family below is defined at *every*
natural index, and is a constant at the out-of-range ones. -/
theorem iIndepFun_const {Ω ι : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {β : ι → Type*} {_ : ∀ i, MeasurableSpace (β i)}
    (c : ∀ i, β i) : iIndepFun (fun i (_ : Ω) => c i) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  by_cases hall : ∀ i ∈ S, c i ∈ sets i
  · have huniv : (⋂ i ∈ S, (fun _ : Ω => c i) ⁻¹' sets i) = Set.univ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]
      exact fun i hi => hall i hi
    have hp : ∀ i ∈ S, μ ((fun _ : Ω => c i) ⁻¹' sets i) = 1 := by
      intro i hi
      have he : ((fun _ : Ω => c i) ⁻¹' sets i) = (Set.univ : Set Ω) := by
        ext ω; simp [hall i hi]
      rw [he, measure_univ]
    rw [huniv, measure_univ, Finset.prod_congr rfl hp, Finset.prod_const_one]
  · obtain ⟨i₀, hi₀S, hi₀⟩ : ∃ i ∈ S, c i ∉ sets i := by
      by_contra hcon
      exact hall fun i hi => not_not.mp fun hni => hcon ⟨i, hi, hni⟩
    have hzero : μ ((fun _ : Ω => c i₀) ⁻¹' sets i₀) = 0 := by
      have he : ((fun _ : Ω => c i₀) ⁻¹' sets i₀) = (∅ : Set Ω) := by
        ext ω; simp [hi₀]
      rw [he, measure_empty]
    have hsub : (⋂ i ∈ S, (fun _ : Ω => c i) ⁻¹' sets i)
        ⊆ (fun _ : Ω => c i₀) ⁻¹' sets i₀ := Set.biInter_subset_of_mem hi₀S
    rw [measure_mono_null hsub hzero, Finset.prod_eq_zero hi₀S hzero]

/-! ## The sample space: one abstract coordinate per (run, phase) -/

variable {r m : ℕ}

/-- **The sample space of `r` runs of `m` phases**: one `E`-valued coordinate per
(run, phase) pair, arranged as a *nested* product `Fin r → (Fin m → E)`.

`E` is an arbitrary measurable space — in the intended application it is the
space of one phase's randomness (a sampler trajectory), not a real number.

Nested rather than flat (`Fin r × Fin m → E`) on purpose: with this arrangement
each *run* is a function of a single outer coordinate, so independence of the
runs — the grouping step, which is what a flat arrangement makes hard — is a
direct application of `ProbabilityTheory.iIndepFun_pi`. -/
abbrev RunSpace (E : Type*) (r m : ℕ) := Fin r → Fin m → E

variable {E : Type*} [MeasurableSpace E]

/-- The product measure on `RunSpace E r m`: run `j`, phase `i` draws from
`ν j i`, all `r · m` draws independent. -/
noncomputable def runMeasure (ν : Fin r → Fin m → Measure E) : Measure (RunSpace E r m) :=
  Measure.pi fun j => Measure.pi fun i => ν j i

/-- `runMeasure` of probability measures is a probability measure. -/
instance isProbabilityMeasure_runMeasure (ν : Fin r → Fin m → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)] : IsProbabilityMeasure (runMeasure ν) := by
  rw [runMeasure]; infer_instance

/-- The coordinate projection is measure preserving onto the corresponding factor. -/
theorem measurePreserving_coord (ν : Fin r → Fin m → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)] (j : Fin r) (i : Fin m) :
    MeasurePreserving (fun ω : RunSpace E r m => ω j i) (runMeasure ν) (ν j i) :=
  (measurePreserving_eval (fun i => ν j i) i).comp
    (measurePreserving_eval (fun j => Measure.pi fun i => ν j i) j)

/-! ## The abstract per-phase score

`score g j i` is the score of run `j`, phase `i`: an arbitrary measurable
function `g j i` of that pair's own coordinate.  It is defined at every pair of
*natural numbers*, taking the value `1` outside the range — the shape the
consumer needs, since its estimator family is indexed by `ℕ`. -/

/-- The score of run `j`, phase `i`: `g j i` applied to the `(j, i)` coordinate,
and `1` at out-of-range indices. -/
noncomputable def score (g : Fin r → Fin m → E → ℝ) (j i : ℕ) (ω : RunSpace E r m) : ℝ :=
  if hj : j < r then if hi : i < m then g ⟨j, hj⟩ ⟨i, hi⟩ (ω ⟨j, hj⟩ ⟨i, hi⟩) else 1 else 1

omit [MeasurableSpace E] in
/-- At in-range indices the score is what it says: `g j i` of the `(j,i)` coordinate. -/
theorem score_coe (g : Fin r → Fin m → E → ℝ) (j : Fin r) (i : Fin m) (ω : RunSpace E r m) :
    score g (j : ℕ) (i : ℕ) ω = g j i (ω j i) := by
  rw [score, dif_pos j.isLt, dif_pos i.isLt]

/-- **`hW_meas`**: every score is measurable, at every pair of natural indices. -/
theorem measurable_score {g : Fin r → Fin m → E → ℝ} (hg : ∀ j i, Measurable (g j i))
    (j i : ℕ) : Measurable (score g j i) := by
  by_cases hj : j < r
  · by_cases hi : i < m
    · have h : score g j i
          = fun ω : RunSpace E r m => g ⟨j, hj⟩ ⟨i, hi⟩ (ω ⟨j, hj⟩ ⟨i, hi⟩) := by
        funext ω; rw [score, dif_pos hj, dif_pos hi]
      rw [h]
      exact (hg _ _).comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
    · have h : score g j i = fun _ : RunSpace E r m => (1 : ℝ) := by
        funext ω; rw [score, dif_pos hj, dif_neg hi]
      rw [h]; exact measurable_const
  · have h : score g j i = fun _ : RunSpace E r m => (1 : ℝ) := by
      funext ω; rw [score, dif_neg hj]
    rw [h]; exact measurable_const

/-- **`hphase_indep`**: for each run index `j`, the `m` phase scores of run `j`
are independent.

Proof: on the factor `Fin m → E` the scores of run `j` are independent by
`ProbabilityTheory.iIndepFun_pi`; the projection `ω ↦ ω j` is measure preserving
onto that factor (`MeasureTheory.measurePreserving_eval`), and
`Arlib.Probability.iIndepFun_comp_measurePreserving` transports independence
along it.  At an out-of-range `j` the family is constant, and
`Arlib.Probability.iIndepFun_const` applies. -/
theorem iIndepFun_score_phases (ν : Fin r → Fin m → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)] {g : Fin r → Fin m → E → ℝ}
    (hg : ∀ j i, Measurable (g j i)) (j : ℕ) :
    iIndepFun (fun i : Fin m => score g j (i : ℕ)) (runMeasure ν) := by
  by_cases hj : j < r
  · have heq : (fun (i : Fin m) => score g j (i : ℕ))
        = fun (i : Fin m) (ω : RunSpace E r m) => g ⟨j, hj⟩ i (ω ⟨j, hj⟩ i) := by
      funext i ω
      rw [score, dif_pos hj, dif_pos i.isLt]
    rw [heq]
    exact iIndepFun_comp_measurePreserving
      (measurePreserving_eval (fun j => Measure.pi fun i => ν j i) ⟨j, hj⟩)
      (fun i => (hg _ i).comp (measurable_pi_apply i))
      (iIndepFun_pi fun i => (hg ⟨j, hj⟩ i).aemeasurable)
  · have heq : (fun (i : Fin m) => score g j (i : ℕ))
        = fun (_ : Fin m) (_ : RunSpace E r m) => (1 : ℝ) := by
      funext i ω; rw [score, dif_neg hj]
    rw [heq]
    exact iIndepFun_const _

/-- **`hindep_runs`**: the `r` runs — each the constant `c` times the product of
its own `m` phase scores — are independent.

This is the **grouping** step, and it is why the sample space is nested: run `j`
is a function of the single outer coordinate `ω j`, so this is
`ProbabilityTheory.iIndepFun_pi` with the whole product over phases absorbed into
the coordinate function.  No block-independence lemma is needed. -/
theorem iIndepFun_runs (ν : Fin r → Fin m → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)] {g : Fin r → Fin m → E → ℝ}
    (hg : ∀ j i, Measurable (g j i)) (c : ℝ) :
    iIndepFun (fun (j : Fin r) (ω : RunSpace E r m) =>
      c * ∏ i : Fin m, score g (j : ℕ) (i : ℕ) ω) (runMeasure ν) := by
  have heq : (fun (j : Fin r) (ω : RunSpace E r m) =>
        c * ∏ i : Fin m, score g (j : ℕ) (i : ℕ) ω)
      = fun (j : Fin r) (ω : RunSpace E r m) => c * ∏ i : Fin m, g j i (ω j i) := by
    funext j ω
    exact congrArg (c * ·) (Finset.prod_congr rfl fun i _ => score_coe g j i ω)
  rw [heq]
  exact iIndepFun_pi (μ := fun j : Fin r => Measure.pi fun i => ν j i)
    (X := fun (j : Fin r) (η : Fin m → E) => c * ∏ i : Fin m, g j i (η i))
    fun j => (measurable_const.mul (Finset.measurable_fun_prod _ fun i _ =>
      (hg j i).comp (measurable_pi_apply i))).aemeasurable

/-- **`hprodLp`**: the product over phases is in `L²`.

The integrability hypothesis is explicit and is a *uniform bound* on the abstract
scores: `|g j i x| ≤ B` with `1 ≤ B` (the `1` also covers the out-of-range value
of `score`).  Then the product is bounded by `B ^ m`, and a bounded measurable
function on a probability space is in every `Lᵖ`. -/
theorem memLp_two_runProd (ν : Fin r → Fin m → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)] {g : Fin r → Fin m → E → ℝ}
    (hg : ∀ j i, Measurable (g j i)) {B : ℝ} (hB : 1 ≤ B)
    (hgb : ∀ j i x, |g j i x| ≤ B) (j : ℕ) :
    MemLp (fun ω => ∏ i : Fin m, score g j (i : ℕ) ω) 2 (runMeasure ν) := by
  have hsb : ∀ (j i : ℕ) (ω : RunSpace E r m), |score g j i ω| ≤ B := by
    intro j i ω
    rw [score]
    split
    · split
      · exact hgb _ _ _
      · rw [abs_one]; exact hB
    · rw [abs_one]; exact hB
  have hmeas : Measurable fun ω : RunSpace E r m => ∏ i : Fin m, score g j (i : ℕ) ω :=
    Finset.measurable_fun_prod _ fun i _ => measurable_score hg j (i : ℕ)
  refine MemLp.of_bound hmeas.aestronglyMeasurable (B ^ m) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc ∏ i : Fin m, |score g j (i : ℕ) ω| ≤ ∏ _i : Fin m, B :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hsb _ _ _
    _ = B ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

omit [MeasurableSpace E] in
/-- **`hmed` and `hmed_meas`**: `medianSel` of the runs is a median of the runs,
and is measurable in `ω`. -/
theorem isMedian_medianSel_runs (g : Fin r → Fin m → E → ℝ) (c : ℝ) (ω : RunSpace E r m) :
    Arlib.GaussianCooling.IsMedian
      (fun j : Fin r => c * ∏ i : Fin m, score g (j : ℕ) (i : ℕ) ω)
      (medianSel fun j : Fin r => c * ∏ i : Fin m, score g (j : ℕ) (i : ℕ) ω) :=
  medianSel_isMedian _

theorem measurable_medianSel_runs {g : Fin r → Fin m → E → ℝ}
    (hg : ∀ j i, Measurable (g j i)) (c : ℝ) :
    Measurable fun ω : RunSpace E r m =>
      medianSel fun j : Fin r => c * ∏ i : Fin m, score g (j : ℕ) (i : ℕ) ω :=
  measurable_medianSel fun j =>
    measurable_const.mul (Finset.measurable_fun_prod _ fun i _ =>
      measurable_score hg (j : ℕ) (i : ℕ))

/-! ## The universal space: countably many runs of countably many phases

`RunSpace E r m` fixes `r` and `m`.  A consumer whose repetition count `r` and
phase count `m` depend on the problem instance needs **one** probability space
serving every `(r, m)` at once, since the estimator interface fixes a single
`Ω` and `μ` up front.  `NatRunSpace E` is that space: one `E`-valued coordinate
per pair of naturals, with `MeasureTheory.Measure.infinitePi` as the product
measure.  `Measure.infinitePi` needs nothing of `E` beyond `MeasurableSpace E`
(it is the Ionescu-Tulcea construction, which is valid for probability measures
on arbitrary measurable spaces).

Everything below is the same mathematics as above, and *strictly more usable*:
`r` and `m` are now arguments of the theorems, not of the space.  Restriction of
an independent `ℕ`-indexed family to `Fin r` is `ProbabilityTheory.iIndepFun.precomp`
along `Fin.val`.  No junk values are needed either, so `natScore` is literally
`g j i` of the `(j, i)` coordinate. -/

/-- Sample space: one `E`-valued coordinate per (run, phase) pair of naturals. -/
abbrev NatRunSpace (E : Type*) := ℕ → ℕ → E

/-- The countable product measure on `NatRunSpace E`. -/
noncomputable def natRunMeasure (ν : ℕ → ℕ → Measure E) : Measure (NatRunSpace E) :=
  Measure.infinitePi fun j => Measure.infinitePi fun i => ν j i

instance isProbabilityMeasure_natRunMeasure (ν : ℕ → ℕ → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)] : IsProbabilityMeasure (natRunMeasure ν) := by
  rw [natRunMeasure]; infer_instance

/-- The score of run `j`, phase `i`: `g j i` of the `(j, i)` coordinate. -/
noncomputable def natScore (g : ℕ → ℕ → E → ℝ) (j i : ℕ) (ω : NatRunSpace E) : ℝ :=
  g j i (ω j i)

/-- **`hW_meas`** on the universal space. -/
theorem measurable_natScore {g : ℕ → ℕ → E → ℝ} (hg : ∀ j i, Measurable (g j i)) (j i : ℕ) :
    Measurable (natScore g j i) :=
  (hg j i).comp ((measurable_pi_apply i).comp (measurable_pi_apply j))

/-- **`hphase_indep`** on the universal space, for *every* phase count `m`.

The `ℕ`-indexed phase family of run `j` is independent by
`ProbabilityTheory.iIndepFun_infinitePi` transported along the measure-preserving
projection `ω ↦ ω j`; restricting to `Fin m` is
`ProbabilityTheory.iIndepFun.precomp` along the injection `Fin.val`. -/
theorem iIndepFun_natScore_phases (ν : ℕ → ℕ → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)] {g : ℕ → ℕ → E → ℝ}
    (hg : ∀ j i, Measurable (g j i)) (j m : ℕ) :
    iIndepFun (fun i : Fin m => natScore g j (i : ℕ)) (natRunMeasure ν) := by
  have hall : iIndepFun (fun (i : ℕ) (ω : NatRunSpace E) => g j i (ω j i)) (natRunMeasure ν) :=
    iIndepFun_comp_measurePreserving (T := fun ω : NatRunSpace E => ω j)
      (f := fun (i : ℕ) (η : ℕ → E) => g j i (η i))
      (measurePreserving_eval_infinitePi (fun j => Measure.infinitePi fun i => ν j i) j)
      (fun i => (hg j i).comp (measurable_pi_apply i))
      (iIndepFun_infinitePi fun i => hg j i)
  exact hall.precomp Fin.val_injective

/-- **`hindep_runs`** on the universal space, for *every* repetition count `r` and
phase count `m`.  Grouping again comes for free: run `j` is a function of the
single outer coordinate `ω j`. -/
theorem iIndepFun_natRuns (ν : ℕ → ℕ → Measure E) [∀ j i, IsProbabilityMeasure (ν j i)]
    {g : ℕ → ℕ → E → ℝ} (hg : ∀ j i, Measurable (g j i)) (c : ℝ) (r m : ℕ) :
    iIndepFun (fun (j : Fin r) (ω : NatRunSpace E) =>
      c * ∏ i : Fin m, natScore g (j : ℕ) (i : ℕ) ω) (natRunMeasure ν) := by
  have hall : iIndepFun (fun (j : ℕ) (ω : NatRunSpace E) =>
      c * ∏ i : Fin m, natScore g j (i : ℕ) ω) (natRunMeasure ν) :=
    iIndepFun_infinitePi
      (X := fun (j : ℕ) (η : ℕ → E) => c * ∏ i : Fin m, g j (i : ℕ) (η (i : ℕ)))
      fun j => measurable_const.mul (Finset.measurable_fun_prod _ fun i _ =>
        (hg j (i : ℕ)).comp (measurable_pi_apply (i : ℕ)))
  exact hall.precomp Fin.val_injective

/-- **`hprodLp`** on the universal space.  Explicit hypothesis: a uniform bound
`|g j i x| ≤ B` on the abstract scores. -/
theorem memLp_two_natRunProd (ν : ℕ → ℕ → Measure E) [∀ j i, IsProbabilityMeasure (ν j i)]
    {g : ℕ → ℕ → E → ℝ} (hg : ∀ j i, Measurable (g j i)) {B : ℝ}
    (hgb : ∀ j i x, |g j i x| ≤ B) (j m : ℕ) :
    MemLp (fun ω => ∏ i : Fin m, natScore g j (i : ℕ) ω) 2 (natRunMeasure ν) := by
  have hmeas : Measurable fun ω : NatRunSpace E => ∏ i : Fin m, natScore g j (i : ℕ) ω :=
    Finset.measurable_fun_prod _ fun i _ => measurable_natScore hg j (i : ℕ)
  refine MemLp.of_bound hmeas.aestronglyMeasurable (B ^ m) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc ∏ i : Fin m, |natScore g j (i : ℕ) ω| ≤ ∏ _i : Fin m, B :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hgb _ _ _
    _ = B ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

omit [MeasurableSpace E] in
/-- **`hmed`** on the universal space. -/
theorem isMedian_medianSel_natRuns (g : ℕ → ℕ → E → ℝ) (c : ℝ) (r m : ℕ)
    (ω : NatRunSpace E) :
    Arlib.GaussianCooling.IsMedian
      (fun j : Fin r => c * ∏ i : Fin m, natScore g (j : ℕ) (i : ℕ) ω)
      (medianSel fun j : Fin r => c * ∏ i : Fin m, natScore g (j : ℕ) (i : ℕ) ω) :=
  medianSel_isMedian _

/-- **`hmed_meas`** on the universal space. -/
theorem measurable_medianSel_natRuns {g : ℕ → ℕ → E → ℝ} (hg : ∀ j i, Measurable (g j i))
    (c : ℝ) (r m : ℕ) :
    Measurable fun ω : NatRunSpace E =>
      medianSel fun j : Fin r => c * ∏ i : Fin m, natScore g (j : ℕ) (i : ℕ) ω :=
  measurable_medianSel fun j =>
    measurable_const.mul (Finset.measurable_fun_prod _ fun i _ =>
      measurable_natScore hg (j : ℕ) (i : ℕ))

/-- The coordinate projection of the universal space is measure preserving. -/
theorem measurePreserving_natCoord (ν : ℕ → ℕ → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)] (j i : ℕ) :
    MeasurePreserving (fun ω : NatRunSpace E => ω j i) (natRunMeasure ν) (ν j i) :=
  (measurePreserving_eval_infinitePi (fun i => ν j i) i).comp
    (measurePreserving_eval_infinitePi (fun j => Measure.infinitePi fun i => ν j i) j)

/-! ## Non-vacuity: a genuinely random instance

`CLAUDE.md` §11 asks for a witness that is not degenerate.  A one-point sample
space satisfies every independence statement above *vacuously*; the instance
below does not.  It uses `r = 2` runs, `m = 2` phases, and a fair coin per
coordinate, and `Arlib.Probability.not_ae_const_score` proves that no score is
almost-everywhere constant — so the independence assertions have content. -/

/-- **The fair coin on `{0, 1} ⊆ ℝ`**: `½·δ₀ + ½·δ₁`. -/
noncomputable def coin : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1)

/-- The mass the coin assigns to a measurable set: half the number of atoms in it. -/
theorem coin_apply {s : Set ℝ} (hs : MeasurableSet s) :
    coin s = 2⁻¹ * (s.indicator 1 (0 : ℝ) + s.indicator 1 (1 : ℝ)) := by
  rw [coin, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ hs, smul_eq_mul]

/-- The coin is a probability measure. -/
instance isProbabilityMeasure_coin : IsProbabilityMeasure coin := by
  constructor
  rw [coin_apply MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- **The coin is spread out**: any measurable set missing one of the two atoms
has mass at most `½`, hence strictly less than `1`. -/
theorem coin_le_half {s : Set ℝ} (hs : MeasurableSet s)
    (h : ¬((0 : ℝ) ∈ s ∧ (1 : ℝ) ∈ s)) : coin s ≤ 2⁻¹ := by
  rw [coin_apply hs]
  have hsum : (s.indicator 1 (0 : ℝ) + s.indicator 1 (1 : ℝ) : ℝ≥0∞) ≤ 1 := by
    by_cases h0 : (0 : ℝ) ∈ s
    · have h1 : (1 : ℝ) ∉ s := fun hc => h ⟨h0, hc⟩
      rw [Set.indicator_of_mem h0, Set.indicator_of_notMem h1]
      simp
    · rw [Set.indicator_of_notMem h0]
      by_cases h1 : (1 : ℝ) ∈ s
      · rw [Set.indicator_of_mem h1]; simp
      · rw [Set.indicator_of_notMem h1]; simp
  calc (2 : ℝ≥0∞)⁻¹ * (s.indicator 1 (0 : ℝ) + s.indicator 1 (1 : ℝ))
      ≤ 2⁻¹ * 1 := mul_le_mul_right hsum _
    _ = 2⁻¹ := mul_one _

theorem coin_lt_one {s : Set ℝ} (hs : MeasurableSet s)
    (h : ¬((0 : ℝ) ∈ s ∧ (1 : ℝ) ∈ s)) : coin s < 1 :=
  lt_of_le_of_lt (coin_le_half hs h) (ENNReal.inv_lt_one.mpr (by norm_num))

/-- **The engine of non-degeneracy.**  If a random variable is a measurable
function `f` of a coordinate whose law is the fair coin, and `f` separates the
two atoms (`f 0 ≠ f 1`), then it is *not* almost-everywhere constant — for any
candidate constant `c`.

This is what rules out the degenerate witness: on a subsingleton sample space
every random variable is a.e. constant, and every independence statement is
vacuous.  Here none is. -/
theorem not_ae_const_of_coin_coord {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {T : Ω → ℝ} (hT : MeasurePreserving T μ coin)
    {f : ℝ → ℝ} (hf : Measurable f) (hfne : f 0 ≠ f 1) (c : ℝ) :
    ¬ (fun ω => f (T ω)) =ᵐ[μ] (fun _ => c) := by
  intro hc
  have hmeasS : MeasurableSet (f ⁻¹' {c}) := hf (measurableSet_singleton c)
  have hms : MeasurableSet {ω | f (T ω) = c} :=
    (hf.comp hT.measurable) (measurableSet_singleton c)
  have h0 : μ {ω | f (T ω) = c}ᶜ = 0 := MeasureTheory.ae_iff.mp hc
  rw [measure_compl hms (measure_ne_top _ _), measure_univ] at h0
  have hfull : μ {ω | f (T ω) = c} = 1 :=
    le_antisymm prob_le_one (tsub_eq_zero_iff_le.mp h0)
  have hset : {ω | f (T ω) = c} = T ⁻¹' (f ⁻¹' {c}) := rfl
  have hnot : ¬((0 : ℝ) ∈ f ⁻¹' {c} ∧ (1 : ℝ) ∈ f ⁻¹' {c}) := by
    rintro ⟨h0', h1'⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at h0' h1'
    exact hfne (h0'.trans h1'.symm)
  rw [hset, hT.measure_preimage hmeasS.nullMeasurableSet] at hfull
  exact absurd hfull (ne_of_lt (coin_lt_one hmeasS hnot))

/-- **The finite-space witness is not degenerate**: on the coin product space no
score with `g j i 0 ≠ g j i 1` is almost-everywhere constant. -/
theorem not_ae_const_score {r m : ℕ} {g : Fin r → Fin m → ℝ → ℝ}
    (hg : ∀ j i, Measurable (g j i)) (j : Fin r) (i : Fin m)
    (hgne : g j i 0 ≠ g j i 1) (c : ℝ) :
    ¬ (score g (j : ℕ) (i : ℕ)) =ᵐ[runMeasure fun _ _ => coin] (fun _ => c) := by
  have h : (score g (j : ℕ) (i : ℕ)) = fun ω : RunSpace ℝ r m => g j i (ω j i) :=
    funext fun ω => score_coe g j i ω
  rw [h]
  exact not_ae_const_of_coin_coord (measurePreserving_coord _ j i) (hg j i) hgne c

/-- **The universal-space witness is not degenerate**: same statement on
`NatRunSpace`, for every pair of natural indices. -/
theorem not_ae_const_natScore {g : ℕ → ℕ → ℝ → ℝ} (hg : ∀ j i, Measurable (g j i))
    (j i : ℕ) (hgne : g j i 0 ≠ g j i 1) (c : ℝ) :
    ¬ (natScore g j i) =ᵐ[natRunMeasure fun _ _ => coin] (fun _ => c) :=
  not_ae_const_of_coin_coord (measurePreserving_natCoord _ j i) (hg j i) hgne c

/-! ### The concrete `r = 2`, `m = 2`, fair-coin instance -/

/-- The clamp `x ↦ max 0 (min 1 x)`: bounded by `1`, measurable, and separating
the two coin atoms (`0 ↦ 0`, `1 ↦ 1`). -/
noncomputable def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

theorem measurable_clamp01 : Measurable clamp01 :=
  measurable_const.max (measurable_const.min measurable_id)

theorem abs_clamp01_le_one (x : ℝ) : |clamp01 x| ≤ 1 :=
  abs_le.mpr ⟨le_trans (by norm_num) (le_max_left _ _),
    max_le zero_le_one (min_le_left _ _)⟩

theorem clamp01_zero : clamp01 0 = 0 := by norm_num [clamp01]

theorem clamp01_one : clamp01 1 = 1 := by norm_num [clamp01]

/-- The witness score family: `2` runs, `2` phases, every score the clamp of its
own fair coin. -/
noncomputable def witG : Fin 2 → Fin 2 → ℝ → ℝ := fun _ _ => clamp01

/-- The witness sample space measure: four independent fair coins. -/
noncomputable def witMeasure : Measure (RunSpace ℝ 2 2) := runMeasure fun _ _ => coin

instance isProbabilityMeasure_witMeasure : IsProbabilityMeasure witMeasure := by
  rw [witMeasure]; infer_instance

/-- `hW_meas` for the witness. -/
theorem wit_measurable_score (j i : ℕ) : Measurable (score witG j i) :=
  measurable_score (fun _ _ => measurable_clamp01) j i

/-- `hphase_indep` for the witness — non-vacuously, see `wit_not_ae_const`. -/
theorem wit_phase_indep (j : ℕ) :
    iIndepFun (fun i : Fin 2 => score witG j (i : ℕ)) witMeasure :=
  iIndepFun_score_phases _ (fun _ _ => measurable_clamp01) j

/-- `hindep_runs` for the witness. -/
theorem wit_runs_indep (c : ℝ) :
    iIndepFun (fun (j : Fin 2) (ω : RunSpace ℝ 2 2) =>
      c * ∏ i : Fin 2, score witG (j : ℕ) (i : ℕ) ω) witMeasure :=
  iIndepFun_runs _ (fun _ _ => measurable_clamp01) c

/-- `hprodLp` for the witness: the clamp is bounded by `1`. -/
theorem wit_memLp (j : ℕ) :
    MemLp (fun ω => ∏ i : Fin 2, score witG j (i : ℕ) ω) 2 witMeasure :=
  memLp_two_runProd _ (fun _ _ => measurable_clamp01) le_rfl
    (fun _ _ x => abs_clamp01_le_one x) j

/-- `hmed` for the witness. -/
theorem wit_isMedian (c : ℝ) (ω : RunSpace ℝ 2 2) :
    Arlib.GaussianCooling.IsMedian
      (fun j : Fin 2 => c * ∏ i : Fin 2, score witG (j : ℕ) (i : ℕ) ω)
      (medianSel fun j : Fin 2 => c * ∏ i : Fin 2, score witG (j : ℕ) (i : ℕ) ω) :=
  medianSel_isMedian _

/-- `hmed_meas` for the witness. -/
theorem wit_measurable_medianSel (c : ℝ) :
    Measurable fun ω : RunSpace ℝ 2 2 =>
      medianSel fun j : Fin 2 => c * ∏ i : Fin 2, score witG (j : ℕ) (i : ℕ) ω :=
  measurable_medianSel_runs (fun _ _ => measurable_clamp01) c

/-- **The witness is genuinely random**: every one of the four scores fails to be
almost-everywhere constant.  Contrast the degenerate `Unit`-space witness, where
independence holds because the space is a subsingleton. -/
theorem wit_not_ae_const (j i : Fin 2) (c : ℝ) :
    ¬ (score witG (j : ℕ) (i : ℕ)) =ᵐ[witMeasure] (fun _ => c) := by
  rw [witMeasure]
  refine not_ae_const_score (fun _ _ => measurable_clamp01) j i ?_ c
  show clamp01 0 ≠ clamp01 1
  rw [clamp01_zero, clamp01_one]
  norm_num

/-! ### The universal-space witness

`NatRunSpace` with a fair coin per coordinate and the clamp as the score.  This
is the instance a consumer whose `r` and `m` vary with the problem instance
should use: one space, every `(r, m)`. -/

/-- The universal-space witness score family. -/
noncomputable def natWitG : ℕ → ℕ → ℝ → ℝ := fun _ _ => clamp01

/-- The universal-space witness measure: countably many independent fair coins. -/
noncomputable def natWitMeasure : Measure (NatRunSpace ℝ) := natRunMeasure fun _ _ => coin

instance isProbabilityMeasure_natWitMeasure : IsProbabilityMeasure natWitMeasure := by
  rw [natWitMeasure]; infer_instance

/-- `hW_meas` for the universal witness. -/
theorem natWit_measurable_score (j i : ℕ) : Measurable (natScore natWitG j i) :=
  measurable_natScore (fun _ _ => measurable_clamp01) j i

/-- `hphase_indep` for the universal witness, at every phase count. -/
theorem natWit_phase_indep (j m : ℕ) :
    iIndepFun (fun i : Fin m => natScore natWitG j (i : ℕ)) natWitMeasure :=
  iIndepFun_natScore_phases _ (fun _ _ => measurable_clamp01) j m

/-- `hindep_runs` for the universal witness, at every repetition and phase count. -/
theorem natWit_runs_indep (c : ℝ) (r m : ℕ) :
    iIndepFun (fun (j : Fin r) (ω : NatRunSpace ℝ) =>
      c * ∏ i : Fin m, natScore natWitG (j : ℕ) (i : ℕ) ω) natWitMeasure :=
  iIndepFun_natRuns _ (fun _ _ => measurable_clamp01) c r m

/-- `hprodLp` for the universal witness. -/
theorem natWit_memLp (j m : ℕ) :
    MemLp (fun ω => ∏ i : Fin m, natScore natWitG j (i : ℕ) ω) 2 natWitMeasure :=
  memLp_two_natRunProd _ (fun _ _ => measurable_clamp01)
    (fun _ _ x => abs_clamp01_le_one x) j m

/-- `hmed` for the universal witness. -/
theorem natWit_isMedian (c : ℝ) (r m : ℕ) (ω : NatRunSpace ℝ) :
    Arlib.GaussianCooling.IsMedian
      (fun j : Fin r => c * ∏ i : Fin m, natScore natWitG (j : ℕ) (i : ℕ) ω)
      (medianSel fun j : Fin r => c * ∏ i : Fin m, natScore natWitG (j : ℕ) (i : ℕ) ω) :=
  medianSel_isMedian _

/-- `hmed_meas` for the universal witness. -/
theorem natWit_measurable_medianSel (c : ℝ) (r m : ℕ) :
    Measurable fun ω : NatRunSpace ℝ =>
      medianSel fun j : Fin r => c * ∏ i : Fin m, natScore natWitG (j : ℕ) (i : ℕ) ω :=
  measurable_medianSel_natRuns (fun _ _ => measurable_clamp01) c r m

/-- **The universal witness is genuinely random**: no score is a.e. constant. -/
theorem natWit_not_ae_const (j i : ℕ) (c : ℝ) :
    ¬ (natScore natWitG j i) =ᵐ[natWitMeasure] (fun _ => c) := by
  rw [natWitMeasure]
  refine not_ae_const_natScore (fun _ _ => measurable_clamp01) j i ?_ c
  show clamp01 0 ≠ clamp01 1
  rw [clamp01_zero, clamp01_one]
  norm_num


/-! ### A witness whose coordinate space is *not* `ℝ`

The two witnesses above both take `E := ℝ`, so on their own they do not show that
the generality in `E` is usable.  This one takes `E := Traj = ℕ → ℝ`, the space of
a whole *trajectory* — the shape a sampler's per-phase randomness actually has —
and re-derives all six plumbing facts plus non-degeneracy.

The point of the section is negative: **nothing** had to be assumed about `Traj`
beyond its `MeasurableSpace` instance.  In particular the trajectory measure
`trajMeasure` is itself an `Measure.infinitePi`, so `trajWitMeasure` is a
product of products of products, and every lemma above still applies verbatim. -/

/-- A **trajectory**: one phase's randomness is an infinite sequence of reals, not
a single real.  Deliberately not `ℝ`, and deliberately not a standard Borel space
by assumption — only `MeasurableSpace` is used. -/
abbrev Traj : Type := ℕ → ℝ

/-- A trajectory of independent fair coins. -/
noncomputable def trajMeasure : Measure Traj := Measure.infinitePi fun _ => coin

instance isProbabilityMeasure_trajMeasure : IsProbabilityMeasure trajMeasure := by
  rw [trajMeasure]; infer_instance

/-- The trajectory score: clamp the trajectory's first step. -/
noncomputable def trajG : ℕ → ℕ → Traj → ℝ := fun _ _ η => clamp01 (η 0)

theorem measurable_trajG (j i : ℕ) : Measurable (trajG j i) :=
  measurable_clamp01.comp (measurable_pi_apply 0)

theorem abs_trajG_le_one (j i : ℕ) (η : Traj) : |trajG j i η| ≤ 1 :=
  abs_clamp01_le_one _

/-- The universal run space over **trajectory** coordinates. -/
noncomputable def trajWitMeasure : Measure (NatRunSpace Traj) :=
  natRunMeasure fun _ _ => trajMeasure

instance isProbabilityMeasure_trajWitMeasure : IsProbabilityMeasure trajWitMeasure := by
  rw [trajWitMeasure]; infer_instance

/-- `hW_meas` over trajectory coordinates. -/
theorem trajWit_measurable_score (j i : ℕ) : Measurable (natScore trajG j i) :=
  measurable_natScore measurable_trajG j i

/-- `hphase_indep` over trajectory coordinates, at every phase count. -/
theorem trajWit_phase_indep (j m : ℕ) :
    iIndepFun (fun i : Fin m => natScore trajG j (i : ℕ)) trajWitMeasure :=
  iIndepFun_natScore_phases _ measurable_trajG j m

/-- `hindep_runs` over trajectory coordinates, at every repetition and phase count. -/
theorem trajWit_runs_indep (c : ℝ) (r m : ℕ) :
    iIndepFun (fun (j : Fin r) (ω : NatRunSpace Traj) =>
      c * ∏ i : Fin m, natScore trajG (j : ℕ) (i : ℕ) ω) trajWitMeasure :=
  iIndepFun_natRuns _ measurable_trajG c r m

/-- `hprodLp` over trajectory coordinates. -/
theorem trajWit_memLp (j m : ℕ) :
    MemLp (fun ω => ∏ i : Fin m, natScore trajG j (i : ℕ) ω) 2 trajWitMeasure :=
  memLp_two_natRunProd _ measurable_trajG (fun j i η => abs_trajG_le_one j i η) j m

/-- `hmed` over trajectory coordinates. -/
theorem trajWit_isMedian (c : ℝ) (r m : ℕ) (ω : NatRunSpace Traj) :
    Arlib.GaussianCooling.IsMedian
      (fun j : Fin r => c * ∏ i : Fin m, natScore trajG (j : ℕ) (i : ℕ) ω)
      (medianSel fun j : Fin r => c * ∏ i : Fin m, natScore trajG (j : ℕ) (i : ℕ) ω) :=
  medianSel_isMedian _

/-- `hmed_meas` over trajectory coordinates. -/
theorem trajWit_measurable_medianSel (c : ℝ) (r m : ℕ) :
    Measurable fun ω : NatRunSpace Traj =>
      medianSel fun j : Fin r => c * ∏ i : Fin m, natScore trajG (j : ℕ) (i : ℕ) ω :=
  measurable_medianSel_natRuns measurable_trajG c r m

/-- The first step of the `(j, i)` trajectory is a fair coin: the composite of the
`(j, i)` coordinate projection of `trajWitMeasure` with the `0`th coordinate
projection of `trajMeasure`. -/
theorem measurePreserving_trajStep (j i : ℕ) :
    MeasurePreserving (fun ω : NatRunSpace Traj => ω j i 0) trajWitMeasure coin := by
  rw [trajWitMeasure]
  exact (measurePreserving_eval_infinitePi (fun _ => coin) 0).comp
    (measurePreserving_natCoord (fun _ _ => trajMeasure) j i)

/-- **The trajectory witness is genuinely random**: no score is a.e. constant.
Non-vacuity at a coordinate space that is not `ℝ`. -/
theorem trajWit_not_ae_const (j i : ℕ) (c : ℝ) :
    ¬ (natScore trajG j i) =ᵐ[trajWitMeasure] (fun _ => c) := by
  have h : natScore trajG j i = fun ω : NatRunSpace Traj => clamp01 (ω j i 0) := rfl
  rw [h]
  refine not_ae_const_of_coin_coord (measurePreserving_trajStep j i) measurable_clamp01 ?_ c
  rw [clamp01_zero, clamp01_one]
  norm_num

/-! ## Axiom audit

Every declaration in this file, checked against Mathlib's three foundational
axioms.  Anything else in the output (in particular `sorryAx`) means a hole. -/

#print axioms Arlib.Probability.measurable_finset_inf'
#print axioms Arlib.Probability.medianSel
#print axioms Arlib.Probability.medianSel_aux
#print axioms Arlib.Probability.medianSel_isMedian
#print axioms Arlib.Probability.measurable_medianSel
#print axioms Arlib.Probability.iIndepFun_comp_measurePreserving
#print axioms Arlib.Probability.iIndepFun_const
#print axioms Arlib.Probability.RunSpace
#print axioms Arlib.Probability.runMeasure
#print axioms Arlib.Probability.isProbabilityMeasure_runMeasure
#print axioms Arlib.Probability.measurePreserving_coord
#print axioms Arlib.Probability.score
#print axioms Arlib.Probability.score_coe
#print axioms Arlib.Probability.measurable_score
#print axioms Arlib.Probability.iIndepFun_score_phases
#print axioms Arlib.Probability.iIndepFun_runs
#print axioms Arlib.Probability.memLp_two_runProd
#print axioms Arlib.Probability.isMedian_medianSel_runs
#print axioms Arlib.Probability.measurable_medianSel_runs
#print axioms Arlib.Probability.coin
#print axioms Arlib.Probability.coin_apply
#print axioms Arlib.Probability.isProbabilityMeasure_coin
#print axioms Arlib.Probability.coin_le_half
#print axioms Arlib.Probability.coin_lt_one
#print axioms Arlib.Probability.not_ae_const_score
#print axioms Arlib.Probability.clamp01
#print axioms Arlib.Probability.measurable_clamp01
#print axioms Arlib.Probability.abs_clamp01_le_one
#print axioms Arlib.Probability.clamp01_zero
#print axioms Arlib.Probability.clamp01_one
#print axioms Arlib.Probability.witG
#print axioms Arlib.Probability.witMeasure
#print axioms Arlib.Probability.isProbabilityMeasure_witMeasure
#print axioms Arlib.Probability.wit_measurable_score
#print axioms Arlib.Probability.wit_phase_indep
#print axioms Arlib.Probability.wit_runs_indep
#print axioms Arlib.Probability.wit_memLp
#print axioms Arlib.Probability.wit_isMedian
#print axioms Arlib.Probability.wit_measurable_medianSel
#print axioms Arlib.Probability.wit_not_ae_const
#print axioms Arlib.Probability.NatRunSpace
#print axioms Arlib.Probability.natRunMeasure
#print axioms Arlib.Probability.isProbabilityMeasure_natRunMeasure
#print axioms Arlib.Probability.natScore
#print axioms Arlib.Probability.measurable_natScore
#print axioms Arlib.Probability.iIndepFun_natScore_phases
#print axioms Arlib.Probability.iIndepFun_natRuns
#print axioms Arlib.Probability.memLp_two_natRunProd
#print axioms Arlib.Probability.isMedian_medianSel_natRuns
#print axioms Arlib.Probability.measurable_medianSel_natRuns
#print axioms Arlib.Probability.measurePreserving_natCoord
#print axioms Arlib.Probability.not_ae_const_of_coin_coord
#print axioms Arlib.Probability.not_ae_const_natScore
#print axioms Arlib.Probability.natWitG
#print axioms Arlib.Probability.natWitMeasure
#print axioms Arlib.Probability.isProbabilityMeasure_natWitMeasure
#print axioms Arlib.Probability.natWit_measurable_score
#print axioms Arlib.Probability.natWit_phase_indep
#print axioms Arlib.Probability.natWit_runs_indep
#print axioms Arlib.Probability.natWit_memLp
#print axioms Arlib.Probability.natWit_isMedian
#print axioms Arlib.Probability.natWit_measurable_medianSel
#print axioms Arlib.Probability.natWit_not_ae_const
#print axioms Arlib.Probability.Traj
#print axioms Arlib.Probability.trajMeasure
#print axioms Arlib.Probability.isProbabilityMeasure_trajMeasure
#print axioms Arlib.Probability.trajG
#print axioms Arlib.Probability.measurable_trajG
#print axioms Arlib.Probability.abs_trajG_le_one
#print axioms Arlib.Probability.trajWitMeasure
#print axioms Arlib.Probability.isProbabilityMeasure_trajWitMeasure
#print axioms Arlib.Probability.trajWit_measurable_score
#print axioms Arlib.Probability.trajWit_phase_indep
#print axioms Arlib.Probability.trajWit_runs_indep
#print axioms Arlib.Probability.trajWit_memLp
#print axioms Arlib.Probability.trajWit_isMedian
#print axioms Arlib.Probability.trajWit_measurable_medianSel
#print axioms Arlib.Probability.measurePreserving_trajStep
#print axioms Arlib.Probability.trajWit_not_ae_const

end Arlib.Probability
