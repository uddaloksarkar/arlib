/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.HitAndRunLem41Discharge

/-!
# The `hLem41` binder of Theorem 1.1: decomposition, and exactly where it stops

The binder in question is the one at
`Arlib/MarkovChains/Continuous/HitAndRunMixing.lean:961`, inside
`Arlib.MarkovChains.tvLe_iterate_hitAndRun_unitBall`:

    hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500))

**This file does not discharge it, and states why.**  The verdict, split by strength of
evidence:

* **Machine-checked** (`lemma41_route_gt_one_sub_inv_five_hundred`): for every `n ≥ 1` and
  every cap bound `q₂ ≥ 9/25`, the constant that the source's proof produces is *strictly
  weaker* than `1 − 1/500`.  Since `9/25` is the only cap bound this repository proves
  (`Arlib.MarkovChains.unifSphere_cap_le`, `n ≥ 1100`), the route is **not instantiable here**
  at the binder's constant, at any dimension.
* **Arithmetic in prose, not formalised** (Finding 2 below, and the table in
  `HitAndRunOverlap.lean`'s module docstring): even at the *sharp* cap constant
  `q₂ → 2(1 − Φ(1)) = 0.31731…` — which is below `9/25` from about `n = 8` on, so the Lean
  lemma does not cover it — the route still tops out at `1 − 1/1892.8…` as `n → ∞` and is
  vacuous for `2 ≤ n ≤ 4`.  So the route fails for every `n ≥ 2`; only `n = 1` reaches
  `1 − 1/500`.

What *is* attainable, and already proved elsewhere in this repository, is `1 − 1/8000` for
interior pairs at `n ≥ 1100` (`Arlib.MarkovChains.hLem41_interior_uncond`), which is a
**weaker** total-variation bound and therefore cannot be converted
(`ofReal_one_sub_lt_ofReal_one_sub`).

## Sources

* **Statement.** L. Lovász, S. Vempala, *Hit-and-Run from a Corner*, 7 August 2005
  (`LV07.pdf` in the repository root; identical to
  `https://faculty.cc.gatech.edu/~vempala/papers/start.pdf`).  §4, verbatim:

  > **Lemma 4.1** [9] Let `u, v ∈ K`.  Suppose that `d_K(u,v) < 1/8` and
  > `|u − v| < (2/√n) max{F(u), F(v)}`.  Then `d_tv(P_u, P_v) < 1 − 1/500`.

  The paper gives **no proof**; `[9]` is Lovász 1999.

* **Proof.** L. Lovász, *Hit-and-run mixes fast*, Math. Program. Ser. A **86** (1999) 443–461,
  **Lemma 8** (p. 451–453), read from the author's PDF at
  `https://faculty.washington.edu/harin/L1.pdf`.  Its hypothesis is the *asymmetric*
  `|u − v| < (2/√n) F(u)`; the `max` of Lemma 4.1 comes from the symmetry of `d_tv`
  (`tvLe_hitAndRun_binder_of_asymm` below, and
  `Arlib.MarkovChains.tvLe_hitAndRun_lemma41_uncond_max`).  The budget is
  `P_u(A₁) ≤ 1/8`, `P_u(A₂) ≤ 1/6`, `P_u(A₃) ≤ 1/3`, summed to `< 3/4`, against the overlap
  factor `1/(2e⁴) > 1/120`, giving `1 − (1 − 3/4)/120 = 1 − 1/480 ≤ 1 − 1/500`.

  The **cap step** the task asks about is the `1/6`, verbatim:

  > To estimate the probability that `x ∈ A₂`, let `C` be the cap on the unit sphere defined
  > by `(u−v)ᵀ x ≥ (1/√n)|u−v|`.  … The probability that this happens is the ratio between the
  > surface of `C` and the surface of the half sphere.  It takes a standard computation to show
  > that this ratio is less than `1/6`.

  With the corrected `A₃` (below) the budget closes iff that ratio, written `q₂`, is `< 3/8`.

## Survey: what already exists

Lemma 4.1 is essentially fully formalised in this repository, and the present file adds only
the parts about the *binder* that were missing.

| file:line | content |
|---|---|
| `Arlib/MarkovChains/Continuous/HitAndRunOverlap.lean:583` | `tvLe_hitAndRun_lemma41` — Lovász's proof, parametric in the cap bound `q₂`, concluding `1 − (1 − (1/8 + q₂ + 1/2))/(2(1+4/n)ⁿ)` |
| `…HitAndRunOverlap.lean:716` | `tvLe_hitAndRun_lemma41_of_le_three_eighths` — the same rounded to `1 − (3/8 − q₂)/120` |
| `…HitAndRunOverlap.lean:751` | `tvLe_hitAndRun_lemma41_unconditional` — no unproved hypothesis; non-trivial only at `n = 1` |
| `Arlib/MarkovChains/Continuous/SphereCap.lean` | the cap estimate `σ ≤ 9/25` for `n ≥ 1100`, and `tvLe_hitAndRun_lemma41_uncond` at `1 − 1/8000` |
| `Arlib/MarkovChains/Continuous/HitAndRunUncond.lean:409` | `tvLe_hitAndRun_lemma41_uncond_max` — the same in the binder's `max` shape |
| `Arlib/MarkovChains/Continuous/HitAndRunLem41Discharge.lean` | `hLem41_interior_uncond` — the binder over `interior K`, at `1 − 1/8000`, `n ≥ 1100`, no unproved hypothesis |
| `Arlib/MarkovChains/Continuous/HitAndRunLem41Discharge.lean` | `chordLow_eq_zero_of_notMem_interior` — the boundary obstruction |
| `Arlib/Convexity/ChordCompare.lean` | the chord comparison, its `Λ = 2` form, and the counterexample to the printed one-sided `A₃` |
| `Arlib/Convexity/HitAndRunStep.lean:530` | `medianStep`, the lower `1/8`-quantile standing for the paper's `F` |
| `Arlib/MarkovChains/Continuous/HitAndRun.lean:416` | `hitAndRun = hitAndRunProposal + (1 − mass)·δ_u` |
| `Arlib/Convexity/CrossRatio.lean:344` | `crossRatioDist`, with junk value `0` where the true `d_K` is `+∞` |

So: **no part of Lemma 4.1 needed to be re-proved.**  What was missing is (i) an account of
the binder's constant, (ii) the reduction of the `∀ u v ∈ K` binder to a smaller residual, and
(iii) the observation that the binder is strictly stronger than the printed lemma.

## Three findings

**1.  The binder is strictly stronger than Lemma 4.1 as printed.**
In the paper `d_K(u,v) = +∞` whenever `u` or `v` is an endpoint of the chord through them, so
the hypothesis `d_K(u,v) < 1/8` *excludes* every boundary–interior pair.  `crossRatioDist` is a
quotient and Lean's `x / 0 = 0`, so at exactly those pairs the formalised hypothesis is
satisfied by the junk value `0` (`crossRatioDist_eq_zero_of_notMem_interior`,
`crossRatioDist_lt_of_notMem_interior` below, on top of
`Arlib.MarkovChains.chordLow_eq_zero_of_notMem_interior`).  The binder therefore demands a
total-variation bound at pairs about which the source says nothing.  Consumers that only need
interior pairs — which is what `HitAndRunConductance.lean` in fact uses — should take
`Arlib.MarkovChains.conductance_hitAndRun_ge_of_tv_interior` instead.

**2.  `1 − 1/500` is not attainable by the source's proof, and this is checked.**
`lemma41_route_gt_one_sub_inv_five_hundred` proves, for every `n ≥ 1` and every `q₂ ≥ 9/25`
(the rest of this finding — the sharp `q₂`, the table, the `Λ`-sweep — is arithmetic in prose,
not formalised),

    1 − 1/500  <  1 − (1 − (1/8 + q₂ + 1/2)) / (2(1 + 4/n)ⁿ),

the right-hand side being exactly the conclusion of
`Arlib.MarkovChains.tvLe_hitAndRun_lemma41`.  Two of the paper's three bounds are wrong in the
same direction:

* the cap bound `1/6` is off by the sphere/half-sphere factor — the true `q₂` is `1/2` at
  `n = 2`, `0.4226…` at `n = 3`, decreasing to `2(1 − Φ(1)) = 0.31731…`, and never `≤ 1/6`;
  `SphereCap.lean` proves `q₂ ≤ 9/25 = 0.36` for `n ≥ 1100`;
* the mass `1/3` is for the *one-sided* `A₃ = {x : |x−u| < (1/3)|u − a(u,x)|}`, but the proof's
  step "*Similarly, |v − s| < 2|x−v||x−u|/|u−q|*" needs the bound at the **other** chord
  endpoint too; `ChordCompare.lean` exhibits an explicit `n = 2` body where every other
  hypothesis holds and the chord comparison fails (`101.0` against `35.06`).  The two-sided
  `A₃` has sharp mass `1/2`, attained on a chord split by `u` in ratio `1 : 3`.

With `q = 1/8 + q₂ + 1/2` and the sharp overlap factor `1/(2e⁴)`, the best the route yields is
`1 − 1/1892.8…` as `n → ∞` and nothing at all for `2 ≤ n ≤ 4`.  Retuning the chord-comparison
factor `Λ` does not rescue it: with `ChordCompare.lean`'s `ρ ≤ 9 − 8/Λ`, `μ ≤ 8 − 9/Λ` the
bad-set mass is `2/(1 + (8 − 9/Λ))`, and maximising `(1 − q)/(2Λe⁴)` over `Λ` tops out near
`1 − 1/720`.  Only `n = 1` reaches `1 − 1/500`, where `q₂ = 0` and
`tvLe_hitAndRun_lemma41_unconditional` gives `1 − 3/80`.

**3.  No counterexample to the binder was found, and the shape one would have to take is
pinned down.**  Testing `Arlib.TVLe` on the singleton `{u}` gives
`ofReal (1/500) ≤ hitAndRunProposal K u univ + hitAndRunProposal K v {u}`
(`ofReal_le_hitAndRunProposal_add_of_binder`), so a counterexample needs a point `u` whose
tangent cone is narrow enough that the walk stays put with probability `> 1 − 1/500` — a cube
vertex in dimension `n ≥ 10` has proposal mass `2¹⁻ⁿ ≤ 1/512` — together with a `v` satisfying
`dist u v < (2/√n)·max{F(u), F(v)}`.  That combination appears to be impossible: a narrow
tangent cone at `u` makes the atom of `hitAndRun K u` exceed `1/8`, hence `F(u) = 0`
(`medianStep_eq_zero_of_hitAndRunProposal_lt`, since `medianStep` is the lower `1/8`-quantile),
so the requirement becomes `F(v) > (√n/2)·dist(u,v)`; and inside a cone of half-angle `α` at
`u`, chords through a point at distance `d` from the apex have length `Θ(d·tan α·√n/√log n)`,
so `F(v) > (√n/2) d` forces `tan α ≳ √log n`, i.e. a cone so wide that the atom at `u` is far
below `1 − 1/500`.  **This paragraph is a heuristic estimate, not a proof**, and it is the
reason nothing here claims the binder is false.

## What is proved here

| name | content |
|---|---|
| `one_sub_hitAndRunProposal_le_hitAndRun_singleton` | the residual atom: `1 − P_u(ℝⁿ) ≤ hitAndRun K u {u}` |
| `medianStep_eq_zero_of_hitAndRunProposal_lt` | proposal mass `< 7/8` ⟹ `F(x) = 0` |
| `sevenEighths_le_hitAndRunProposal_of_medianStep_pos` | its contrapositive |
| `not_dist_lt_of_medianStep_eq_zero` | `F(u) = F(v) = 0` makes the binder's second hypothesis unsatisfiable |
| `exists_sevenEighths_le_of_dist_lt` | one of the two points always moves with probability `≥ 7/8` |
| `tvLe_hitAndRun_binder_of_asymm` | **the reduction**: the binder follows from its asymmetric, off-diagonal, `F(u) > 0` case |
| `five_le_one_add_four_div_pow` | `5 ≤ (1 + 4/n)ⁿ` for `n ≥ 1` (Bernoulli) |
| `lemma41_route_gt_one_sub_inv_five_hundred` | **the no-go**: the route's constant exceeds `1 − 1/500` at every `n ≥ 1` once `q₂ ≥ 9/25` |
| `ofReal_one_sub_lt_ofReal_one_sub` | `1 − 1/500 < 1 − 1/8000` in `ℝ≥0∞`: monotonicity runs the wrong way |
| `crossRatioDist_eq_zero_of_notMem_interior`, `crossRatioDist_lt_of_notMem_interior` | the binder's first hypothesis is vacuous at boundary–interior pairs |
| `tvLe_hitAndRun_binder_uncond_8000` | **the assembly**: the binder at `1 − 1/8000` modulo one named boundary statement `hbd` |
| `hitAndRun_singleton_eq_of_ne` | off-diagonal, the residual atom does not cover `{u}` |
| `ofReal_le_hitAndRunProposal_add_of_tvLe`, `ofReal_le_hitAndRunProposal_add_of_binder` | what the binder forces at the boundary |

## What is not proved, and where it stalls

1. **The binder at `1 − 1/500`, for `n ≥ 2`.**  Stalls at the constant, not at any Lean step:
   `lemma41_route_gt_one_sub_inv_five_hundred` proves that the only available route produces a
   strictly weaker bound.  Closing it needs either a sharper cap estimate *and* a smaller `A₃`
   than `ChordCompare.lean`'s counterexample permits (the arithmetic above shows even the
   sharp `q₂ = 0.3173…` with `A₃`-mass `1/3` gives only `1 − 1/487`, and `A₃`-mass `1/3` is
   exactly what is refuted), or a different proof of Lemma 4.1 altogether.

2. **`hbd`, the boundary hypothesis of `tvLe_hitAndRun_binder_uncond_8000`.**  Stalls at
   `hitAndRunProposal K u Set.univ = 1`, which `tvLe_hitAndRun_lemma41` requires of *both*
   points and which `Arlib.hitAndRunProposal_univ_eq_one_of_mem_interior` supplies only on the
   interior.  `sevenEighths_le_hitAndRunProposal_of_medianStep_pos` is the strongest substitute
   the binder's hypotheses yield, and `7/8 < 1`: the walk from a wedge point of a polytope with
   dihedral angle `φ` has proposal mass `φ/π`, which is `≥ 7/8` but `< 1` for
   `7π/8 ≤ φ < π`.  Bridging would need a version of `tvLe_hitAndRun_of_overlap`
   (`HitAndRunOverlap.lean:517`) that tolerates sub-probability proposals, paying the defect
   `(1 − m_u) + (1 − m_v)` in the constant — and the constant is already the binding
   obstruction, so it was not attempted.  Also stalled: `ha : chordLow K u v < 0`, which
   `chordLow_eq_zero_of_notMem_interior` shows is *false* at boundary–interior pairs, so the
   route through `tvLe_hitAndRun_lemma41` is closed there in principle and not merely in
   practice.

3. **The binder at `n = 1`, where the constant *is* reachable.**  For `n = 1` every chord of a
   closed bounded convex `K ⊆ ℝ` is `K` itself, so `hitAndRun K u` is the uniform measure on
   `K` for *every* `u ∈ K` and the total-variation distance is `0`.  Formalising this needs
   `unifSphere 1` — the normalisation of `(volume : Measure (EuclideanSpace ℝ (Fin 1))).toSphere`
   on the two-point sphere `{±1}` — as an explicit sum of two Diracs, together with the
   evaluation of `chordDensity` against it.  No such computation exists in this repository
   (there is no `Fin 1` special case anywhere in `HitAndRun.lean`, `HitAndRunStep.lean` or
   `SphereCoord.lean`), and Mathlib v4.32's `Measure.toSphere` is developed only through the
   polar-coordinate change of variables.  Not attempted.
-/

set_option maxHeartbeats 8000000

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The atom of the one-step law, and `F = 0` -/

/-- The one-step law keeps an atom at `x` of mass exactly the proposal's defect. -/
theorem one_sub_hitAndRunProposal_le_hitAndRun_singleton
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K)
    (x : EuclideanSpace ℝ (Fin n)) :
    1 - hitAndRunProposal K x Set.univ ≤ hitAndRun K x {x} := by
  rw [hitAndRun_apply_set hKm x (measurableSet_singleton x),
    Set.indicator_of_mem (Set.mem_singleton x), Pi.one_apply, mul_one]
  exact le_add_self

/-- **A point the walk is likely to stay at has `F = 0`.**  If the hit-and-run proposal from
`x` has mass `< 7/8`, the residual atom at `x` carries more than `1/8`, so the closed ball of
radius `0` already lies in `medianStepSet`, and `F(x) = medianStep K x = 0`. -/
theorem medianStep_eq_zero_of_hitAndRunProposal_lt
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K)
    {x : EuclideanSpace ℝ (Fin n)} (h : hitAndRunProposal K x Set.univ < 7 / 8) :
    medianStep K x = 0 := by
  have hmem : (0 : ℝ) ∈ medianStepSet K x := by
    have hball : Metric.closedBall x (0 : ℝ) = {x} := Metric.closedBall_zero
    have hlt : (1 : ℝ≥0∞) / 8 < 1 - hitAndRunProposal K x Set.univ := by
      rw [lt_tsub_iff_right]
      calc (1 : ℝ≥0∞) / 8 + hitAndRunProposal K x Set.univ
          < 1 / 8 + 7 / 8 := by
            exact ENNReal.add_lt_add_left (by simp) h
        _ = 1 := by
            rw [ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 7 = 8 by norm_num,
              ENNReal.div_self (by norm_num) (by norm_num)]
    show (1 : ℝ≥0∞) / 8 < hitAndRun K x (Metric.closedBall x (0 : ℝ))
    rw [hball]
    exact hlt.trans_le (one_sub_hitAndRunProposal_le_hitAndRun_singleton hKm x)
  exact le_antisymm (csInf_le (bddBelow_medianStepSet K x) hmem) (medianStep_nonneg K x)

/-- The contrapositive: a point with a strictly positive median step moves with probability
at least `7/8`.  This is the *only* consequence of the `hLem41` binder's hypotheses that
constrains the boundary, and it is strictly weaker than the `hitAndRunProposal K x univ = 1`
that `tvLe_hitAndRun_lemma41` requires. -/
theorem sevenEighths_le_hitAndRunProposal_of_medianStep_pos
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K)
    {x : EuclideanSpace ℝ (Fin n)} (h : 0 < medianStep K x) :
    7 / 8 ≤ hitAndRunProposal K x Set.univ := by
  by_contra hcon
  exact absurd (medianStep_eq_zero_of_hitAndRunProposal_lt hKm (not_le.mp hcon)) h.ne'

/-! ## 2. The vacuous corner of the binder -/

/-- **If both median steps vanish, the binder's second hypothesis is unsatisfiable.**
`dist u v < (2/√n)·max (F u) (F v) = 0` contradicts `dist_nonneg`. -/
theorem not_dist_lt_of_medianStep_eq_zero {K : Set (EuclideanSpace ℝ (Fin n))}
    {u v : EuclideanSpace ℝ (Fin n)} (hu : medianStep K u = 0) (hv : medianStep K v = 0) :
    ¬ dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) := by
  rw [hu, hv, max_self, mul_zero]
  exact not_lt.mpr dist_nonneg

/-- **At least one of the two points moves with probability `≥ 7/8`.**  Whenever the binder's
hypotheses hold at `u ≠ v`, the pair is not a pair of "stuck" points. -/
theorem exists_sevenEighths_le_of_dist_lt {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) {u v : EuclideanSpace ℝ (Fin n)}
    (hF : dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v)) :
    7 / 8 ≤ hitAndRunProposal K u Set.univ ∨ 7 / 8 ≤ hitAndRunProposal K v Set.univ := by
  rcases eq_or_lt_of_le (medianStep_nonneg K u) with hu | hu
  · rcases eq_or_lt_of_le (medianStep_nonneg K v) with hv | hv
    · exact absurd hF (not_dist_lt_of_medianStep_eq_zero hu.symm hv.symm)
    · exact Or.inr (sevenEighths_le_hitAndRunProposal_of_medianStep_pos hKm hv)
  · exact Or.inl (sevenEighths_le_hitAndRunProposal_of_medianStep_pos hKm hu)

/-! ## 3. Reducing the binder to an asymmetric, non-degenerate form -/

/-- **The `hLem41` binder reduces to the asymmetric statement at a point with positive median
step.**

The binder quantifies over all pairs of `K` with no non-degeneracy at all.  Three of its cases
are free:

* the diagonal `u = v`, by `Arlib.TVLe.refl`;
* pairs with `medianStep K u = medianStep K v = 0`, where the second hypothesis reads
  `dist u v < 0` and is unsatisfiable (`not_dist_lt_of_medianStep_eq_zero`);
* the exchange `u ↔ v`, by `Arlib.TVLe.symm` together with `Arlib.crossRatioDist_comm` and the
  symmetry of `dist` and of `max` — which is also what turns Lovász's own hypothesis
  `|u − v| < (2/√n)·F(u)` (Lemma 8 of *Hit-and-run mixes fast*) into the
  `max{F(u), F(v)}` of Lovász–Vempala's Lemma 4.1.

What is left is one point `u` with `0 < medianStep K u`, hence — by
`sevenEighths_le_hitAndRunProposal_of_medianStep_pos` — with `hitAndRunProposal K u univ ≥ 7/8`,
and `dist u v < (2/√n)·medianStep K u`. -/
theorem tvLe_hitAndRun_binder_of_asymm {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (hKb : Bornology.IsBounded K) {c : ℝ≥0∞}
    (h : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → 0 < medianStep K u →
      7 / 8 ≤ hitAndRunProposal K u Set.univ →
      crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * medianStep K u →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) c) :
    ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) c := by
  intro u hu v hv hdK hF
  rcases eq_or_ne u v with rfl | huv
  · exact (Arlib.TVLe.refl _).mono bot_le
  have hd : 0 < dist u v := dist_pos.mpr huv
  rcases max_cases (medianStep K u) (medianStep K v) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq] at hF
    have hmul : 0 < 2 / Real.sqrt n * medianStep K u := hd.trans hF
    have hpos : 0 < medianStep K u := by
      rcases (medianStep_nonneg K u).lt_or_eq with h1 | h1
      · exact h1
      · rw [← h1, mul_zero] at hmul; exact absurd hmul (lt_irrefl 0)
    exact h u hu v hv huv hpos
      (sevenEighths_le_hitAndRunProposal_of_medianStep_pos hKm hpos) hdK hF
  · rw [heq] at hF
    have hmul : 0 < 2 / Real.sqrt n * medianStep K v := hd.trans hF
    have hpos : 0 < medianStep K v := by
      rcases (medianStep_nonneg K v).lt_or_eq with h1 | h1
      · exact h1
      · rw [← h1, mul_zero] at hmul; exact absurd hmul (lt_irrefl 0)
    refine (h v hv u hu huv.symm hpos
      (sevenEighths_le_hitAndRunProposal_of_medianStep_pos hKm hpos) ?_ ?_).symm
    · rwa [← crossRatioDist_comm hKb huv hu hv]
    · rwa [dist_comm] at hF

/-! ## 4. The constant: why the paper's route cannot reach `1 − 1/500` -/

/-- Bernoulli's inequality at `a = 4/n`: `5 ≤ (1 + 4/n)ⁿ` for every `n ≥ 1`. -/
theorem five_le_one_add_four_div_pow {n : ℕ} (hn : 1 ≤ n) :
    (5 : ℝ) ≤ (1 + 4 / (n : ℝ)) ^ n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2 : (-2 : ℝ) ≤ 4 / (n : ℝ) := by
    have : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
    linarith
  have hbern : (1 : ℝ) + (n : ℝ) * (4 / (n : ℝ)) ≤ (1 + 4 / (n : ℝ)) ^ n :=
    one_add_mul_le_pow h2 n
  rwa [mul_div_cancel₀ _ hn0.ne', show (1 : ℝ) + 4 = 5 by norm_num] at hbern

/-- **The overlap constant produced by Lovász's proof exceeds `1 − 1/500` at every dimension,
once the cap bound is `9/25`.**

`Arlib.MarkovChains.tvLe_hitAndRun_lemma41` concludes at
`1 − (1 − (1/8 + q₂ + 1/2))/(2(1 + 4/n)ⁿ)`, where `q₂` is the mass of the almost-orthogonal
cap `A₂` and `1/2` is the (corrected, two-sided) mass of the short-chord set `A₃`.  Since
`(1 + 4/n)ⁿ ≥ 5` for every `n ≥ 1`, the subtracted term is at most
`(3/8 − q₂)/10 ≤ (3/8 − 9/25)/10 = 3/2000 < 1/500`.

So for **every** `n ≥ 1` and every cap bound `q₂ ≥ 9/25` — in particular the `9/25` that
`Arlib.MarkovChains.unifSphere_cap_le` proves — the conclusion of that route is *strictly
weaker* than the `hLem41` binder demands.  This is the machine-checked form of the statement
that the paper's `1 − 1/500` is not attainable here. -/
theorem lemma41_route_gt_one_sub_inv_five_hundred {n : ℕ} (hn : 1 ≤ n) {q₂ : ℝ}
    (hq₂ : 9 / 25 ≤ q₂) :
    1 - 1 / 500
      < 1 - 1 / (2 * (1 + 4 / (n : ℝ)) ^ n) * (1 - (1 / 8 + q₂ + 1 / 2)) := by
  have hP : (5 : ℝ) ≤ (1 + 4 / (n : ℝ)) ^ n := five_le_one_add_four_div_pow hn
  set P : ℝ := (1 + 4 / (n : ℝ)) ^ n with hPdef
  have hP0 : (0 : ℝ) < 2 * P := by linarith
  have ht0 : (0 : ℝ) < 1 / (2 * P) := by positivity
  have ht : 1 / (2 * P) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hP0 (by norm_num)]; linarith
  rcases le_or_gt q₂ (3 / 8) with hle | hgt
  · nlinarith
  · nlinarith

/-- The instance at the cap bound this repository actually proves,
`Arlib.MarkovChains.unifSphere_cap_le` (`q₂ = 9/25`, `n ≥ 1100`). -/
theorem lemma41_route_gt_one_sub_inv_five_hundred' {n : ℕ} (hn : 1 ≤ n) :
    1 - 1 / 500
      < 1 - 1 / (2 * (1 + 4 / (n : ℝ)) ^ n) * (1 - (1 / 8 + 9 / 25 + 1 / 2)) :=
  lemma41_route_gt_one_sub_inv_five_hundred hn le_rfl

/-- **`Arlib.TVLe.mono` runs the wrong way.**  The proved Lemma 4.1 constant `1 − 1/8000` is a
*larger* total-variation bound than the binder's `1 − 1/500`, so no monotonicity step converts
`hLem41_interior_uncond` into the binder. -/
theorem ofReal_one_sub_lt_ofReal_one_sub :
    ENNReal.ofReal (1 - 1 / 500) < ENNReal.ofReal (1 - 1 / 8000 : ℝ) := by
  refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr ?_
  norm_num

/-! ## 5. The binder's first hypothesis is vacuous at the boundary -/

/-- **`d_K(u,v) = 0` — the junk value — for every boundary `u` and interior `v`.**

`Arlib.crossRatioDist` is a quotient whose denominator `|p−u|·|v−q|` vanishes exactly when `u`
or `v` is an endpoint of the chord (`Arlib/Convexity/CrossRatio.lean`, § *Degenerate values*),
and Lean's `x / 0 = 0`.  By `Arlib.MarkovChains.chordLow_eq_zero_of_notMem_interior` that is
precisely what happens when `u ∈ K \ interior K` and `v ∈ interior K`: the chord does not
extend past `u`, so `chordLow K u v = 0` and the closed form
`(b − a)/((−a)(b − 1))` of `Arlib.crossRatioDist_eq_param` has denominator `0`. -/
theorem crossRatioDist_eq_zero_of_notMem_interior {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {u v : EuclideanSpace ℝ (Fin n)} (huv : u ≠ v) (hu : u ∈ K) (hu' : u ∉ interior K)
    (hv : v ∈ interior K) : crossRatioDist K u v = 0 := by
  rw [crossRatioDist_eq_param hKb huv hu (interior_subset hv),
    chordLow_eq_zero_of_notMem_interior hKc hKcl hKb huv hu hu' hv]
  simp

/-- **The binder's cross-ratio hypothesis holds automatically at every boundary–interior
pair.**

Lovász–Vempala's Lemma 4.1 reads "*Suppose that `d_K(u,v) < 1/8`*", and in the paper
`d_K(u,v) = +∞` at such a pair, so the paper's hypothesis *excludes* it.  The formalised
hypothesis `crossRatioDist K u v < 1/8` does not: it is satisfied, by the junk value `0`.

The `hLem41` binder is therefore **strictly stronger than Lemma 4.1 as printed** — it demands
a total-variation bound at pairs the paper says nothing about.  This is the one place where the
binder, as stated, asks for more than the source supports. -/
theorem crossRatioDist_lt_of_notMem_interior {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {u v : EuclideanSpace ℝ (Fin n)} (huv : u ≠ v) (hu : u ∈ K) (hu' : u ∉ interior K)
    (hv : v ∈ interior K) : crossRatioDist K u v < 1 / 8 := by
  rw [crossRatioDist_eq_zero_of_notMem_interior hKc hKcl hKb huv hu hu' hv]
  norm_num

/-! ## 6. The assembly: the binder at `1 − 1/8000`, boundary pairs isolated -/

/-- **The `hLem41` binder at the proved constant `1 − 1/8000`, with everything but the boundary
discharged.**

Interior pairs are `Arlib.MarkovChains.hLem41_interior_uncond`; the diagonal, the doubly
degenerate pairs and the `u ↔ v` exchange are `tvLe_hitAndRun_binder_of_asymm`.  What is left
is exactly `hbd`: pairs in which **at least one of the two points is not interior**, the pair
is off-diagonal, the walk from `u` moves with probability at least `7/8`, and
`|u − v| < (2/√n)·F(u)`.

`hbd` is *not* proved here, and it is not a restatement of the goal: it is strictly smaller
than the binder (five extra hypotheses, one of them the asymmetric `F(u)` in place of
`max{F(u),F(v)}`).  Section 7 records exactly where it stalls. -/
theorem tvLe_hitAndRun_binder_uncond_8000 (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    (hbd : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → (u ∉ interior K ∨ v ∉ interior K) →
      0 < medianStep K u → 7 / 8 ≤ hitAndRunProposal K u Set.univ →
      crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * medianStep K u →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 8000))) :
    ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 8000)) := by
  refine tvLe_hitAndRun_binder_of_asymm hKm hKb ?_
  intro u hu v hv huv hpos h78 hdK hF
  by_cases hui : u ∈ interior K
  · by_cases hvi : v ∈ interior K
    · refine hLem41_interior_uncond hn hKc hKcl hKm hKb u hui v hvi hdK (lt_of_lt_of_le hF ?_)
      have h2 : (0 : ℝ) ≤ 2 / Real.sqrt n := by positivity
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) h2
    · exact hbd u hu v hv huv (Or.inr hvi) hpos h78 hdK hF
  · exact hbd u hu v hv huv (Or.inl hui) hpos h78 hdK hF

/-! ## 7. What the binder forces at the boundary -/

/-- Off the diagonal the residual atom of the one-step law from `v` sits at `v`, so it does not
help cover `{u}`. -/
theorem hitAndRun_singleton_eq_of_ne {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) {u v : EuclideanSpace ℝ (Fin n)} (huv : u ≠ v) :
    hitAndRun K v {u} = hitAndRunProposal K v {u} := by
  rw [hitAndRun_apply_set hKm v (measurableSet_singleton u),
    Set.indicator_of_notMem (by simpa using huv.symm), mul_zero, add_zero]

/-- **A total-variation bound at level `1 − c` forces the walk from `u` to move.**

Testing `Arlib.TVLe` on the singleton `{u}` and using the residual atom
`1 − P_u(univ) ≤ hitAndRun K u {u}` gives

    ofReal c  ≤  hitAndRunProposal K u univ  +  hitAndRun K v {u}.

So the `hLem41` binder is a genuine constraint at boundary points: at a point whose tangent
cone is so narrow that the hit-and-run proposal keeps mass `< 1/500` — a vertex of a cube in
dimension `n ≥ 10` has proposal mass `2¹⁻ⁿ` — the binder can only hold if the *other* walk
places mass on `{u}`. -/
theorem ofReal_le_hitAndRunProposal_add_of_tvLe {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) {u v : EuclideanSpace ℝ (Fin n)} {c : ℝ} (hc1 : c ≤ 1)
    (h : Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - c))) :
    ENNReal.ofReal c ≤ hitAndRunProposal K u Set.univ + hitAndRun K v {u} := by
  have h1 : hitAndRun K u {u} ≤ hitAndRun K v {u} + ENNReal.ofReal (1 - c) :=
    h.left (measurableSet_singleton u)
  have h2 : 1 - hitAndRunProposal K u Set.univ
      ≤ hitAndRun K v {u} + ENNReal.ofReal (1 - c) :=
    le_trans (one_sub_hitAndRunProposal_le_hitAndRun_singleton hKm u) h1
  have h3 : (1 : ℝ≥0∞)
      ≤ hitAndRun K v {u} + ENNReal.ofReal (1 - c) + hitAndRunProposal K u Set.univ :=
    tsub_le_iff_right.mp h2
  have hofc : ENNReal.ofReal c = 1 - ENNReal.ofReal (1 - c) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 1 - c)]
    norm_num
  rw [hofc]
  refine tsub_le_iff_right.mpr (le_trans h3 (le_of_eq ?_))
  ring
/-- **The binder's own constant, spelled as a lower bound on the proposal masses.**

If the `hLem41` binder holds at an off-diagonal pair `u ≠ v`, then

    1/500  ≤  P_u(ℝⁿ)  +  P_v({u}),

where both terms are *proposal* masses.  A counterexample to the binder therefore has to be a
pair `u ≠ v` satisfying `crossRatioDist K u v < 1/8` and
`dist u v < (2/√n)·max{F(u), F(v)}` with `hitAndRunProposal K u univ + hitAndRunProposal K v {u}
< 1/500`; no such pair is exhibited here, and the search described in the module docstring
found none. -/
theorem ofReal_le_hitAndRunProposal_add_of_binder {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) {u v : EuclideanSpace ℝ (Fin n)} (huv : u ≠ v)
    (h : Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500))) :
    ENNReal.ofReal (1 / 500)
      ≤ hitAndRunProposal K u Set.univ + hitAndRunProposal K v {u} := by
  rw [← hitAndRun_singleton_eq_of_ne hKm huv]
  exact ofReal_le_hitAndRunProposal_add_of_tvLe hKm (by norm_num) h

/-! ## Axiom profile -/

section AxiomCheck

#print axioms one_sub_hitAndRunProposal_le_hitAndRun_singleton
#print axioms medianStep_eq_zero_of_hitAndRunProposal_lt
#print axioms sevenEighths_le_hitAndRunProposal_of_medianStep_pos
#print axioms not_dist_lt_of_medianStep_eq_zero
#print axioms exists_sevenEighths_le_of_dist_lt
#print axioms tvLe_hitAndRun_binder_of_asymm
#print axioms five_le_one_add_four_div_pow
#print axioms lemma41_route_gt_one_sub_inv_five_hundred
#print axioms lemma41_route_gt_one_sub_inv_five_hundred'
#print axioms ofReal_one_sub_lt_ofReal_one_sub
#print axioms crossRatioDist_eq_zero_of_notMem_interior
#print axioms crossRatioDist_lt_of_notMem_interior
#print axioms tvLe_hitAndRun_binder_uncond_8000
#print axioms hitAndRun_singleton_eq_of_ne
#print axioms ofReal_le_hitAndRunProposal_add_of_tvLe
#print axioms ofReal_le_hitAndRunProposal_add_of_binder

end AxiomCheck

end Arlib.MarkovChains
