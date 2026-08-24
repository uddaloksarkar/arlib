/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Lattice.KV97.Inflate
import Arlib.MarkovChains.Continuous.ConvexBodyMixing

/-!
# The geometry of the inflated polytope, as the ball walk needs it

`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` proves *unconditional*
total-variation mixing of the lazy ball walk on `Arlib.Polytope.inflate A b κ`,
but it takes two hypotheses **about the inflated body**:

* a diameter bound `∀ x ∈ inflate A b κ, ∀ y ∈ inflate A b κ, dist x y ≤ D`;
* an inscribed ball `Metric.ball c γ ⊆ inflate A b κ`.

A caller who knows the *original* polytope `Arlib.Polytope.body A b` — which is
the object a problem instance actually presents — has no direct way to supply
these. This file closes that gap: it converts geometry of `body A b` into
geometry of `inflate A b κ`, with explicit constants.

## Main results

* `Arlib.KV97.closedBall_subset_inflate` / `Arlib.KV97.ball_subset_inflate` —
  **inflation enlarges the inscribed ball by exactly `κ`**: if
  `Metric.ball c γ ⊆ body A b` with `γ > 0`, then even the *closed*
  ball `Metric.closedBall c (γ + κ)` sits inside `inflate A b κ` (for every real
  `κ`; `κ < 0` reads as a deflation bound). The constant is
  `γ + κ`, not `γ + κ·min‖Aᵢ‖` or anything smaller: displacing facet `i` by
  `κ‖Aᵢ‖` is displacing its hyperplane by metric distance `κ`, so the inscribed
  ball gains `κ` in every direction at once.
* `Arlib.KV97.dist_le_of_mem_inflate` — **the diameter bound**, `D' = (1 + κ/γ)·D`.
  It comes from the homothety bound `Arlib.Polytope.inflate_subset_homothety`
  (a homothety of ratio `k` scales all distances by `|k|`), so it needs the same
  inscribed ball. Boundedness of `body A b` is a genuine hypothesis: inflating an
  unbounded polytope leaves it unbounded, and nothing about `A`, `b` forces
  boundedness.
* `Arlib.KV97.inflateGeom` — **the packaged bundle**: from "`body A b` contains a
  ball of radius `γ > 0` and has all pairwise distances `≤ D`" it returns exactly
  the six facts `mixesWithin_lazy_ballWalk_polytope` consumes — measurability,
  convexity, `volume ≠ 0`, `volume ≠ ⊤`, the diameter bound and the inscribed
  ball — for `inflate A b κ`.
* `Arlib.KV97.mixesWithin_lazy_ballWalk_inflate_of_body` — the mixing theorem with
  its geometric hypotheses moved from `inflate A b κ` to `body A b`.
* `Arlib.KV97.mixesWithin_lazy_ballWalk_inflated_of_body` — the same for
  Kannan–Vempala's `Arlib.KV97.inflated`, which is *definitionally*
  `Arlib.Polytope.inflate A b (kappaOf c r)` (`Arlib.KV97.inflated_eq_inflate`).

## Non-vacuity

`Arlib.KV97.exists_mixing_inflate_box` instantiates everything on the axis-aligned
box `∏ᵢ [tᵢ − R, tᵢ + R]`, cut out by the `2n` constraints `±xᵢ ≤ R ± tᵢ`
(`Arlib.KV97.boxA`, `Arlib.KV97.boxB`), for **every** `κ ≥ 0`, with explicit
`γ = R + κ > 0` and `D = (1 + κ/R)·2R√n > 0`. Two structurally different
instances are recorded: the cube `[-1,1]ⁿ` of
`Arlib.MarkovChains.exists_unconditional_mixing_polytope`
(`Arlib.KV97.exists_mixing_inflate_cube`: `t = 0`, `R = 1`, `κ = 0`, `γ = 1`,
`D = 2√n`) and a genuinely inflated box about an arbitrary centre
(`Arlib.KV97.exists_mixing_inflate_box_shifted`: any `t`, `R = 2`, `κ = 1`,
`γ = 3`, `D = 6√n`), so neither the centre, the radius, nor `κ` is forced.

## Implementation notes

**Degenerate facets.** No lemma here assumes `A i ≠ 0`. A zero normal makes the
`i`-th constraint read `0 ≤ b i`: vacuous when `b i ≥ 0`, and unsatisfiable when
`b i < 0` — in which case `body A b = ∅` and the hypothesis
`Metric.ball c γ ⊆ body A b` with `γ > 0` is already false, so the lemmas are not
silently applied to an empty body. Inflation does not change such a facet either,
since `κ * ‖A i‖ = 0`.

**`toReal` guards.** Nothing here takes `ENNReal.toReal`; the two volume facts are
stated in `ℝ≥0∞` as `≠ 0` and `≠ ⊤`, and `≠ ⊤` is *derived* (from the diameter
bound) rather than assumed, so no `toReal` can silently collapse to `0`.

**Boundedness is assumed, not proved.** `hD` on `body A b` is an honest
hypothesis. `Arlib.Polytope.body` over an arbitrary — possibly empty — index type
can be all of `EuclideanSpace ℝ (Fin n)`, so no theorem can supply it.
-/

namespace Arlib.KV97

open MeasureTheory Set Arlib.MarkovChains
open scoped InnerProductSpace ENNReal

variable {n : ℕ} {ι : Type*}

/-! ## Inflation enlarges the inscribed ball -/

/-- **Inflating by `κ` grows the inscribed ball by `κ`.**

If `Metric.ball c γ ⊆ Arlib.Polytope.body A b` with `γ > 0` and `κ ≥ 0`, then the
*closed* ball of radius `γ + κ` about the same centre lies inside
`Arlib.Polytope.inflate A b κ`.

The proof is Cauchy–Schwarz against the slack
`⟪A i, c⟫ + γ‖A i‖ ≤ b i` supplied by
`Arlib.Polytope.inner_center_le_of_ball_subset`: a point `x` with
`‖x − c‖ ≤ γ + κ` has `⟪A i, x⟫ ≤ ⟪A i, c⟫ + ‖A i‖(γ + κ) ≤ b i + κ‖A i‖`.

No hypothesis on `A i` is needed; a zero normal is covered by
`Arlib.Polytope.inner_center_le_of_ball_subset`. Nor is `κ ≥ 0` needed: for
`κ < 0` the statement is the (still true, and still sharp) claim that *deflating*
shrinks the inscribed ball by at most `|κ|`. -/
theorem closedBall_subset_inflate {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {γ κ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball c γ ⊆ Arlib.Polytope.body A b) :
    Metric.closedBall c (γ + κ) ⊆ Arlib.Polytope.inflate A b κ := by
  intro x hx i
  have hslack : ⟪A i, c⟫_ℝ + γ * ‖A i‖ ≤ b i :=
    Arlib.Polytope.inner_center_le_of_ball_subset hγ hball i
  have hxc : ‖x - c‖ ≤ γ + κ := by
    rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hx
  have hCS : ⟪A i, x - c⟫_ℝ ≤ ‖A i‖ * ‖x - c‖ := real_inner_le_norm _ _
  have hmul : ‖A i‖ * ‖x - c‖ ≤ ‖A i‖ * (γ + κ) :=
    mul_le_mul_of_nonneg_left hxc (norm_nonneg _)
  calc ⟪A i, x⟫_ℝ = ⟪A i, c⟫_ℝ + ⟪A i, x - c⟫_ℝ := by rw [inner_sub_right]; ring
    _ ≤ ⟪A i, c⟫_ℝ + ‖A i‖ * (γ + κ) := by linarith
    _ = (⟪A i, c⟫_ℝ + γ * ‖A i‖) + κ * ‖A i‖ := by ring
    _ ≤ b i + κ * ‖A i‖ := by linarith

/-- **The open-ball form of `Arlib.KV97.closedBall_subset_inflate`**, which is the
shape `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` asks for. -/
theorem ball_subset_inflate {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {γ κ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball c γ ⊆ Arlib.Polytope.body A b) :
    Metric.ball c (γ + κ) ⊆ Arlib.Polytope.inflate A b κ :=
  (Metric.ball_subset_closedBall).trans (closedBall_subset_inflate hγ hball)

/-! ## The diameter of the inflated body -/

/-- A homothety of ratio `k` scales every distance by `|k|`. -/
theorem dist_homothety_apply (c : EuclideanSpace ℝ (Fin n)) (k : ℝ)
    (p q : EuclideanSpace ℝ (Fin n)) :
    dist (AffineMap.homothety c k p) (AffineMap.homothety c k q) = |k| * dist p q := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, dist_eq_norm]
  rw [show (k • (p - c) + c) - (k • (q - c) + c) = k • (p - q) by module, norm_smul,
    Real.norm_eq_abs]

/-- **The diameter bound for the inflated body.**

If `body A b` contains `Metric.ball c γ` with `γ > 0` and all its pairwise
distances are at most `D`, then all pairwise distances in `inflate A b κ` are at
most `(1 + κ/γ)·D`, for `κ ≥ 0`.

The proof is the homothety bound `Arlib.Polytope.inflate_subset_homothety`: the
inflation sits inside the image of `body A b` under the homothety about `c` of
ratio `1 + κ/γ`, and a homothety multiplies distances by its ratio
(`Arlib.KV97.dist_homothety_apply`).

Boundedness of `body A b` is a genuine hypothesis, not a consequence: inflating an
unbounded polytope leaves it unbounded, and `Arlib.Polytope.body` over an empty
index type is the whole space. The inscribed ball is a genuine hypothesis too —
without it there is no ratio to homothet by (a slab `{|x₁| ≤ 0}` in the plane has
diameter `∞` after any positive inflation, yet `0` before). -/
theorem dist_le_of_mem_inflate {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {γ κ D : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hball : Metric.ball c γ ⊆ Arlib.Polytope.body A b)
    (hD : ∀ x ∈ Arlib.Polytope.body A b, ∀ y ∈ Arlib.Polytope.body A b, dist x y ≤ D) :
    ∀ x ∈ Arlib.Polytope.inflate A b κ, ∀ y ∈ Arlib.Polytope.inflate A b κ,
      dist x y ≤ (1 + κ / γ) * D := by
  have hk : (0:ℝ) < 1 + κ / γ := by
    have : (0:ℝ) ≤ κ / γ := div_nonneg hκ hγ.le
    linarith
  intro x hx y hy
  obtain ⟨x', hx', rfl⟩ := Arlib.Polytope.inflate_subset_homothety hγ hκ hball hx
  obtain ⟨y', hy', rfl⟩ := Arlib.Polytope.inflate_subset_homothety hγ hκ hball hy
  rw [dist_homothety_apply, abs_of_nonneg hk.le]
  exact mul_le_mul_of_nonneg_left (hD x' hx' y' hy') hk.le

/-! ## Convexity and measurability

Both already exist in `Arlib.Convexity.Polytope` — `Arlib.Polytope.convex_inflate`
and `Arlib.Polytope.measurableSet_inflate`, read off from the presentation of the
inflation as an intersection of closed half-spaces
(`Arlib.Polytope.inflate_eq_iInter`). They are re-exported here only so that the
bundle below is self-contained; nothing is reproved. -/

/-- `Arlib.Polytope.inflate A b κ` is convex (`Arlib.Polytope.convex_inflate`). -/
theorem convex_inflate (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (κ : ℝ) :
    Convex ℝ (Arlib.Polytope.inflate A b κ) :=
  Arlib.Polytope.convex_inflate A b κ

/-- `Arlib.Polytope.inflate A b κ` is measurable
(`Arlib.Polytope.measurableSet_inflate`). -/
theorem measurableSet_inflate (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (κ : ℝ) :
    MeasurableSet (Arlib.Polytope.inflate A b κ) :=
  Arlib.Polytope.measurableSet_inflate A b κ

/-! ## The packaged bundle -/

/-- **Everything the mixing theorem needs about the inflated body, from the
original body.**

Assumed: `κ ≥ 0`; `Arlib.Polytope.body A b` contains `Metric.ball c γ` with
`γ > 0`; all pairwise distances in `Arlib.Polytope.body A b` are at most `D`.

Proved, for `K = Arlib.Polytope.inflate A b κ`, exactly the six facts
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` and
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_convex` consume:
`MeasurableSet K`, `Convex ℝ K`, `volume K ≠ 0`, `volume K ≠ ⊤`, the diameter
bound with `D' = (1 + κ/γ)·D`, and the inscribed ball with `γ' = γ + κ > 0`.

The two volume facts are *derived*, not assumed: `≠ 0` from the inscribed ball,
`≠ ⊤` from the diameter bound (`K` sits in a closed ball about `c`). In
particular no `ENNReal.toReal` appears anywhere, so no silent `⊤ ↦ 0`. -/
theorem inflateGeom {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {γ κ D : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hball : Metric.ball c γ ⊆ Arlib.Polytope.body A b)
    (hD : ∀ x ∈ Arlib.Polytope.body A b, ∀ y ∈ Arlib.Polytope.body A b, dist x y ≤ D) :
    MeasurableSet (Arlib.Polytope.inflate A b κ) ∧
    Convex ℝ (Arlib.Polytope.inflate A b κ) ∧
    volume (Arlib.Polytope.inflate A b κ) ≠ 0 ∧
    volume (Arlib.Polytope.inflate A b κ) ≠ ⊤ ∧
    (∀ x ∈ Arlib.Polytope.inflate A b κ, ∀ y ∈ Arlib.Polytope.inflate A b κ,
      dist x y ≤ (1 + κ / γ) * D) ∧
    0 < γ + κ ∧
    Metric.ball c (γ + κ) ⊆ Arlib.Polytope.inflate A b κ := by
  have hγκ : 0 < γ + κ := by linarith
  have hball' : Metric.ball c (γ + κ) ⊆ Arlib.Polytope.inflate A b κ :=
    ball_subset_inflate hγ hball
  have hD' := dist_le_of_mem_inflate (D := D) hγ hκ hball hD
  exact ⟨measurableSet_inflate A b κ, convex_inflate A b κ,
    volume_ne_zero_of_ball_subset hγκ hball',
    volume_ne_top_of_diam_bound (hball' (Metric.mem_ball_self hγκ)) hD',
    hD', hγκ, hball'⟩

/-- **Unconditional mixing on the inflated polytope, with hypotheses about the
*original* polytope.**

This is `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` with its two
geometric hypotheses moved from `Arlib.Polytope.inflate A b κ` to
`Arlib.Polytope.body A b`, using `Arlib.KV97.ball_subset_inflate`
(`γ ↦ γ + κ`) and `Arlib.KV97.dist_le_of_mem_inflate` (`D ↦ (1 + κ/γ)·D`).

Assumed: `1 ≤ n`; `κ ≥ 0`; `Metric.ball c γ ⊆ body A b` with `γ > 0`; all pairwise
distances in `body A b` at most `D`; `0 < δ ≤ γ + κ`; an `M`-warm start; `eps > 0`;
enough steps. No isoperimetry, no local-conductance hypothesis, and no hypothesis
about the inflated body itself.

Proved: total-variation mixing of the lazy ball walk on `inflate A b κ` to
`Arlib.uniformOn volume (inflate A b κ)`. -/
theorem mixesWithin_lazy_ballWalk_inflate_of_body (hn : 1 ≤ n)
    (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    {c : EuclideanSpace ℝ (Fin n)} {γ D : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball c γ ⊆ Arlib.Polytope.body A b)
    (hD : ∀ x ∈ Arlib.Polytope.body A b, ∀ y ∈ Arlib.Polytope.body A b, dist x y ≤ D)
    {δ : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ + κ)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (Arlib.uniformOn volume (Arlib.Polytope.inflate A b κ)))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M
      (min (((γ + κ) / ((γ + κ) + (1 + κ / γ) * D)) ^ n / 32)
        ((1 / 2 : ℝ) ^ n / ((1 + κ / γ) * D) *
          (((γ + κ) / ((γ + κ) + (1 + κ / γ) * D)) ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (ballWalk (Arlib.Polytope.inflate A b κ) δ))
      (Arlib.uniformOn volume (Arlib.Polytope.inflate A b κ)) mu0 t (ENNReal.ofReal eps) :=
  mixesWithin_lazy_ballWalk_polytope hn A b κ
    (D := (1 + κ / γ) * D) (dist_le_of_mem_inflate hγ hκ hball hD)
    (c := c) (γ := γ + κ) (by linarith) (ball_subset_inflate hγ hball) hδ hδγ hM hwarm heps ht

/-! ## Transfer to Kannan–Vempala's `inflated`

There are two inflation definitions in the development: `Arlib.Polytope.inflate`,
which the mixing theorem consumes, and `Arlib.KV97.inflated`, which the
Kannan–Vempala pipeline produces. They are the *same* operation — `inflated` is
`inflate` at the displacement `Arlib.KV97.kappaOf c r` — so the transfer below is
`rfl` plus `Arlib.KV97.kappaOf_nonneg`. -/

/-- **The two inflations agree.** `Arlib.KV97.inflated A b c r` is by definition
`Arlib.Polytope.inflate A b (kappaOf c r)`. -/
theorem inflated_eq_inflate (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (cp r : ℝ) :
    inflated A b cp r = Arlib.Polytope.inflate A b (kappaOf cp r) := rfl

/-- The inscribed ball of `Arlib.KV97.inflated`: radius `γ + kappaOf cp r`. -/
theorem ball_subset_inflated {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {cen : EuclideanSpace ℝ (Fin n)} {γ cp r : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b) :
    Metric.ball cen (γ + kappaOf cp r) ⊆ inflated A b cp r :=
  ball_subset_inflate hγ hball

/-- The diameter bound for `Arlib.KV97.inflated`:
`D' = (1 + kappaOf cp r / γ)·D`. The hypothesis `0 ≤ cp` is what makes the
displacement nonnegative (`Arlib.KV97.kappaOf_nonneg`). -/
theorem dist_le_of_mem_inflated {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {cen : EuclideanSpace ℝ (Fin n)} {γ D cp r : ℝ} (hγ : 0 < γ) (hcp : 0 ≤ cp)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hD : ∀ x ∈ Arlib.Polytope.body A b, ∀ y ∈ Arlib.Polytope.body A b, dist x y ≤ D) :
    ∀ x ∈ inflated A b cp r, ∀ y ∈ inflated A b cp r,
      dist x y ≤ (1 + kappaOf cp r / γ) * D :=
  dist_le_of_mem_inflate hγ (kappaOf_nonneg hcp) hball hD

/-- **Unconditional mixing of the lazy ball walk on Kannan–Vempala's `P'`**, with
all geometric hypotheses stated about the original polytope `P = body A b`.

Assumed: `1 ≤ n`; `0 ≤ cp` (so that `kappaOf cp r ≥ 0`); `P` contains
`Metric.ball cen γ` with `γ > 0` and has all pairwise distances at most `D`;
`0 < δ ≤ γ + kappaOf cp r`; an `M`-warm start; `eps > 0`; enough steps.

Proved: total-variation mixing on `Arlib.KV97.inflated A b cp r` to its uniform
measure. -/
theorem mixesWithin_lazy_ballWalk_inflated_of_body (hn : 1 ≤ n)
    (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) {cp : ℝ} (r : ℝ) (hcp : 0 ≤ cp)
    {cen : EuclideanSpace ℝ (Fin n)} {γ D : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hD : ∀ x ∈ Arlib.Polytope.body A b, ∀ y ∈ Arlib.Polytope.body A b, dist x y ≤ D)
    {δ : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ + kappaOf cp r)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn volume (inflated A b cp r)))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M
      (min (((γ + kappaOf cp r) /
              ((γ + kappaOf cp r) + (1 + kappaOf cp r / γ) * D)) ^ n / 32)
        ((1 / 2 : ℝ) ^ n / ((1 + kappaOf cp r / γ) * D) *
          (((γ + kappaOf cp r) /
            ((γ + kappaOf cp r) + (1 + kappaOf cp r / γ) * D)) ^ n) ^ 2 *
          δ / (128 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (ballWalk (inflated A b cp r) δ))
      (Arlib.uniformOn volume (inflated A b cp r)) mu0 t (ENNReal.ofReal eps) :=
  mixesWithin_lazy_ballWalk_inflate_of_body hn A b (kappaOf_nonneg hcp) hγ hball hD hδ hδγ
    hM hwarm heps ht

/-! ## Non-vacuity: the axis-aligned box

`Arlib.KV97.inflateGeom` and `Arlib.KV97.mixesWithin_lazy_ballWalk_inflate_of_body`
assume that `Arlib.Polytope.body A b` is bounded and contains a ball. Neither
follows from the shape of `A` and `b`, so a witness is required, and it must be
non-degenerate: a witness with `γ = 0` (a lower-dimensional body) or `D = 0` (a
point) or an empty body would make the packaged lemma true but useless.

The witness is the box `∏ᵢ [tᵢ − R, tᵢ + R]`, cut out by the `2n` constraints
`⟪±eᵢ, x⟫ ≤ R ± tᵢ` indexed by `Fin n × Bool`. It generalises the cube `[-1,1]ⁿ`
of `Arlib.MarkovChains.exists_unconditional_mixing_polytope` (take `t = 0`,
`R = 1`), and it is instantiated below at two structurally different parameter
sets, so that neither the centre nor the radius nor `κ` is forced. -/

/-- The `2n` outer normals `±eᵢ` of an axis-aligned box, indexed by
`Fin n × Bool` (`true` for `+eᵢ`). -/
noncomputable def boxA (n : ℕ) : Fin n × Bool → EuclideanSpace ℝ (Fin n) :=
  fun p => if p.2 then EuclideanSpace.single p.1 (1 : ℝ) else -EuclideanSpace.single p.1 (1 : ℝ)

/-- The offsets making `Arlib.Polytope.body (boxA n) (boxB R t)` the box of
half-width `R` centred at `t`: `⟪eᵢ, x⟫ ≤ R + tᵢ` and `⟪-eᵢ, x⟫ ≤ R - tᵢ`. -/
noncomputable def boxB (R : ℝ) (t : EuclideanSpace ℝ (Fin n)) : Fin n × Bool → ℝ :=
  fun p => if p.2 then R + t p.1 else R - t p.1

/-- The box is exactly `{x | ∀ i, |xᵢ − tᵢ| ≤ R}`. -/
theorem mem_box_iff {R : ℝ} {t x : EuclideanSpace ℝ (Fin n)} :
    x ∈ Arlib.Polytope.body (boxA n) (boxB R t) ↔ ∀ i, |x i - t i| ≤ R := by
  constructor
  · intro hx i
    have h1 := hx (i, true)
    have h2 := hx (i, false)
    simp [boxA, boxB, EuclideanSpace.inner_single_left, inner_neg_left] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  · intro hx
    rintro ⟨i, s⟩
    have hi := abs_le.1 (hx i)
    cases s <;>
      simp [boxA, boxB, EuclideanSpace.inner_single_left, inner_neg_left] <;>
      linarith [hi.1, hi.2]

/-- The box of half-width `R` centred at `t` contains `Metric.ball t R`. -/
theorem ball_subset_box {R : ℝ} (t : EuclideanSpace ℝ (Fin n)) :
    Metric.ball t R ⊆ Arlib.Polytope.body (boxA n) (boxB R t) := by
  intro x hx
  have hxn : ‖x - t‖ < R := by rwa [← dist_eq_norm, ← Metric.mem_ball]
  refine mem_box_iff.2 fun i => ?_
  have h := PiLp.norm_apply_le (p := 2) (x - t) i
  rw [Real.norm_eq_abs] at h
  have hsub : (x - t) i = x i - t i := rfl
  rw [hsub] at h
  linarith

/-- All pairwise distances in the box of half-width `R ≥ 0` are at most `2R√n`. -/
theorem dist_le_of_mem_box {R : ℝ} (hR : 0 ≤ R) (t : EuclideanSpace ℝ (Fin n)) :
    ∀ x ∈ Arlib.Polytope.body (boxA n) (boxB R t),
      ∀ y ∈ Arlib.Polytope.body (boxA n) (boxB R t),
      dist x y ≤ 2 * R * Real.sqrt (n : ℝ) := by
  intro x hx y hy
  have hxi := mem_box_iff.1 hx
  have hyi := mem_box_iff.1 hy
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ (2 * R) ^ 2 * (n : ℝ) := by
    have hle : ∀ i ∈ Finset.univ, dist (x i) (y i) ^ 2 ≤ (2 * R) ^ 2 := by
      intro i _
      have h1 := abs_le.1 (hxi i)
      have h2 := abs_le.1 (hyi i)
      have hd : dist (x i) (y i) = |x i - y i| := Real.dist_eq _ _
      rw [hd, sq_abs]
      nlinarith [h1.1, h1.2, h2.1, h2.2]
    calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin n, (2 * R) ^ 2 := Finset.sum_le_sum hle
      _ = (2 * R) ^ 2 * (n : ℝ) := by simp [mul_comm]
  calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt ((2 * R) ^ 2 * (n : ℝ)) :=
        Real.sqrt_le_sqrt hsum
    _ = 2 * R * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]

/-- At `R = 1`, `t = 0` the box is the cube `[-1,1]ⁿ` — the very body used as the
non-vacuity witness of `Arlib.MarkovChains.exists_unconditional_mixing_polytope`. -/
theorem mem_cube_iff {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ Arlib.Polytope.body (boxA n) (boxB 1 (0 : EuclideanSpace ℝ (Fin n))) ↔
      ∀ i, |x i| ≤ 1 := by
  simpa using mem_box_iff (R := 1) (t := (0 : EuclideanSpace ℝ (Fin n))) (x := x)

/-- **The packaged lemma fires, non-degenerately, on the inflated box.**

Assumed: `1 ≤ n`; a half-width `R > 0`; any centre `t`; any inflation `κ ≥ 0`;
`0 < δ ≤ R + κ`; `eps > 0`. Nothing else — in particular no property of the body
is assumed, all of them are supplied by `Arlib.KV97.inflateGeom`.

Proved: a starting law and a step count exist for which the lazy ball walk on
`Arlib.Polytope.inflate (boxA n) (boxB R t) κ` mixes to within `eps`, **together
with** explicit witnesses `γ = R + κ` and `D = (1 + κ/R)·2R√n` that are
*strictly positive* and satisfy the inscribed-ball and diameter conjuncts. The two
positivity conjuncts are part of the statement precisely so that the witness
cannot be an empty body, a single point, or a lower-dimensional face. -/
theorem exists_mixing_inflate_box (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R)
    (t : EuclideanSpace ℝ (Fin n)) {κ : ℝ} (hκ : 0 ≤ κ)
    {δ : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ R + κ) {eps : ℝ} (heps : 0 < eps) :
    ∃ (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (_ : IsProbabilityMeasure mu0) (T : ℕ),
      0 < R + κ ∧ 0 < (1 + κ / R) * (2 * R * Real.sqrt (n : ℝ)) ∧
      Metric.ball t (R + κ) ⊆ Arlib.Polytope.inflate (boxA n) (boxB R t) κ ∧
      (∀ x ∈ Arlib.Polytope.inflate (boxA n) (boxB R t) κ,
        ∀ y ∈ Arlib.Polytope.inflate (boxA n) (boxB R t) κ,
        dist x y ≤ (1 + κ / R) * (2 * R * Real.sqrt (n : ℝ))) ∧
      MixesWithin (lazy (ballWalk (Arlib.Polytope.inflate (boxA n) (boxB R t) κ) δ))
        (Arlib.uniformOn volume (Arlib.Polytope.inflate (boxA n) (boxB R t) κ)) mu0 T
        (ENNReal.ofReal eps) := by
  obtain ⟨hK, hconv, hK0, hKtop, hD, hγ, hball⟩ :=
    inflateGeom (A := boxA n) (b := boxB R t) (c := t) (γ := R) (κ := κ)
      (D := 2 * R * Real.sqrt (n : ℝ)) hR hκ (ball_subset_box t) (dist_le_of_mem_box hR.le t)
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hratio : (0:ℝ) < 1 + κ / R := by
    have : (0:ℝ) ≤ κ / R := div_nonneg hκ hR.le
    linarith
  have hDpos : 0 < (1 + κ / R) * (2 * R * Real.sqrt (n : ℝ)) :=
    mul_pos hratio (mul_pos (by linarith) hsqrt)
  obtain ⟨mu0, hprob, T, hmix⟩ :=
    exists_unconditional_mixing_convex hn hK hconv hK0 hKtop hD hγ hball hδ hδγ heps
  exact ⟨mu0, hprob, T, hγ, hDpos, hball, hD, hmix⟩

/-- **Witness 1: the cube `[-1,1]ⁿ`, uninflated** (`R = 1`, `t = 0`, `κ = 0`),
with `γ = 1` and `D = 2√n`. This is the body of
`Arlib.MarkovChains.exists_unconditional_mixing_polytope`
(see `Arlib.KV97.mem_cube_iff`), now reached through `Arlib.KV97.inflateGeom`. -/
theorem exists_mixing_inflate_cube (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (_ : IsProbabilityMeasure mu0) (T : ℕ),
      (0:ℝ) < 1 ∧ (0:ℝ) < 2 * Real.sqrt (n : ℝ) ∧
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆
        Arlib.Polytope.inflate (boxA n) (boxB 1 (0 : EuclideanSpace ℝ (Fin n))) 0 ∧
      (∀ x ∈ Arlib.Polytope.inflate (boxA n) (boxB 1 (0 : EuclideanSpace ℝ (Fin n))) 0,
        ∀ y ∈ Arlib.Polytope.inflate (boxA n) (boxB 1 (0 : EuclideanSpace ℝ (Fin n))) 0,
        dist x y ≤ 2 * Real.sqrt (n : ℝ)) ∧
      MixesWithin
        (lazy (ballWalk
          (Arlib.Polytope.inflate (boxA n) (boxB 1 (0 : EuclideanSpace ℝ (Fin n))) 0) δ))
        (Arlib.uniformOn volume
          (Arlib.Polytope.inflate (boxA n) (boxB 1 (0 : EuclideanSpace ℝ (Fin n))) 0)) mu0 T
        (ENNReal.ofReal eps) := by
  obtain ⟨mu0, hprob, T, -, -, hball, hD, hmix⟩ :=
    exists_mixing_inflate_box hn (R := 1) one_pos (0 : EuclideanSpace ℝ (Fin n))
      (κ := 0) le_rfl hδ (by linarith) heps
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine ⟨mu0, hprob, T, one_pos, by positivity, ?_, ?_, hmix⟩
  · simpa using hball
  · intro x hx y hy
    have h := hD x hx y hy
    norm_num at h
    exact h

/-- **Witness 2: a genuinely inflated box of half-width `2` about an arbitrary
centre `t`** (`R = 2`, `κ = 1`), with `γ = 3` and `D = 6√n`. Structurally
different from witness 1 — nonzero inflation, different half-width, unconstrained
centre — so none of `c`, `γ`, `D`, `κ` is forced by the hypothesis bundle. -/
theorem exists_mixing_inflate_box_shifted (hn : 1 ≤ n) (t : EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (hδ3 : δ ≤ 3) {eps : ℝ} (heps : 0 < eps) :
    ∃ (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (_ : IsProbabilityMeasure mu0) (T : ℕ),
      (0:ℝ) < 3 ∧ (0:ℝ) < 6 * Real.sqrt (n : ℝ) ∧
      Metric.ball t 3 ⊆ Arlib.Polytope.inflate (boxA n) (boxB 2 t) 1 ∧
      (∀ x ∈ Arlib.Polytope.inflate (boxA n) (boxB 2 t) 1,
        ∀ y ∈ Arlib.Polytope.inflate (boxA n) (boxB 2 t) 1,
        dist x y ≤ 6 * Real.sqrt (n : ℝ)) ∧
      MixesWithin (lazy (ballWalk (Arlib.Polytope.inflate (boxA n) (boxB 2 t) 1) δ))
        (Arlib.uniformOn volume (Arlib.Polytope.inflate (boxA n) (boxB 2 t) 1)) mu0 T
        (ENNReal.ofReal eps) := by
  obtain ⟨mu0, hprob, T, -, -, hball, hD, hmix⟩ :=
    exists_mixing_inflate_box hn (R := 2) two_pos t (κ := 1) zero_le_one hδ (by linarith) heps
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine ⟨mu0, hprob, T, by norm_num, by positivity, ?_, ?_, hmix⟩
  · rw [show (3:ℝ) = 2 + 1 by norm_num]
    exact hball
  · intro x hx y hy
    have h := hD x hx y hy
    norm_num at h
    linarith

/-! ### Axiom audit

Every declaration in this file must depend on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms closedBall_subset_inflate
#print axioms ball_subset_inflate
#print axioms dist_homothety_apply
#print axioms dist_le_of_mem_inflate
#print axioms convex_inflate
#print axioms measurableSet_inflate
#print axioms inflateGeom
#print axioms mixesWithin_lazy_ballWalk_inflate_of_body
#print axioms inflated_eq_inflate
#print axioms ball_subset_inflated
#print axioms dist_le_of_mem_inflated
#print axioms mixesWithin_lazy_ballWalk_inflated_of_body
#print axioms boxA
#print axioms boxB
#print axioms mem_box_iff
#print axioms ball_subset_box
#print axioms dist_le_of_mem_box
#print axioms mem_cube_iff
#print axioms exists_mixing_inflate_box
#print axioms exists_mixing_inflate_cube
#print axioms exists_mixing_inflate_box_shifted

end Arlib.KV97
