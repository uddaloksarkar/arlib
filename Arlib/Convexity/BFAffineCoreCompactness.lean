/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFVerticalSelectorIntegration

/-!
# Compactness of interior affine cores

Pointwise Helly convergence is not in general stable under evaluation at moving points.  For
the normalized BF profiles it becomes stable on every fixed compact subinterval of `(0,1)`,
because the profiles have a common Lipschitz constant there.  This file proves that bridge and
then shows that affine cores whose endpoints stay uniformly away from `0,1` survive the BF
profile limit.

The fixed interior margin is essential: normalized concave profiles may jump at either endpoint,
so the corresponding statement with moving endpoints converging to `0` or `1` is false.
-/

open Set Filter
open scoped Topology

namespace Arlib

/-- Evaluation at a moving interior point commutes with a pointwise Helly limit of uniformly
bounded nonnegative concave profiles. -/
theorem tendsto_profile_moving_eval_of_interior
    {u : ℕ → ℝ → ℝ} {V : ℝ → ℝ} {x : ℕ → ℝ} {x₀ M c : ℝ}
    (hconc : ∀ k, ConcaveOn ℝ (Ioo (0 : ℝ) 1) (u k))
    (hu0 : ∀ k t, 0 ≤ u k t) (hM0 : 0 ≤ M) (huM : ∀ k t, u k t ≤ M)
    (hc : 0 < c) (hc2 : c < 1 / 2)
    (hx : ∀ᶠ k in atTop, x k ∈ Icc c (1 - c)) (hx₀ : x₀ ∈ Icc c (1 - c))
    (hxto : Tendsto x atTop (nhds x₀))
    (hlim : ∀ t, Tendsto (fun k => u k t) atTop (nhds (V t))) :
    Tendsto (fun k => u k (x k)) atTop (nhds (V x₀)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  let L : ℝ := 2 * M / c
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨Nx, hNx⟩ := (Metric.tendsto_atTop.mp hxto)
    (eps / (2 * (L + 1))) (by positivity)
  obtain ⟨Nu, hNu⟩ := (Metric.tendsto_atTop.mp (hlim x₀)) (eps / 2) (by positivity)
  obtain ⟨Nh, hNh⟩ := (eventually_atTop.1 hx)
  refine ⟨max Nh (max Nx Nu), fun k hk => ?_⟩
  have hkh : Nh ≤ k := (le_max_left _ _).trans hk
  have hkx : Nx ≤ k := (le_max_left Nx Nu).trans ((le_max_right Nh _).trans hk)
  have hku : Nu ≤ k := (le_max_right Nx Nu).trans ((le_max_right Nh _).trans hk)
  have hxk := hNh k hkh
  have hmove := abs_sub_le_of_concaveOn_Ioo (hconc k) (hu0 k) hM0 (huM k)
    hc hc2 hxk hx₀
  have hdist : |x k - x₀| < eps / (2 * (L + 1)) := by
    simpa [Real.dist_eq] using hNx k hkx
  have hnear : |u k (x k) - u k x₀| < eps / 2 := by
    have hmul : L * |x k - x₀| < eps / 2 := by
      have hratio : L / (L + 1) < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      calc
        L * |x k - x₀| ≤ L * (eps / (2 * (L + 1))) := by
          exact mul_le_mul_of_nonneg_left hdist.le hL0
        _ = eps / 2 * (L / (L + 1)) := by field_simp
        _ < eps / 2 := mul_lt_of_lt_one_right (by positivity) hratio
    exact hmove.trans_lt hmul
  have hfixed : |u k x₀ - V x₀| < eps / 2 := by
    simpa [Real.dist_eq] using hNu k hku
  rw [Real.dist_eq]
  calc
    |u k (x k) - V x₀| ≤
        |u k (x k) - u k x₀| + |u k x₀ - V x₀| := abs_sub_le _ _ _
    _ < eps := by linarith

/-- Affineness on a moving core is closed under BF profile convergence, provided all core
endpoints remain in one fixed compact subinterval of `(0,1)`. -/
theorem parametricProfileAffineOn_limit_of_interior
    {u : ℕ → ℝ → ℝ} {V : ℝ → ℝ} {a b : ℕ → ℝ} {a₀ b₀ M c : ℝ}
    (hconc : ∀ k, ConcaveOn ℝ (Ioo (0 : ℝ) 1) (u k))
    (hu0 : ∀ k t, 0 ≤ u k t) (hM0 : 0 ≤ M) (huM : ∀ k t, u k t ≤ M)
    (hc : 0 < c) (hc2 : c < 1 / 2)
    (ha : Tendsto a atTop (nhds a₀)) (hb : Tendsto b atTop (nhds b₀))
    (hamem : ∀ k, a k ∈ Icc c (1 - c)) (hbmem : ∀ k, b k ∈ Icc c (1 - c))
    (haff : ∀ k, ParametricProfileAffineOn (u k) (a k) (b k))
    (hlim : ∀ t, Tendsto (fun k => u k t) atTop (nhds (V t))) :
    ParametricProfileAffineOn V a₀ b₀ := by
  have ha₀mem : a₀ ∈ Icc c (1 - c) := isClosed_Icc.mem_of_tendsto ha
    (Eventually.of_forall hamem)
  have hb₀mem : b₀ ∈ Icc c (1 - c) := isClosed_Icc.mem_of_tendsto hb
    (Eventually.of_forall hbmem)
  intro s hs
  let z : ℕ → ℝ := fun k => (1 - s) * a k + s * b k
  let z₀ : ℝ := (1 - s) * a₀ + s * b₀
  have hz : Tendsto z atTop (nhds z₀) := (tendsto_const_nhds.sub tendsto_const_nhds).mul ha |>.add
    (tendsto_const_nhds.mul hb)
  have hzmem : ∀ k, z k ∈ Icc c (1 - c) := by
    intro k
    exact (convex_Icc c (1 - c)) (hamem k) (hbmem k)
      (sub_nonneg.mpr hs.2) hs.1 (by ring)
  have hz₀mem : z₀ ∈ Icc c (1 - c) :=
    (convex_Icc c (1 - c)) ha₀mem hb₀mem
      (sub_nonneg.mpr hs.2) hs.1 (by ring)
  have hza := tendsto_profile_moving_eval_of_interior hconc hu0 hM0 huM hc hc2
    (Eventually.of_forall hzmem) hz₀mem hz hlim
  have haa := tendsto_profile_moving_eval_of_interior hconc hu0 hM0 huM hc hc2
    (Eventually.of_forall hamem) ha₀mem ha hlim
  have hbb := tendsto_profile_moving_eval_of_interior hconc hu0 hM0 huM hc hc2
    (Eventually.of_forall hbmem) hb₀mem hb hlim
  have heq : (fun k => u k (z k)) =
      fun k => (1 - s) * u k (a k) + s * u k (b k) := by
    funext k
    exact haff k s hs
  rw [heq] at hza
  exact tendsto_nhds_unique hza
    ((tendsto_const_nhds.mul haa).add (tendsto_const_nhds.mul hbb))

end Arlib

#print axioms Arlib.tendsto_profile_moving_eval_of_interior
#print axioms Arlib.parametricProfileAffineOn_limit_of_interior
