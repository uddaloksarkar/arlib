/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Uniform convergence of triangular powers to the exponential

This file upgrades `Real.tendsto_one_add_pow_exp_of_tendsto` from scalar sequences to
triangular arrays, uniformly on a compact parameter set.  The boundedness supplied by
compactness is essential: even `(1 + x / n) ^ n` does not converge uniformly to `exp x` on all
of `ℝ`.
-/

open Filter Set Topology
open scoped Topology

namespace Arlib

/-- The real form of the first-order logarithm remainder bound used below. -/
private lemma abs_log_one_add_sub_self_le {x : ℝ} (hx : |x| < 1) :
    |Real.log (1 + x) - x| ≤ |x| ^ 2 * (1 - |x|)⁻¹ / 2 := by
  have h := Complex.norm_log_one_add_sub_self_le (z := (x : ℂ)) (by simpa using hx)
  have hpos : 0 < 1 + x := by rw [abs_lt] at hx; linarith
  have heq : Complex.log (1 + (x : ℂ)) = (Real.log (1 + x) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.ofReal_log hpos.le]
  rw [heq, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real] at h
  simpa using h

/-- If `n * g n x` converges uniformly to a continuous function `G` on a compact set, then
`n * log (1 + g n x)` converges uniformly to `G` there.

This is the uniform triangular-array analogue of
`Real.tendsto_nat_mul_log_one_add_of_tendsto`. -/
theorem tendstoUniformlyOn_nat_mul_log_one_add_of_tendsto
    {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsCompact s)
    {g : ℕ → X → ℝ} {G : X → ℝ} (hG : ContinuousOn G s)
    (hg : TendstoUniformlyOn (fun (n : ℕ) x => (n : ℝ) * g n x) G atTop s) :
    TendstoUniformlyOn (fun (n : ℕ) x => (n : ℝ) * Real.log (1 + g n x)) G atTop s := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact tendstoUniformlyOn_empty
  obtain ⟨C, hC⟩ := hs.bddAbove_image hG.norm
  have hC0 : 0 ≤ C := by
    obtain ⟨x, hx⟩ := hsne
    exact (norm_nonneg (G x)).trans (hC (mem_image_of_mem _ hx))
  let B : ℝ := C + 1
  have hB0 : 0 < B := by dsimp [B]; linarith
  rw [Metric.tendstoUniformlyOn_iff] at hg ⊢
  intro ε hε
  have hsmall := hg (ε / 2) (half_pos hε)
  have hbound := hg 1 zero_lt_one
  have hdiv : Tendsto (fun n : ℕ => B ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hdiv_event : ∀ᶠ n : ℕ in atTop, B ^ 2 / (n : ℝ) < ε / 2 :=
    (tendsto_order.1 hdiv).2 _ (half_pos hε)
  have hn_large : ∀ᶠ n : ℕ in atTop, 2 * B < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (2 * B)
  filter_upwards [hsmall, hbound, hdiv_event, hn_large] with n hnsmall hnbound hndiv hnlarge
  intro x hx
  have hn0 : (0 : ℝ) < n := hB0.trans (by nlinarith)
  have hGx : |G x| ≤ C := by simpa only [Real.norm_eq_abs] using hC (mem_image_of_mem _ hx)
  have hng : |(n : ℝ) * g n x| < B := by
    have hd := hnbound x hx
    rw [Real.dist_eq] at hd
    calc
      |(n : ℝ) * g n x| = |G x - (G x - (n : ℝ) * g n x)| := by congr 1 <;> ring
      _ ≤ |G x| + |G x - (n : ℝ) * g n x| := abs_sub _ _
      _ < B := by dsimp [B]; linarith
  have hg_abs : |g n x| < 1 / 2 := by
    rw [abs_mul, abs_of_pos hn0] at hng
    nlinarith [abs_nonneg (g n x)]
  have hlog := abs_log_one_add_sub_self_le (lt_trans hg_abs one_half_lt_one)
  have hrem : |(n : ℝ) * (Real.log (1 + g n x) - g n x)| < ε / 2 := by
    rw [abs_mul, abs_of_pos hn0]
    calc
      (n : ℝ) * |Real.log (1 + g n x) - g n x|
          ≤ (n : ℝ) * (|g n x| ^ 2 * (1 - |g n x|)⁻¹ / 2) :=
        mul_le_mul_of_nonneg_left hlog hn0.le
      _ ≤ B ^ 2 / (n : ℝ) := by
        have hone : (1 - |g n x|)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith [abs_nonneg (g n x)]) (by norm_num)]
          linarith
        have hng_le : (n : ℝ) * |g n x| ≤ B := by
          rw [← abs_of_pos hn0, ← abs_mul]
          exact hng.le
        calc
          (n : ℝ) * (|g n x| ^ 2 * (1 - |g n x|)⁻¹ / 2)
              ≤ (n : ℝ) * (|g n x| ^ 2 * 2 / 2) := by gcongr
          _ = ((n : ℝ) * |g n x|) ^ 2 / (n : ℝ) := by field_simp
          _ ≤ B ^ 2 / (n : ℝ) := by gcongr
      _ < ε / 2 := hndiv
  have hnsmallx := hnsmall x hx
  rw [Real.dist_eq] at hnsmallx ⊢
  calc
    |G x - (n : ℝ) * Real.log (1 + g n x)|
        = |(G x - (n : ℝ) * g n x) -
            (n : ℝ) * (Real.log (1 + g n x) - g n x)| := by congr 1 <;> ring
    _ ≤ |G x - (n : ℝ) * g n x| +
            |(n : ℝ) * (Real.log (1 + g n x) - g n x)| := abs_sub _ _
    _ < ε := by linarith

/-- **Uniform triangular-array power-to-exponential limit.**

If `n * g n x` converges uniformly to a continuous `G` on a compact set `s`, then
`(1 + g n x) ^ n` converges uniformly to `exp (G x)` on `s`.

Taking `g n x = G x / n` gives the compact-uniform convergence
`(1 + G x / n) ^ n → exp (G x)`.  Taking `g n x` to be a varying affine perturbation whose
product with `n` has a uniform affine limit gives the finite-slope branch of the localization
argument. -/
theorem tendstoUniformlyOn_one_add_pow_exp_of_tendsto
    {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsCompact s)
    {g : ℕ → X → ℝ} {G : X → ℝ} (hG : ContinuousOn G s)
    (hg : TendstoUniformlyOn (fun (n : ℕ) x => (n : ℝ) * g n x) G atTop s) :
    TendstoUniformlyOn (fun n x => (1 + g n x) ^ n) (fun x => Real.exp (G x)) atTop s := by
  have hlog := tendstoUniformlyOn_nat_mul_log_one_add_of_tendsto hs hG hg
  obtain ⟨C, hC⟩ := hs.bddAbove_image hG.norm
  let B : ℝ := max C 0 + 1
  have hB0 : 0 < B := by dsimp [B]; linarith [le_max_right C 0]
  have hG_range : ∀ x ∈ s, G x ∈ Set.Icc (-B) B := by
    intro x hx
    have hGx : |G x| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (mem_image_of_mem _ hx)
    have hCB : C ≤ B := by dsimp only [B]; linarith [le_max_left C 0]
    rw [mem_Icc]
    exact abs_le.mp (hGx.trans hCB)
  have hlog_close := (Metric.tendstoUniformlyOn_iff.1 hlog) 1 zero_lt_one
  have hlog_range : ∀ᶠ n : ℕ in atTop, ∀ x ∈ s,
      (n : ℝ) * Real.log (1 + g n x) ∈ Set.Icc (-B) B := by
    filter_upwards [hlog_close] with n hn
    intro x hx
    have hd := hn x hx
    rw [Real.dist_eq] at hd
    have hGx : |G x| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (mem_image_of_mem _ hx)
    have hH : |(n : ℝ) * Real.log (1 + g n x)| ≤ B := by
      calc
        |(n : ℝ) * Real.log (1 + g n x)|
            = |G x - (G x - (n : ℝ) * Real.log (1 + g n x))| := by congr 1 <;> ring
        _ ≤ |G x| + |G x - (n : ℝ) * Real.log (1 + g n x)| := abs_sub _ _
        _ ≤ B := by dsimp [B]; linarith [le_max_left C 0]
    exact abs_le.mp hH
  have hexp : TendstoUniformlyOn
      (fun (n : ℕ) x => Real.exp ((n : ℝ) * Real.log (1 + g n x)))
      (fun x => Real.exp (G x)) atTop s :=
    UniformContinuousOn.comp_tendstoUniformlyOn_eventually hlog_range hG_range
      (isCompact_Icc.uniformContinuousOn_of_continuous Real.continuous_exp.continuousOn) hlog
  have hg_close := (Metric.tendstoUniformlyOn_iff.1 hg) 1 zero_lt_one
  have hn_large : ∀ᶠ n : ℕ in atTop, 2 * B < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (2 * B)
  have hbase : ∀ᶠ n : ℕ in atTop, ∀ x ∈ s, 0 < 1 + g n x := by
    filter_upwards [hg_close, hn_large] with n hn hnlarge
    intro x hx
    have hn0 : (0 : ℝ) < n := hB0.trans (by nlinarith)
    have hd := hn x hx
    rw [Real.dist_eq] at hd
    have hGx : |G x| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (mem_image_of_mem _ hx)
    have hng : |(n : ℝ) * g n x| < B := by
      calc
        |(n : ℝ) * g n x| = |G x - (G x - (n : ℝ) * g n x)| := by congr 1 <;> ring
        _ ≤ |G x| + |G x - (n : ℝ) * g n x| := abs_sub _ _
        _ < B := by dsimp [B]; linarith [le_max_left C 0]
    rw [abs_mul, abs_of_pos hn0] at hng
    have hg_abs : |g n x| < 1 / 2 := by nlinarith [abs_nonneg (g n x)]
    linarith [neg_le_of_abs_le hg_abs.le]
  apply hexp.congr
  filter_upwards [hbase] with n hn
  intro x hx
  change Real.exp ((n : ℝ) * Real.log (1 + g n x)) = (1 + g n x) ^ n
  rw [Real.exp_nat_mul, Real.exp_log (hn x hx)]

/-- The classical limit `(1 + G x / n) ^ n → exp (G x)`, uniformly for `x` in a compact set
on which `G` is continuous. -/
theorem tendstoUniformlyOn_one_add_div_pow_exp
    {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsCompact s)
    {G : X → ℝ} (hG : ContinuousOn G s) :
    TendstoUniformlyOn (fun (n : ℕ) x => (1 + G x / (n : ℝ)) ^ n)
      (fun x => Real.exp (G x)) atTop s := by
  apply tendstoUniformlyOn_one_add_pow_exp_of_tendsto hs hG
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_ne_atTop 0] with n hn
  intro x hx
  rw [Real.dist_eq, abs_lt]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  constructor <;> rw [mul_div_cancel₀ _ hn'] <;> linarith

#print axioms Arlib.tendstoUniformlyOn_nat_mul_log_one_add_of_tendsto
#print axioms Arlib.tendstoUniformlyOn_one_add_pow_exp_of_tendsto
#print axioms Arlib.tendstoUniformlyOn_one_add_div_pow_exp

end Arlib
