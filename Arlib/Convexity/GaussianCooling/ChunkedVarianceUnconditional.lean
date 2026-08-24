/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.ChunkedSchedule
import Arlib.Convexity.GaussianCooling.LogConcaveProfileVariance

/-!
# Unconditional variance bounds for the flattened adaptive schedule

This file connects the recursively concatenated schedule of `ChunkedSchedule` to the
localization-free compact-body variance theorem.  The rate is constant inside a chunk,
so it is the chunk start, rather than the current variance, that appears in the rate.
-/

namespace Arlib.GaussianCooling.Chunked

open MeasureTheory Metric Set
open scoped BigOperators

/-- The cooling rate attached to a flattened global phase. -/
noncomputable def adaptivePhaseRate (N s₀ : ℝ) (i : ℕ) : ℝ :=
  adaptiveChunkRate N s₀ (adaptivePhaseChunk N s₀ i)

/-- The variance-product factor assigned to one flattened phase after averaging `k`
independent exact-law scores. -/
noncomputable def adaptiveGlobalPhaseVarFactor (k N s₀ : ℝ) (i : ℕ) : ℝ :=
  1 + adaptiveSigmaSq N s₀ i / (k * N)

/-- The flattened successor uses exactly `adaptivePhaseRate`. -/
theorem adaptiveSigmaSq_succ_eq_phaseRate {N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (i : ℕ) :
    adaptiveSigmaSq N s₀ (i + 1) =
      adaptiveSigmaSq N s₀ i * (1 + adaptivePhaseRate N s₀ i) := by
  simpa only [adaptivePhaseRate] using adaptiveSigmaSq_succ hN hs₀ i

/-- The explicit relative second moment occurring in `variance_ratio`. -/
noncomputable def indicatorRelativeSecondMoment {n : ℕ} (K : Set (EuclSpace n))
    (sigma alpha : ℝ) : ℝ :=
  (∫ x, (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2) x /
        gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x) ^ 2
      * (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x /
        G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)))) /
    (∫ x, (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2) x /
        gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x)
      * (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x /
        G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)))) ^ 2

theorem indicatorRelativeSecondMoment_nonneg {n : ℕ} (K : Set (EuclSpace n))
    (sigma alpha : ℝ) : 0 ≤ indicatorRelativeSecondMoment K sigma alpha := by
  unfold indicatorRelativeSecondMoment
  apply div_nonneg
  · apply integral_nonneg
    intro x
    apply mul_nonneg (sq_nonneg _)
    apply div_nonneg
    · exact gW_nonneg (fun y ↦ indicator_nonneg (fun _ _ ↦ by simp) y) _ _
    · exact G_indicator_nonneg K _
  · exact sq_nonneg _

/-- The elementary comparison that makes a chunk-constant rate compatible with Claim 5.11.
If `s ≤ u` and `a=s/(2N)`, then the localization exponent at hot variance `u(1+a)` is at
most `a`, hence its exponential is at most `1+u/N`. -/
theorem chunkConstantRate_exp_le {N s u a : ℝ} (hN : 0 < N) (hs : 0 < s)
    (hsN : s ≤ N) (hsu : s ≤ u) (ha : a = s / (2 * N)) :
    Real.exp (2 * N * a ^ 2 / (u * (1 + a))) ≤ 1 + u / N := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha2 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ (by positivity : 0 < 2 * N)]
    nlinarith
  have hua : 0 < u * (1 + a) := mul_pos hu (by linarith)
  have hratio : s / (u * (1 + a)) ≤ 1 := by
    rw [div_le_one hua]
    nlinarith
  have hexpArg : 2 * N * a ^ 2 / (u * (1 + a)) ≤ a := by
    have heq : 2 * N * a ^ 2 / (u * (1 + a)) =
        a * (s / (u * (1 + a))) := by
      rw [ha]
      field_simp
    rw [heq]
    exact mul_le_of_le_one_right ha0 hratio
  have hexp := exp_le_one_add_two_mul ha0 ha2
  have htwo : 2 * a ≤ u / N := by
    rw [ha]
    have hNne := hN.ne'
    field_simp
    nlinarith
  exact (Real.exp_le_exp.2 hexpArg).trans (hexp.trans (by linarith))

/-- The global factor is literally the corresponding local factor in its located chunk. -/
theorem adaptiveGlobalPhaseVarFactor_eq_local (k N s₀ : ℝ) (i : ℕ) :
    adaptiveGlobalPhaseVarFactor k N s₀ i =
      adaptivePhaseVarFactor k N s₀ (adaptivePhaseChunk N s₀ i)
        (adaptiveLocalPhase N s₀ i) := by
  rfl

/-- A local geometric phase is no colder than its chunk start. -/
theorem adaptiveChunkStart_le_geom {N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (j t : ℕ) :
    adaptiveChunkStart N s₀ j ≤
      geomSchedule (adaptiveChunkStart N s₀ j) (adaptiveChunkRate N s₀ j) t := by
  unfold geomSchedule
  have hstart := adaptiveChunkStart_pos hN hs₀ j
  have hbase : 1 ≤ 1 + adaptiveChunkRate N s₀ j := by
    linarith [adaptiveChunkRate_pos hN hs₀ j]
  have hpow : 1 ≤ (1 + adaptiveChunkRate N s₀ j) ^ t := one_le_pow₀ hbase
  nlinarith

/-- **Per-global-phase exact-law relative second moment.**  For every phase whose chunk
starts below `C²n`, the score between the old variance and its actual chunk-schedule
successor has relative second moment at most `1 + sigmaSqᵢ/(C²n)`.

The rate is chunk-constant, so this is obtained from `compactConvex_lc_variance_bound`
rather than the pointwise-rate specialization `compactConvex_fast_var_bound`. -/
theorem adaptivePhase_relativeSecondMoment_le {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclSpace n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K) {C s₀ : ℝ}
    (hC : 0 < C) (hs₀ : 0 < s₀) (i : ℕ)
    (hbelow : adaptiveChunkStart (C ^ 2 * n) s₀
      (adaptivePhaseChunk (C ^ 2 * n) s₀ i) ≤ C ^ 2 * n)
    (hKR : K ⊆ Metric.closedBall 0 (C * √n)) :
    indicatorRelativeSecondMoment K
        (√(adaptiveSigmaSq (C ^ 2 * n) s₀ i *
          (1 + adaptivePhaseRate (C ^ 2 * n) s₀ i)))
        (adaptivePhaseRate (C ^ 2 * n) s₀ i) ≤
      1 + adaptiveSigmaSq (C ^ 2 * n) s₀ i / (C ^ 2 * n) := by
  let N : ℝ := C ^ 2 * n
  let j : ℕ := adaptivePhaseChunk N s₀ i
  let u : ℝ := adaptiveSigmaSq N s₀ i
  let a : ℝ := adaptivePhaseRate N s₀ i
  have hnNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hN : 0 < N := by dsimp [N]; positivity
  have hu : 0 < u := adaptiveSigmaSq_pos hN hs₀ i
  have hstart : 0 < adaptiveChunkStart N s₀ j := adaptiveChunkStart_pos hN hs₀ j
  have ha : a = adaptiveChunkStart N s₀ j / (2 * N) := by
    rfl
  have ha0 : 0 ≤ a := by rw [ha]; exact (div_pos hstart (by positivity)).le
  have ha2 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ (by positivity : 0 < 2 * N)]
    change adaptiveChunkStart (C ^ 2 * ↑n) s₀
      (adaptivePhaseChunk (C ^ 2 * ↑n) s₀ i) ≤ C ^ 2 * ↑n at hbelow
    dsimp only [N, j]
    nlinarith
  have hstartu : adaptiveChunkStart N s₀ j ≤ u := by
    exact adaptiveChunkStart_le_geom hN hs₀ j (adaptiveLocalPhase N s₀ i)
  have hhot : 0 < u * (1 + a) := mul_pos hu (by linarith)
  have hsqrt : 0 < √(u * (1 + a)) := Real.sqrt_pos.2 hhot
  have hGa : G (indicator K (1 : EuclSpace n → ℝ))
      ((√(u * (1 + a))) ^ 2 / (1 + a)) ≠ 0 :=
    G_indicator_ne_zero hKcl.measurableSet hvol (by positivity)
  have hGb : G (indicator K (1 : EuclSpace n → ℝ))
      ((√(u * (1 + a))) ^ 2) ≠ 0 :=
    G_indicator_ne_zero hKcl.measurableSet hvol (by positivity)
  have hcore := compactConvex_lc_variance_bound hn hKc hKcl hKb hvol hsqrt ha0 ha2
    hKR hGa hGb
  have hnum : Real.exp (2 * N * a ^ 2 / (u * (1 + a))) ≤ 1 + u / N :=
    chunkConstantRate_exp_le hN hstart
      (by simpa [N, j] using hbelow) hstartu ha
  have hR : (C * √(n : ℝ)) ^ 2 = N := by
    dsimp [N]
    rw [mul_pow, Real.sq_sqrt hnpos.le]
  rw [Real.sq_sqrt hhot.le] at hcore
  change indicatorRelativeSecondMoment K (√(u * (1 + a))) a ≤ 1 + u / N
  rw [hR] at hcore
  exact (show indicatorRelativeSecondMoment K (√(u * (1 + a))) a ≤
      Real.exp (2 * N * a ^ 2 / (u * (1 + a))) by
        simpa only [indicatorRelativeSecondMoment, Real.sq_sqrt hhot.le] using hcore).trans hnum

/-- Averaging `k` independent exact-law scores turns the raw bound into precisely the
flattened phase factor used by `adaptiveChunkActualVar`. -/
theorem adaptivePhase_averagedRelativeSecondMoment_le {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclSpace n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K) {C s₀ k : ℝ}
    (hC : 0 < C) (hs₀ : 0 < s₀) (hk : 0 < k) (i : ℕ)
    (hbelow : adaptiveChunkStart (C ^ 2 * n) s₀
      (adaptivePhaseChunk (C ^ 2 * n) s₀ i) ≤ C ^ 2 * n)
    (hKR : K ⊆ Metric.closedBall 0 (C * √n)) :
    1 + (indicatorRelativeSecondMoment K
          (√(adaptiveSigmaSq (C ^ 2 * n) s₀ i *
            (1 + adaptivePhaseRate (C ^ 2 * n) s₀ i)))
          (adaptivePhaseRate (C ^ 2 * n) s₀ i) - 1) / k ≤
      adaptiveGlobalPhaseVarFactor k (C ^ 2 * n) s₀ i := by
  have hraw := adaptivePhase_relativeSecondMoment_le hn hKc hKcl hKb hvol hC hs₀ i
    hbelow hKR
  unfold adaptiveGlobalPhaseVarFactor
  have hsub : indicatorRelativeSecondMoment K
          (√(adaptiveSigmaSq (C ^ 2 * n) s₀ i *
            (1 + adaptivePhaseRate (C ^ 2 * n) s₀ i)))
          (adaptivePhaseRate (C ^ 2 * n) s₀ i) - 1 ≤
      adaptiveSigmaSq (C ^ 2 * n) s₀ i / (C ^ 2 * n) := by
    linarith
  have hdiv := (div_le_div_iff_of_pos_right hk).2 hsub
  calc
    1 + (indicatorRelativeSecondMoment K
          (√(adaptiveSigmaSq (C ^ 2 * n) s₀ i *
            (1 + adaptivePhaseRate (C ^ 2 * n) s₀ i)))
          (adaptivePhaseRate (C ^ 2 * n) s₀ i) - 1) / k
        ≤ 1 + (adaptiveSigmaSq (C ^ 2 * n) s₀ i / (C ^ 2 * n)) / k :=
      by simpa [add_comm] using add_le_add_left hdiv 1
    _ = 1 + adaptiveSigmaSq (C ^ 2 * n) s₀ i / (k * (C ^ 2 * n)) := by ring

/-- Flattening one complete chunk: the product over its consecutive global indices is the
local product `adaptiveChunkActualVar`. -/
theorem prod_globalPhaseVarFactor_chunk {k N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (j : ℕ) :
    ∏ t ∈ Finset.range (adaptiveChunkPhases N s₀ j),
        adaptiveGlobalPhaseVarFactor k N s₀ (adaptiveChunkOffset N s₀ j + t) =
      adaptiveChunkActualVar k N s₀ j := by
  apply Finset.prod_congr rfl
  intro t ht
  rw [adaptiveGlobalPhaseVarFactor_eq_local,
    adaptivePhaseChunk_offset_add hN hs₀ (Finset.mem_range.1 ht),
    adaptiveLocalPhase_offset_add hN hs₀ (Finset.mem_range.1 ht)]

/-- The product over the first `J` flattened chunks is exactly the two-level chunk product. -/
theorem prod_globalPhaseVarFactor_eq_chunks {k N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀) :
    ∀ J : ℕ,
      ∏ i ∈ Finset.range (adaptiveChunkOffset N s₀ J),
          adaptiveGlobalPhaseVarFactor k N s₀ i =
        ∏ j ∈ Finset.range J, adaptiveChunkActualVar k N s₀ j := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
      rw [adaptiveChunkOffset_succ, Finset.prod_range_add, Finset.prod_range_succ, ih,
        prod_globalPhaseVarFactor_chunk hN hs₀ J]

/-- The finite flattened phase product inherits the exponential chunk budget. -/
theorem prod_globalPhaseVarFactor_le_exp {k N s₀ κ : ℝ} {J : ℕ} (hk : 42 ≤ k)
    (hN : 0 < N) (hs₀ : 0 < s₀)
    (hbelow : ∀ j < J, adaptiveChunkStart N s₀ j ≤ N)
    (hsamples : 7 * (J : ℝ) ≤ k * κ) :
    ∏ i ∈ Finset.range (adaptiveChunkOffset N s₀ J),
        adaptiveGlobalPhaseVarFactor k N s₀ i ≤ Real.exp κ := by
  rw [prod_globalPhaseVarFactor_eq_chunks hN hs₀ J]
  exact prod_adaptiveChunkActualVar_le_exp hk hN hs₀ hbelow hsamples

/-- A global phase before the end of chunk `J` is located in one of the chunks `< J`. -/
theorem adaptivePhaseChunk_lt_of_lt_offset {N s₀ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    {i J : ℕ} (hi : i < adaptiveChunkOffset N s₀ J) :
    adaptivePhaseChunk N s₀ i < J := by
  by_contra h
  have hJ : J ≤ adaptivePhaseChunk N s₀ i := by omega
  have hoff := (strictMono_adaptiveChunkOffset hN hs₀).monotone hJ
  have hlower := adaptivePhaseChunk_lower hN hs₀ i
  omega

/-- **Flattened exact-estimator variance budget.**  The product of the actual averaged
per-phase relative-second-moment factors over the first `J` chunks is at most `exp κ`.
This is the direct analytic consumer of `prod_adaptiveChunkActualVar_le_exp`. -/
theorem prod_adaptivePhase_averagedRelativeSecondMoment_le_exp {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclSpace n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K) {C s₀ k κ : ℝ} {J : ℕ}
    (hC : 0 < C) (hs₀ : 0 < s₀) (hk : 42 ≤ k)
    (hbelow : ∀ j < J, adaptiveChunkStart (C ^ 2 * n) s₀ j ≤ C ^ 2 * n)
    (hsamples : 7 * (J : ℝ) ≤ k * κ)
    (hKR : K ⊆ Metric.closedBall 0 (C * √n)) :
    ∏ i ∈ Finset.range (adaptiveChunkOffset (C ^ 2 * n) s₀ J),
        (1 + (indicatorRelativeSecondMoment K
            (√(adaptiveSigmaSq (C ^ 2 * n) s₀ i *
              (1 + adaptivePhaseRate (C ^ 2 * n) s₀ i)))
            (adaptivePhaseRate (C ^ 2 * n) s₀ i) - 1) / k) ≤ Real.exp κ := by
  have hnNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hN : 0 < C ^ 2 * (n : ℝ) := by positivity
  have hk0 : 0 < k := by linarith
  calc
    ∏ i ∈ Finset.range (adaptiveChunkOffset (C ^ 2 * n) s₀ J),
        (1 + (indicatorRelativeSecondMoment K
            (√(adaptiveSigmaSq (C ^ 2 * n) s₀ i *
              (1 + adaptivePhaseRate (C ^ 2 * n) s₀ i)))
            (adaptivePhaseRate (C ^ 2 * n) s₀ i) - 1) / k)
      ≤ ∏ i ∈ Finset.range (adaptiveChunkOffset (C ^ 2 * n) s₀ J),
          adaptiveGlobalPhaseVarFactor k (C ^ 2 * n) s₀ i := by
        apply Finset.prod_le_prod
        · intro i hi
          have hr := indicatorRelativeSecondMoment_nonneg K
            (√(adaptiveSigmaSq (C ^ 2 * n) s₀ i *
              (1 + adaptivePhaseRate (C ^ 2 * n) s₀ i)))
            (adaptivePhaseRate (C ^ 2 * n) s₀ i)
          rw [show 1 + (indicatorRelativeSecondMoment K
                (√(adaptiveSigmaSq (C ^ 2 * n) s₀ i *
                  (1 + adaptivePhaseRate (C ^ 2 * n) s₀ i)))
                (adaptivePhaseRate (C ^ 2 * n) s₀ i) - 1) / k =
              (k - 1 + indicatorRelativeSecondMoment K
                (√(adaptiveSigmaSq (C ^ 2 * n) s₀ i *
                  (1 + adaptivePhaseRate (C ^ 2 * n) s₀ i)))
                (adaptivePhaseRate (C ^ 2 * n) s₀ i)) / k by field_simp; ring]
          exact div_nonneg (by linarith) hk0.le
        · intro i hi
          have hchunk := adaptivePhaseChunk_lt_of_lt_offset hN hs₀
            (Finset.mem_range.1 hi)
          exact adaptivePhase_averagedRelativeSecondMoment_le hn hKc hKcl hKb hvol hC
            hs₀ hk0 i (hbelow _ hchunk) hKR
    _ ≤ Real.exp κ := prod_globalPhaseVarFactor_le_exp hk hN hs₀ hbelow hsamples

/-! ## Axiom audit -/

#print axioms chunkConstantRate_exp_le
#print axioms adaptiveSigmaSq_succ_eq_phaseRate
#print axioms adaptivePhase_relativeSecondMoment_le
#print axioms adaptivePhase_averagedRelativeSecondMoment_le
#print axioms prod_globalPhaseVarFactor_eq_chunks
#print axioms prod_globalPhaseVarFactor_le_exp
#print axioms prod_adaptivePhase_averagedRelativeSecondMoment_le_exp

end Arlib.GaussianCooling.Chunked
