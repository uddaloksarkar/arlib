/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.MarkovChains.Continuous.LazyProfileMajorization

/-!
# Scalar Lovász--Simonovits decay

This file isolates the one-dimensional calculation which turns the lazy midpoint recursion
into geometric decay.  It deliberately has no measure-theoretic content.
-/

namespace Arlib.MarkovChains

open Set

/-- The square-root envelope used in the `s`-conductance LS argument. -/
noncomputable def lsShape (s x : Real) : Real :=
  Real.sqrt (min (x - s) (1 - x - s))

/-- The elementary square-root contraction in the LS induction. -/
theorem average_sqrt_one_sub_add_two_mul_le {ph : Real}
    (hph0 : 0 ≤ ph) (hph : ph ≤ 1 / 2) :
    (Real.sqrt (1 - 2 * ph) + Real.sqrt (1 + 2 * ph)) / 2 ≤ 1 - ph ^ 2 / 2 := by
  have hm0 : 0 ≤ 1 - 2 * ph := by linarith
  have hp0 : 0 ≤ 1 + 2 * ph := by linarith
  let a := Real.sqrt (1 - 2 * ph)
  let b := Real.sqrt (1 + 2 * ph)
  let r := 1 - ph ^ 2 / 2
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 1 - 2 * ph := Real.sq_sqrt hm0
  have hb2 : b ^ 2 = 1 + 2 * ph := Real.sq_sqrt hp0
  have hr0 : 0 ≤ r := by
    dsimp [r]
    nlinarith [sq_nonneg ph]
  let c := 2 * r ^ 2 - 1
  have hc0 : 0 ≤ c := by
    dsimp [c, r]
    nlinarith [sq_nonneg (ph ^ 2 - 2)]
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have habsq : (a * b) ^ 2 = 1 - 4 * ph ^ 2 := by
    rw [mul_pow, ha2, hb2]
    ring
  have hcsq : 1 - 4 * ph ^ 2 ≤ c ^ 2 := by
    have hfac : c ^ 2 - (1 - 4 * ph ^ 2) =
        ph ^ 4 * (1 + (ph ^ 2 / 2 - 2) ^ 2) := by
      dsimp [c, r]
      ring
    rw [← sub_nonneg]
    rw [hfac]
    positivity
  have habc : a * b ≤ c := by
    nlinarith [habsq, hcsq]
  have habsum : (a + b) ^ 2 ≤ (2 * r) ^ 2 := by
    nlinarith [ha2, hb2, habc]
  have hab : a + b ≤ 2 * r := by
    nlinarith [sq_nonneg (a + b - 2 * r)]
  change (a + b) / 2 ≤ r
  linarith

/-- Scaled form of the square-root contraction. -/
theorem average_sqrt_mul_one_sub_add_two_mul_le {z ph : Real}
    (hz : 0 ≤ z) (hph0 : 0 ≤ ph) (hph : ph ≤ 1 / 2) :
    (Real.sqrt (z * (1 - 2 * ph)) + Real.sqrt (z * (1 + 2 * ph))) / 2 ≤
      Real.sqrt z * (1 - ph ^ 2 / 2) := by
  rw [Real.sqrt_mul hz, Real.sqrt_mul hz]
  calc
    (Real.sqrt z * Real.sqrt (1 - 2 * ph) +
        Real.sqrt z * Real.sqrt (1 + 2 * ph)) / 2 =
        Real.sqrt z *
          ((Real.sqrt (1 - 2 * ph) + Real.sqrt (1 + 2 * ph)) / 2) := by ring
    _ ≤ Real.sqrt z * (1 - ph ^ 2 / 2) := by
      gcongr
      exact average_sqrt_one_sub_add_two_mul_le hph0 hph

/-- The LS square-root shape contracts under its canonical symmetric midpoint step. -/
theorem lsShape_midpoint_contract {s x ph : Real}
    (hxl : s ≤ x) (hxu : x ≤ 1 - s) (hph0 : 0 ≤ ph) (hph : ph ≤ 1 / 2) :
    let y := min (x - s) (1 - x - s)
    (lsShape s (x - 2 * ph * y) + lsShape s (x + 2 * ph * y)) / 2 ≤
      lsShape s x * (1 - ph ^ 2 / 2) := by
  let y := min (x - s) (1 - x - s)
  by_cases hside : x - s ≤ 1 - x - s
  · have hy : y = x - s := min_eq_left hside
    have hz : 0 ≤ x - s := sub_nonneg.mpr hxl
    have hm : lsShape s (x - 2 * ph * y) ≤
        Real.sqrt ((x - s) * (1 - 2 * ph)) := by
      apply Real.sqrt_le_sqrt
      calc
        min ((x - 2 * ph * y) - s) (1 - (x - 2 * ph * y) - s) ≤
            (x - 2 * ph * y) - s := min_le_left _ _
        _ = (x - s) * (1 - 2 * ph) := by rw [hy]; ring
    have hp : lsShape s (x + 2 * ph * y) ≤
        Real.sqrt ((x - s) * (1 + 2 * ph)) := by
      apply Real.sqrt_le_sqrt
      calc
        min ((x + 2 * ph * y) - s) (1 - (x + 2 * ph * y) - s) ≤
            (x + 2 * ph * y) - s := min_le_left _ _
        _ = (x - s) * (1 + 2 * ph) := by rw [hy]; ring
    calc
      (lsShape s (x - 2 * ph * y) + lsShape s (x + 2 * ph * y)) / 2 ≤
          (Real.sqrt ((x - s) * (1 - 2 * ph)) +
            Real.sqrt ((x - s) * (1 + 2 * ph))) / 2 := by gcongr
      _ ≤ Real.sqrt (x - s) * (1 - ph ^ 2 / 2) :=
        average_sqrt_mul_one_sub_add_two_mul_le hz hph0 hph
      _ = lsShape s x * (1 - ph ^ 2 / 2) := by
        simp only [lsShape, min_eq_left hside]
  · have hside' : 1 - x - s ≤ x - s := le_of_not_ge hside
    have hy : y = 1 - x - s := min_eq_right hside'
    have hz : 0 ≤ 1 - x - s := by linarith
    have hm : lsShape s (x - 2 * ph * y) ≤
        Real.sqrt ((1 - x - s) * (1 + 2 * ph)) := by
      apply Real.sqrt_le_sqrt
      calc
        min ((x - 2 * ph * y) - s) (1 - (x - 2 * ph * y) - s) ≤
            1 - (x - 2 * ph * y) - s := min_le_right _ _
        _ = (1 - x - s) * (1 + 2 * ph) := by rw [hy]; ring
    have hp : lsShape s (x + 2 * ph * y) ≤
        Real.sqrt ((1 - x - s) * (1 - 2 * ph)) := by
      apply Real.sqrt_le_sqrt
      calc
        min ((x + 2 * ph * y) - s) (1 - (x + 2 * ph * y) - s) ≤
            1 - (x + 2 * ph * y) - s := min_le_right _ _
        _ = (1 - x - s) * (1 - 2 * ph) := by rw [hy]; ring
    calc
      (lsShape s (x - 2 * ph * y) + lsShape s (x + 2 * ph * y)) / 2 ≤
          (Real.sqrt ((1 - x - s) * (1 + 2 * ph)) +
            Real.sqrt ((1 - x - s) * (1 - 2 * ph))) / 2 := by gcongr
      _ = (Real.sqrt ((1 - x - s) * (1 - 2 * ph)) +
            Real.sqrt ((1 - x - s) * (1 + 2 * ph))) / 2 := by ring
      _ ≤ Real.sqrt (1 - x - s) * (1 - ph ^ 2 / 2) :=
        average_sqrt_mul_one_sub_add_two_mul_le hz hph0 hph
      _ = lsShape s x * (1 - ph ^ 2 / 2) := by
        simp only [lsShape, min_eq_right hside']

/-- For a concave curve, expanding a symmetric chord can only decrease the average of its
endpoint values.  This is the scalar bridge from the actual boundary flow to the canonical
`s`-conductance displacement. -/
theorem average_le_average_of_concaveOn_symmetric {F : Real → Real} {l u x e d : Real}
    (hF : ConcaveOn Real (Icc l u) F) (he0 : 0 ≤ e) (hed : e ≤ d)
    (hxm : x - d ∈ Icc l u) (hxp : x + d ∈ Icc l u) :
    (F (x - d) + F (x + d)) / 2 ≤ (F (x - e) + F (x + e)) / 2 := by
  by_cases hd0 : d = 0
  · have he : e = 0 := by linarith
    simp [hd0, he]
  · have hd : 0 < d := lt_of_le_of_ne (he0.trans hed) (Ne.symm hd0)
    let p : Real := (d + e) / (2 * d)
    let q : Real := (d - e) / (2 * d)
    have hp : 0 ≤ p := by dsimp [p]; positivity
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hpq : p + q = 1 := by
      dsimp [p, q]
      field_simp
      ring
    have hargm : p • (x - d) + q • (x + d) = x - e := by
      simp only [smul_eq_mul]
      dsimp [p, q]
      field_simp
      ring
    have hargp : q • (x - d) + p • (x + d) = x + e := by
      simp only [smul_eq_mul]
      dsimp [p, q]
      field_simp
      ring
    have hm := hF.2 hxm hxp hp hq hpq
    have hp' := hF.2 hxm hxp hq hp (by linarith)
    rw [hargm] at hm
    rw [hargp] at hp'
    simp only [smul_eq_mul] at hm hp'
    have hsum :
        (p * F (x - d) + q * F (x + d)) +
          (q * F (x - d) + p * F (x + d)) = F (x - d) + F (x + d) := by
      calc
        _ = (p + q) * F (x - d) + (p + q) * F (x + d) := by ring
        _ = _ := by rw [hpq]; ring
    have hadd := add_le_add hm hp'
    rw [hsum] at hadd
    linarith

/-- Canonicalize a one-step LS bound whose actual displacement is at least the
`s`-conductance displacement. -/
theorem lsCurve_canonical_step_of_flow {Fnext F : Real → Real}
    {s x ph q : Real} (hF : ConcaveOn Real (Icc s (1 - s)) F)
    (hph0 : 0 ≤ ph) (hy0 : 0 ≤ min (x - s) (1 - x - s))
    (hq : ph * min (x - s) (1 - x - s) ≤ q)
    (hxm : x - 2 * q ∈ Icc s (1 - s)) (hxp : x + 2 * q ∈ Icc s (1 - s))
    (hactual : Fnext x ≤ (F (x - 2 * q) + F (x + 2 * q)) / 2) :
    Fnext x ≤
      (F (x - 2 * ph * min (x - s) (1 - x - s)) +
        F (x + 2 * ph * min (x - s) (1 - x - s))) / 2 := by
  refine hactual.trans (average_le_average_of_concaveOn_symmetric hF ?_ ?_ hxm hxp)
  · exact mul_nonneg (mul_nonneg (by positivity) hph0) hy0
  · linarith

/-- Abstract scalar LS iteration.  Once a curve satisfies the canonical midpoint recurrence
and the square-root envelope at time zero, the envelope decays geometrically. -/
theorem lsCurve_decay_of_midpoint
    {F : Nat → Real → Real} {s H C ph : Real}
    (hC0 : 0 ≤ C) (hph0 : 0 ≤ ph) (hph : ph ≤ 1 / 2)
    (hstep : ∀ t x, s ≤ x → x ≤ 1 - s →
      let y := min (x - s) (1 - x - s)
      F (t + 1) x ≤ (F t (x - 2 * ph * y) + F t (x + 2 * ph * y)) / 2)
    (hshape : ∀ x, s ≤ x → x ≤ 1 - s →
      let y := min (x - s) (1 - x - s)
      (lsShape s (x - 2 * ph * y) + lsShape s (x + 2 * ph * y)) / 2 ≤
        lsShape s x * (1 - ph ^ 2 / 2))
    (hbase : ∀ x, s ≤ x → x ≤ 1 - s → F 0 x ≤ H + C * lsShape s x) :
    ∀ t x, s ≤ x → x ≤ 1 - s →
      F t x ≤ H + C * lsShape s x * (1 - ph ^ 2 / 2) ^ t := by
  intro t
  induction t with
  | zero =>
      intro x hxl hxu
      simpa using hbase x hxl hxu
  | succ t ih =>
      intro x hxl hxu
      let y := min (x - s) (1 - x - s)
      have hy0 : 0 ≤ y := by
        dsimp [y]
        exact le_min (sub_nonneg.mpr hxl) (by linarith)
      have hxminusL : s ≤ x - 2 * ph * y := by
        have hyx : y ≤ x - s := min_le_left _ _
        have hm : 0 ≤ (1 - 2 * ph) * y := mul_nonneg (by linarith) hy0
        nlinarith
      have hxminusU : x - 2 * ph * y ≤ 1 - s := by
        have hm : 0 ≤ 2 * ph * y := mul_nonneg (mul_nonneg (by positivity) hph0) hy0
        linarith
      have hxplusL : s ≤ x + 2 * ph * y := by
        have hm : 0 ≤ 2 * ph * y := mul_nonneg (mul_nonneg (by positivity) hph0) hy0
        linarith
      have hxplusU : x + 2 * ph * y ≤ 1 - s := by
        have hyx : y ≤ 1 - x - s := min_le_right _ _
        have hm : 0 ≤ (1 - 2 * ph) * y := mul_nonneg (by linarith) hy0
        nlinarith
      calc
        F (Nat.succ t) x ≤
            (F t (x - 2 * ph * y) + F t (x + 2 * ph * y)) / 2 := by
          simpa [Nat.succ_eq_add_one, y] using hstep t x hxl hxu
        _ ≤ (H + C * lsShape s (x - 2 * ph * y) * (1 - ph ^ 2 / 2) ^ t +
            (H + C * lsShape s (x + 2 * ph * y) * (1 - ph ^ 2 / 2) ^ t)) / 2 := by
          gcongr
          · exact ih _ hxminusL hxminusU
          · exact ih _ hxplusL hxplusU
        _ ≤ H + C * lsShape s x * (1 - ph ^ 2 / 2) ^ (Nat.succ t) := by
          have hr0 : 0 ≤ 1 - ph ^ 2 / 2 := by nlinarith [sq_nonneg ph]
          have hcontract := hshape x hxl hxu
          dsimp only at hcontract
          have hmul := mul_le_mul_of_nonneg_right hcontract
            (mul_nonneg hC0 (pow_nonneg hr0 t))
          change ((lsShape s (x - 2 * ph * y) + lsShape s (x + 2 * ph * y)) / 2) *
              (C * (1 - ph ^ 2 / 2) ^ t) ≤
            (lsShape s x * (1 - ph ^ 2 / 2)) *
              (C * (1 - ph ^ 2 / 2) ^ t) at hmul
          rw [pow_succ]
          calc
            (H + C * lsShape s (x - 2 * ph * y) * (1 - ph ^ 2 / 2) ^ t +
                (H + C * lsShape s (x + 2 * ph * y) * (1 - ph ^ 2 / 2) ^ t)) / 2 =
                H + ((lsShape s (x - 2 * ph * y) + lsShape s (x + 2 * ph * y)) / 2) *
                  (C * (1 - ph ^ 2 / 2) ^ t) := by ring
            _ ≤ H + (lsShape s x * (1 - ph ^ 2 / 2)) *
                  (C * (1 - ph ^ 2 / 2) ^ t) := by linarith
            _ = H + C * lsShape s x *
                  ((1 - ph ^ 2 / 2) ^ t * (1 - ph ^ 2 / 2)) := by ring

/-- Scalar LS decay with the square-root contraction discharged. -/
theorem lsCurve_decay
    {F : Nat → Real → Real} {s H C ph : Real}
    (hC0 : 0 ≤ C) (hph0 : 0 ≤ ph) (hph : ph ≤ 1 / 2)
    (hstep : ∀ t x, s ≤ x → x ≤ 1 - s →
      let y := min (x - s) (1 - x - s)
      F (t + 1) x ≤ (F t (x - 2 * ph * y) + F t (x + 2 * ph * y)) / 2)
    (hbase : ∀ x, s ≤ x → x ≤ 1 - s → F 0 x ≤ H + C * lsShape s x) :
    ∀ t x, s ≤ x → x ≤ 1 - s →
      F t x ≤ H + C * lsShape s x * (1 - ph ^ 2 / 2) ^ t :=
  lsCurve_decay_of_midpoint hC0 hph0 hph hstep
    (fun x hxl hxu => lsShape_midpoint_contract hxl hxu hph0 hph) hbase

/-- At every admissible mass, the LS shape is at most one. -/
theorem lsShape_le_one {s x : Real} (hs0 : 0 ≤ s) (hxl : s ≤ x) (hxu : x ≤ 1 - s) :
    lsShape s x ≤ 1 := by
  have hrad0 : 0 ≤ min (x - s) (1 - x - s) :=
    le_min (sub_nonneg.mpr hxl) (by linarith)
  have hrad1 : min (x - s) (1 - x - s) ≤ 1 := by
    exact (min_le_left _ _).trans (by linarith)
  change Real.sqrt (min (x - s) (1 - x - s)) ≤ 1
  simpa using Real.sqrt_le_sqrt hrad1

/-- Uniform residual bound obtained from the decaying LS envelope. -/
theorem lsCurve_uniform_decay
    {F : Nat → Real → Real} {s H C ph : Real}
    (hs0 : 0 ≤ s) (hC0 : 0 ≤ C) (hph0 : 0 ≤ ph) (hph : ph ≤ 1 / 2)
    (hstep : ∀ t x, s ≤ x → x ≤ 1 - s →
      let y := min (x - s) (1 - x - s)
      F (t + 1) x ≤ (F t (x - 2 * ph * y) + F t (x + 2 * ph * y)) / 2)
    (hbase : ∀ x, s ≤ x → x ≤ 1 - s → F 0 x ≤ H + C * lsShape s x) :
    ∀ t x, s ≤ x → x ≤ 1 - s →
      F t x ≤ H + C * (1 - ph ^ 2 / 2) ^ t := by
  intro t x hxl hxu
  have hmain := lsCurve_decay hC0 hph0 hph hstep hbase t x hxl hxu
  have hr0 : 0 ≤ 1 - ph ^ 2 / 2 := by nlinarith [sq_nonneg ph]
  have hmul := mul_le_mul_of_nonneg_right (lsShape_le_one hs0 hxl hxu)
    (mul_nonneg hC0 (pow_nonneg hr0 t))
  nlinarith

#print axioms Arlib.MarkovChains.average_sqrt_one_sub_add_two_mul_le
#print axioms Arlib.MarkovChains.average_sqrt_mul_one_sub_add_two_mul_le
#print axioms Arlib.MarkovChains.lsShape_midpoint_contract
#print axioms Arlib.MarkovChains.average_le_average_of_concaveOn_symmetric
#print axioms Arlib.MarkovChains.lsCurve_canonical_step_of_flow
#print axioms Arlib.MarkovChains.lsCurve_decay_of_midpoint
#print axioms Arlib.MarkovChains.lsCurve_decay
#print axioms Arlib.MarkovChains.lsCurve_uniform_decay

end Arlib.MarkovChains
