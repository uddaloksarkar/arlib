/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# `H` is a contraction in the hitting-time weighted norm

    ‖H Q − H Q'‖_w ≤ β·‖Q − Q'‖_w,      w(s,a) = T_s,  β = 1 − 1/max_{s∈Sₙₜ} T_s.

The literature states this as `‖H Q − Q*‖ ≤ β‖Q − Q*‖`; we prove the two-argument
form, which is strictly stronger, needs no prior knowledge of `Q*`, and *gives*
`Q*` as the Banach fixed point (`Arlib.MDP.FixedPoint`).

This is the mathematical heart of the literature: it is what replaces the missing
discount factor in the undiscounted setting.  The chain of the argument is

  1. the target terms cancel (`extVal_sub_eq_zero_of_term`), so only
     non-terminal successors contribute;
  2. `|max_{a'} Q − max_{a'} Q'| ≤ max_{a'}|Q − Q'| ≤ c·T_{s'}`
     (`MDP.abs_vmax_sub_le`);
  3. the one-step inequality `∑_{s'} P(s'∣s,a)·T_{s'} ≤ T_s − 1`
     (`HittingWeight.step`, the standard the hitting-time Bellman inequality);
  4. `T_s − 1 ≤ β·T_s` (`HittingWeight.sub_one_le_beta_mul`), which is where
     `T_s ≤ Tmax` — and hence the finiteness supplied by the no-EC assumption —
     is consumed.
-/
import Arlib.MDP.Bellman
import Arlib.MDP.WeightedNorm
import Arlib.MDP.HittingWeight

namespace Arlib

open scoped BigOperators
open Finset

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

namespace MDP

variable (M : MDP S A) (hw : HittingWeight M)

/-- **Step 1+2 combined.**  A `WLe`-bound on `Q − Q'` bounds the gap of the
boundary extensions *pointwise in the successor*, uniformly over terminal and
non-terminal successors: on a terminal `s'` both sides are `0` and `T_{s'} = 0`;
on a non-terminal `s'` this is `abs_vmax_sub_le`. -/
theorem abs_extVal_sub_le {Q Q' : S → A → ℝ} {c : ℝ}
    (h : M.WLe hw.w (fun s a => Q s a - Q' s a) c) (s' : S) :
    |M.extVal Q s' - M.extVal Q' s'| ≤ c * hw.T s' := by
  by_cases ht : M.isTerm s' = true
  · -- terminal successor: both sides vanish (`T_{s'} = 0`, and the values cancel)
    rw [M.extVal_sub_eq_zero_of_term ht, hw.T_term s' ht, abs_zero, mul_zero]
  · have ht' : M.isTerm s' = false := by simpa using ht
    rw [M.extVal_nonterm ht', M.extVal_nonterm ht']
    exact M.abs_vmax_sub_le fun a ha => h s' a ht' ha

/-- **the contraction property, pointwise form.**  If `Q − Q'` is bounded by `c·T` on
every non-terminal enabled pair, then `H Q − H Q'` is bounded by `β·c·T`. -/
theorem H_contraction_WLe {Q Q' : S → A → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : M.WLe hw.w (fun s a => Q s a - Q' s a) c) :
    M.WLe hw.w (fun s a => M.H Q s a - M.H Q' s a) (hw.beta * c) := by
  intro s a hs ha
  show |M.H Q s a - M.H Q' s a| ≤ hw.beta * c * hw.w s a
  rw [M.H_sub]
  -- step 1+2: bound the summands
  have h1 : |∑ s', M.P s a s' * (M.extVal Q s' - M.extVal Q' s')|
      ≤ ∑ s', M.P s a s' * (c * hw.T s') := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun s' _ => ?_)
    rw [abs_mul, abs_of_nonneg (M.P_nonneg s a s')]
    exact mul_le_mul_of_nonneg_left (M.abs_extVal_sub_le hw h s') (M.P_nonneg s a s')
  have h2 : ∑ s', M.P s a s' * (c * hw.T s') = c * ∑ s', M.P s a s' * hw.T s' := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s' _ => by ring
  -- step 3: the one-step inequality the hitting-time Bellman inequality
  have h3 : (∑ s', M.P s a s' * hw.T s') ≤ hw.T s - 1 := by
    have := hw.step s a hs ha; linarith
  have h4 : c * (∑ s', M.P s a s' * hw.T s') ≤ c * (hw.T s - 1) :=
    mul_le_mul_of_nonneg_left h3 hc
  -- step 4: `T_s − 1 ≤ β·T_s`
  have h5 : c * (hw.T s - 1) ≤ c * (hw.beta * hw.T s) :=
    mul_le_mul_of_nonneg_left (hw.sub_one_le_beta_mul hs) hc
  have h6 : hw.beta * c * hw.w s a = c * (hw.beta * hw.T s) := by
    show hw.beta * c * hw.T s = c * (hw.beta * hw.T s)
    ring
  rw [h6]
  linarith

/-- **the contraction property.**  `H` is a `β`-contraction in the hitting-time
weighted maximum norm, with `β = 1 − 1/max_{s ∈ Sₙₜ} T_s ∈ [0,1)`. -/
theorem H_contraction (Q Q' : S → A → ℝ) :
    M.wnorm hw.w (fun s a => M.H Q s a - M.H Q' s a)
      ≤ hw.beta * M.wnorm hw.w (fun s a => Q s a - Q' s a) := by
  refine M.wnorm_le_of_WLe hw.w_pos
    (mul_nonneg hw.beta_nonneg (M.wnorm_nonneg _ _)) ?_
  exact M.H_contraction_WLe hw (M.wnorm_nonneg _ _)
    (M.WLe_wnorm (Q := fun s a => Q s a - Q' s a) hw.w_pos)

/-- **`H` is non-expansive off `Sₙₜ × A` too**, in the crude form the
value-iteration Cauchy estimate needs: the gap at *any* pair `(s,a)` — enabled
or not, terminal or not — is bounded by `‖Q − Q'‖_w · Tmax`.  (On `Sₙₜ × A` the
sharp bound `H_contraction` is available; this covers the remaining pairs, whose
values are still pinned by `H`.) -/
theorem abs_H_sub_le_wnorm_mul_Tmax (Q Q' : S → A → ℝ) (s : S) (a : A) :
    |M.H Q s a - M.H Q' s a| ≤ M.wnorm hw.w (fun s a => Q s a - Q' s a) * hw.Tmax := by
  have hCnn : 0 ≤ M.wnorm hw.w (fun s a => Q s a - Q' s a) := M.wnorm_nonneg _ _
  have hWLe : M.WLe hw.w (fun s a => Q s a - Q' s a)
      (M.wnorm hw.w (fun s a => Q s a - Q' s a)) := M.WLe_wnorm hw.w_pos
  -- `T_{s'} ≤ Tmax` uniformly: `T_{s'} = 0 ≤ 1 ≤ Tmax` on terminals, `T_le_Tmax` else
  have hT : ∀ s' : S, hw.T s' ≤ hw.Tmax := by
    intro s'
    by_cases ht : M.isTerm s' = true
    · rw [hw.T_term s' ht]; linarith [hw.one_le_Tmax]
    · exact hw.T_le_Tmax (by simpa using ht)
  rw [M.H_sub]
  calc |∑ s', M.P s a s' * (M.extVal Q s' - M.extVal Q' s')|
      ≤ ∑ s', |M.P s a s' * (M.extVal Q s' - M.extVal Q' s')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', M.P s a s' * (M.wnorm hw.w (fun s a => Q s a - Q' s a) * hw.Tmax) := by
        refine Finset.sum_le_sum fun s' _ => ?_
        rw [abs_mul, abs_of_nonneg (M.P_nonneg s a s')]
        refine mul_le_mul_of_nonneg_left ?_ (M.P_nonneg s a s')
        exact le_trans (M.abs_extVal_sub_le hw hWLe s')
          (mul_le_mul_of_nonneg_left (hT s') hCnn)
    _ = M.wnorm hw.w (fun s a => Q s a - Q' s a) * hw.Tmax := by
        rw [← Finset.sum_mul, M.P_sum_one, one_mul]

end MDP

end Arlib
