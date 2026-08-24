/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.PhaseFromTVGeneral

/-!
# Cold start: an admissible annealing schedule that **starts at `σ²₀ ≤ 1/n`**

## The question

`Arlib/Convexity/GaussianCooling/PhaseFromTVGeneral.lean`'s `general_rate_annealing_witness`
exhibits a schedule meeting, simultaneously, the general cooling rate `hrate`, the
general-rate variance budget `hbudget`, terminal flatness `hflat` and total cooling
`σ²ₘ/σ²₀ ≥ nR²`.  But it meets `hflat` *at every index*, by starting at

    `σ²₀ = R²/(2·log((1 − α²)^{−(n+1)}))`,

which is enormous.  A Gaussian-cooling volume algorithm must **start cold** — `σ²₀ ≲ 1/n` —
so that `chain 0 = ∫_K e^{−‖x‖²/(2σ²₀)}` is (to within `1 ± ε`) the *known* Gaussian
integral over `ℝⁿ` (`vol3_journal.tex:1326`, `lem:starting-gauss`: `σ² ≤ 1/(n + √(8n log(1/ε)))`
suffices when `B_n ⊆ K`).  If instead `σ²₀ ≈ R²`, then `chain 0 ≈ vol K`, the very unknown
the telescoping product `vol K = chain 0 · ∏ ratios` is meant to compute, and the whole
route is vacuous.

**Question.**  Is there an admissible schedule with `σ²₀ ≤ 1/n` as well?

## The answer: YES, and with no largeness condition on `R`

`cold_start_annealing_witness` below produces, under exactly the hypotheses of
`general_rate_annealing_witness` (`0 < ε ≤ 2` and `e ≤ nR²`; `n ≥ 1` is *derived* from the
latter, not assumed), a rate `α > 0`, a phase count `m ≥ 32` and a geometric schedule with

* `∀ j, 0 < σsq j` and `σsq (j+1) = σsq j·(1 + α)` — `hσ` and `hrate`;
* `(1 − α²)^{−(n+1)} ≤ 1 + varBudget (ε/2)/m` — `hbudget`;
* `∀ j, m ≤ j + 1 → R² ≤ 2·σsq j·log((1 − α²)^{−(n+1)})` — `hflat` at the terminal index
  (and every later one), stated also in the literal form `R² ≤ 2·σsq (m−1)·log(…)`;
* `nR² ≤ σsq m / σsq 0` — the schedule anneals;
* **`σsq 0 ≤ 1/n` — the cold start.**

So `hflat` is *not* incompatible with a cold start, and the interface's collapse of
Cousins–Vempala's two-constant accounting (`TerminalMoment.lean`'s finding: CV pay `e²` at
the terminal phase via `lem:starting-gauss` `:1326` with a separate `(1 + e²/k)` factor in
`lem:accuracy` `:1419`, instead of forcing the terminal *variance* up) is **wasteful, not
fatal**.  Carrying two constants would buy back the phase count computed below; it is not
needed for satisfiability.

## Why the cold start is free, and what it does cost

`hflat` is a lower bound on the *terminal* variance, `σ²_{m−1} ≥ R²/(2Λ)` with
`Λ := log((1 − α²)^{−(n+1)}) ≥ (n+1)α²`; the cold start is an upper bound on the *initial*
one.  Both are satisfied as soon as the schedule's total cooling is large enough:

    `σ²_{m−1}/σ²₀ ≥ n·R²/(2Λ)`.

Total cooling is `(1+α)^m`, and — this is the point — it is **not** capped: raising `m`
raises it like `e^{Θ(√(κm/n))}` (the budget forces `α ≲ √(κ/((n+1)m))`, and `mα ≍ √(κm/(n+1))`),
while the extra cooling the cold start demands over the bare `nR²` is only
`1/(2Λ) ≍ (n+1)L'²/κ²`, i.e. **logarithmically** many extra units of log-cooling.  Buying it
therefore costs only a `log²` factor in the phase count.  Concretely, with
`κ := varBudget (ε/2)`, `T := nR²`, `L := log T`,

    `A := 256(n+1)/κ²`,   `L' := 3L + 4·log A`,
    `α := generalCoolRate n κ L' = κ/(16(n+1)L')`,
    `m := generalPhaseCount n κ L' = ⌈32(n+1)L'²/κ⌉₊`,
    `σsq := geomSchedule (1/n) α`,

so the cold-start schedule uses `m = Θ((n/κ)·(L + log(n/κ))²)` phases where
`general_rate_annealing_witness` uses `Θ((n/κ)·L²)` — a `(1 + log(n/κ)/L)²` overhead, not a
change of regime.  Everything else (`hbudget`, `α < 1`, `m ≥ 32`) is `GeneralRate.lean`'s
explicit construction applied at the *larger* log-target `L'` instead of `L`; nothing about
admissibility is re-proved here.

## Why no condition on `R` is needed (and what the alternative route would need)

One is tempted to keep the target at `L` and read the cold start off the terminal bound
directly: `σ²₀ ≥ σ²_{m−1}/(1+α)^m ≳ [R²·128(n+1)L²/κ²]/(nR²)²`, which is `≤ 1/n` exactly
when `R² ≳ 128L²/κ²`.  That route is **not** available at this repo's granularity: it needs
total cooling `≈ e^{2L} = (nR²)²`, whereas the provable lower bound
`totalCooling_ge_exp` — `(1+α)^m ≥ e^{mα/2}` — together with `mα ≥ 2L` yields only
`e^L = nR²`.  Under `e^L` that route needs `128(n+1)L² ≤ κ²`, which is *never* true
(`κ ≤ 1 ≤ L`).  Sharpening `totalCooling_ge_exp` to `(1+α)^m ≥ e^{0.96·mα}` for `α ≤ 1/16`
would resurrect it and yield a schedule with the smaller phase count `Θ((n/κ)L²)` — at the
price of the largeness hypothesis `R ≳ log(nR²)/ε²`, which is exactly the regime an
isotropic body (`R = O(√n)`) with small `ε` fails.  Raising the cooling target instead, as
below, costs `log²` phases and **no** hypothesis on `R`.  That is the trade this file takes.

## Scope

This file adds a *schedule*.  It proves nothing about conductance, mixing, TV error, the
sampler's phase count, or running time, and it edits no other file.  Feeding the schedule to
`hphase_var_of_tvLe_of_flat_general` still needs that theorem's remaining binders (`hTV`,
`hKR`, `hX`, `htop`, `hslack`), which are untouched.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set

/-! ## 1.  Three elementary ingredients -/

/-- **The general-rate allowance dominates `(n+1)α²`.**  `log((1 − α²)^{−(n+1)}) ≥ (n+1)α²`
for `0 ≤ α < 1`, from `log x ≤ x − 1` at `x = 1 − α²`.  This is the lower bound on `Λ` that
turns `hflat` into an explicit demand on the terminal variance. -/
theorem log_generalRate_const_ge (n : ℕ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ((n : ℝ) + 1) * α ^ 2 ≤ Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)) := by
  have hone : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hlog : Real.log ((1 : ℝ) - α ^ 2) ≤ -α ^ 2 := by
    have := Real.log_le_sub_one_of_pos hone
    linarith
  have hrw : Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1))
      = ((n : ℝ) + 1) * (-Real.log ((1 : ℝ) - α ^ 2)) := by
    rw [Real.log_pow, Real.log_inv]
    push_cast
    ring
  rw [hrw]
  have hN : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  nlinarith

/-- **The cold-start amplification inequality.**  If `L ≤ 3T + 4A` with `T ≥ 2` and
`A ≥ 512`, then `L² ≤ T²A³`.

This is the arithmetic heart of the construction: with `T = nR²`, `A = 256(n+1)/κ²` and
`L = L'` the raised log-target, it says the cooling `e^{L'} = T³A⁴` the schedule achieves
exceeds `T·A·L'²`, the cooling the cold start demands.  The three-way split needs only
`A³ ≥ 27`, `TA² ≥ 72` and `T²A ≥ 48`. -/
theorem cold_start_amp {T A L : ℝ} (hT : (2 : ℝ) ≤ T) (hA : (512 : ℝ) ≤ A)
    (hL0 : 0 ≤ L) (hLle : L ≤ 3 * T + 4 * A) : L ^ 2 ≤ T ^ 2 * A ^ 3 := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hAsq : (262144 : ℝ) ≤ A ^ 2 := by nlinarith
  have hAcube : (27 : ℝ) ≤ A ^ 3 := by nlinarith
  have q2 : (72 : ℝ) ≤ T * A ^ 2 := by nlinarith
  have q3 : (48 : ℝ) ≤ T ^ 2 * A := by nlinarith
  have p1 : 27 * T ^ 2 ≤ T ^ 2 * A ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hAcube (sq_nonneg T)]
  have p2 : 72 * (T * A) ≤ T ^ 2 * A ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left q2 (mul_nonneg hT0.le hA0.le)]
  have p3 : 48 * A ^ 2 ≤ T ^ 2 * A ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left q3 (sq_nonneg A)]
  nlinarith [hLle, hL0]

/-- **One phase back costs at most a factor `2`.**  If `c ≤ (1+α)^m` with `0 < m` and
`0 ≤ α ≤ 1`, then `c ≤ 2·(1+α)^{m−1}`.  Used to move the total-cooling bound from the last
index `m` to the terminal index `m − 1`, where `hflat` lives. -/
theorem le_two_mul_pow_pred {α c : ℝ} {m : ℕ} (hm : 0 < m) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (h : c ≤ (1 + α) ^ m) : c ≤ 2 * (1 + α) ^ (m - 1) := by
  have hp : (0 : ℝ) < (1 + α) ^ (m - 1) := pow_pos (by linarith) _
  have hsucc : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hsplit : (1 + α) ^ m = (1 + α) ^ (m - 1) * (1 + α) := by
    conv_lhs => rw [← hsucc]
    rw [pow_succ]
  rw [hsplit] at h
  nlinarith

/-! ## 2.  The deliverable: a cold-started admissible annealing schedule -/

/-- **Cold start is compatible with everything else.**

For every dimension `n`, every accuracy `0 < ε ≤ 2` and every radius `R` with `nR² ≥ e`
(the hypotheses of `general_rate_annealing_witness`, verbatim — `n ≥ 1` is derived from
`nR² ≥ e`, not assumed), there are a rate `α > 0`, a phase count `m ≥ 32` and a schedule
`σsq` with **all** of:

* `∀ j, 0 < σsq j` — `hσ`;
* `∀ j, σsq (j+1) = σsq j·(1 + α)` — `hrate`;
* `(1 − α²)^{−(n+1)} ≤ 1 + varBudget (ε/2)/m` — `hbudget`;
* `∀ j, m ≤ j + 1 → R² ≤ 2·σsq j·log((1 − α²)^{−(n+1)})` — `hflat` at the terminal index
  and beyond, plus its literal `σsq (m−1)` instance;
* `nR² ≤ σsq m / σsq 0` — the schedule anneals;
* `σsq 0 ≤ 1/n` — **the cold start**.

There is **no largeness condition on `R`**: the cold start is bought by raising the
schedule's log-cooling target from `L = log(nR²)` to `L' = 3L + 4·log(256(n+1)/κ²)`, which
costs a factor `Θ((1 + log(n/κ)/L)²)` in the phase count and nothing else.  See the module
docstring for the alternative (a condition `R² ≳ 128L²/κ²` with the smaller phase count).

The witnesses are `GeneralRate.lean`'s explicit ones at the raised target — `α =
generalCoolRate n κ L'`, `m = generalPhaseCount n κ L'`, `κ = varBudget (ε/2)` — and the
geometric schedule `geomSchedule (1/n) α`, i.e. `σ²ⱼ = (1/n)(1+α)ʲ`, started at exactly the
cold-start ceiling. -/
theorem cold_start_annealing_witness (n : ℕ) {ε R : ℝ} (hε0 : 0 < ε) (hε2 : ε ≤ 2)
    (hR : Real.exp 1 ≤ (n : ℝ) * R ^ 2) :
    ∃ (α : ℝ) (m : ℕ) (σsq : ℕ → ℝ),
      0 < m ∧ (32 : ℝ) ≤ (m : ℝ) ∧ 0 < α ∧ α < 1 ∧
      (∀ j, 0 < σsq j) ∧
      (∀ j, σsq (j + 1) = σsq j * (1 + α)) ∧
      ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ 1 + varBudget (ε / 2) / (m : ℝ) ∧
      (∀ j, m ≤ j + 1 →
        R ^ 2 ≤ 2 * σsq j * Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1))) ∧
      R ^ 2 ≤ 2 * σsq (m - 1) * Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)) ∧
      (n : ℝ) * R ^ 2 ≤ σsq m / σsq 0 ∧
      σsq 0 ≤ 1 / (n : ℝ) := by
  -- `n ≥ 1` is forced by `hR`: at `n = 0` the hypothesis reads `e ≤ 0`.
  have hnN : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h] at hR
      simp only [Nat.cast_zero, zero_mul] at hR
      exact absurd hR (not_le.2 (Real.exp_pos 1))
    · omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne0 : (n : ℝ) ≠ 0 := hn0.ne'
  obtain ⟨hκ0, hκ1⟩ := varBudget_pos_le_one (ε := ε / 2) (by linarith) (by linarith)
  set κ : ℝ := varBudget (ε / 2) with hκdef
  set T : ℝ := (n : ℝ) * R ^ 2 with hTdef
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hR
  have hT2 : (2 : ℝ) ≤ T := le_trans (by linarith [Real.exp_one_gt_d9]) hR
  have hκne : κ ≠ 0 := hκ0.ne'
  have hnne : ((n : ℝ) + 1) ≠ 0 := by positivity
  -- the log-target `L`, the amplification `A`, and the *raised* log-target `L'`
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log T := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 256 * ((n : ℝ) + 1) / κ ^ 2 := ⟨_, rfl⟩
  have hLge : (1 : ℝ) ≤ L := by rw [hLdef]; exact (Real.le_log_iff_exp_le hT0).2 hR
  have hLT : L ≤ T := by
    rw [hLdef]
    linarith [Real.log_le_sub_one_of_pos hT0]
  have hA512 : (512 : ℝ) ≤ A := by
    rw [hAdef, le_div_iff₀ (by positivity)]
    nlinarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hlogA0 : (0 : ℝ) ≤ Real.log A := Real.log_nonneg (by linarith)
  have hlogAA : Real.log A ≤ A := by
    linarith [Real.log_le_sub_one_of_pos hA0]
  obtain ⟨L', hL'def⟩ : ∃ L' : ℝ, L' = 3 * L + 4 * Real.log A := ⟨_, rfl⟩
  have hL'1 : (1 : ℝ) ≤ L' := by rw [hL'def]; linarith
  have hL'0 : (0 : ℝ) < L' := by linarith
  have hLL' : L ≤ L' := by rw [hL'def]; linarith
  have hL'ne : L' ≠ 0 := hL'0.ne'
  -- `GeneralRate.lean`'s explicit admissible pair, at the raised target `L'`
  set α : ℝ := generalCoolRate n κ L' with hαdef
  set m : ℕ := generalPhaseCount n κ L' with hmdef
  have hα0 : 0 < α := generalCoolRate_pos hκ0 hL'0
  have hα16 : α ≤ 1 / 16 := generalCoolRate_le_sixteenth hκ0 hκ1 hL'1
  have hα1 : α < 1 := by linarith
  have hmpos : 0 < m := generalPhaseCount_pos hκ0 hκ1 hL'1
  have hm32 : (32 : ℝ) ≤ (m : ℝ) := generalPhaseCount_ge_32 hκ0 hκ1 hL'1
  have hbud : ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ 1 + κ / (m : ℝ) :=
    generalCoolRate_meets_budget hκ0 hκ1 hL'1
  have hcool : Real.exp L' ≤ (1 + α) ^ m := generalCoolRate_total_cooling hκ0 hκ1 hL'1
  -- the cooling the raised target achieves, in closed form
  have hexp3 : Real.exp (3 * L) = T ^ 3 := by
    have h : (3 : ℝ) * L = Real.log (T ^ 3) := by
      rw [Real.log_pow, hLdef]; push_cast; ring
    rw [h, Real.exp_log (by positivity)]
  have hexp4 : Real.exp (4 * Real.log A) = A ^ 4 := by
    have h : (4 : ℝ) * Real.log A = Real.log (A ^ 4) := by
      rw [Real.log_pow]; push_cast; ring
    rw [h, Real.exp_log (by positivity)]
  have hexpL' : Real.exp L' = T ^ 3 * A ^ 4 := by
    rw [hL'def, Real.exp_add, hexp3, hexp4]
  -- the general-rate allowance is at least `1/(A·L'²)`
  have hΛ : 1 / (A * L' ^ 2) ≤ Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)) := by
    have hid : ((n : ℝ) + 1) * α ^ 2 = 1 / (A * L' ^ 2) := by
      rw [hαdef, generalCoolRate, hAdef]
      field_simp
      ring
    rw [← hid]
    exact log_generalRate_const_ge n hα0.le hα1
  -- the arithmetic crux
  have hcrux : L' ^ 2 ≤ T ^ 2 * A ^ 3 :=
    cold_start_amp hT2 hA512 hL'0.le (by rw [hL'def]; linarith)
  have hR2 : R ^ 2 = T / (n : ℝ) := by rw [hTdef]; field_simp
  -- terminal flatness, at the terminal index and every later one
  have hflat : ∀ j, m ≤ j + 1 →
      R ^ 2 ≤ 2 * geomSchedule (1 / (n : ℝ)) α j
        * Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)) := by
    intro j hj
    have hjm : m - 1 ≤ j := by omega
    have hpow : (1 + α) ^ (m - 1) ≤ (1 + α) ^ j :=
      pow_le_pow_right₀ (by linarith) hjm
    have hhalf : Real.exp L' ≤ 2 * (1 + α) ^ (m - 1) :=
      le_two_mul_pow_pred hmpos hα0.le (by linarith) hcool
    have h2 : T ^ 3 * A ^ 4 / 2 ≤ (1 + α) ^ j := by
      rw [hexpL'] at hhalf; linarith
    have hs : T ^ 3 * A ^ 4 / (2 * (n : ℝ)) ≤ geomSchedule (1 / (n : ℝ)) α j := by
      have hmul := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
      calc T ^ 3 * A ^ 4 / (2 * (n : ℝ)) = 1 / (n : ℝ) * (T ^ 3 * A ^ 4 / 2) := by
            field_simp
        _ ≤ 1 / (n : ℝ) * (1 + α) ^ j := hmul
        _ = geomSchedule (1 / (n : ℝ)) α j := by rw [geomSchedule]
    have hspos : (0 : ℝ) < T ^ 3 * A ^ 4 / (2 * (n : ℝ)) := by positivity
    have hlpos : (0 : ℝ) < 1 / (A * L' ^ 2) := by positivity
    have hmul2 : T ^ 3 * A ^ 4 / (2 * (n : ℝ)) * (1 / (A * L' ^ 2))
        ≤ geomSchedule (1 / (n : ℝ)) α j
            * Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)) :=
      mul_le_mul hs hΛ hlpos.le (le_trans hspos.le hs)
    have hgoal : R ^ 2 ≤ 2 * (T ^ 3 * A ^ 4 / (2 * (n : ℝ)) * (1 / (A * L' ^ 2))) := by
      rw [hR2]
      have heq : 2 * (T ^ 3 * A ^ 4 / (2 * (n : ℝ)) * (1 / (A * L' ^ 2)))
          = T ^ 3 * A ^ 3 / ((n : ℝ) * L' ^ 2) := by
        field_simp
      rw [heq, div_le_div_iff₀ hn0 (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hcrux
        (by positivity : (0 : ℝ) ≤ T * (n : ℝ))]
    linarith
  -- the schedule anneals
  have hcoolgoal : T ≤ geomSchedule (1 / (n : ℝ)) α m / geomSchedule (1 / (n : ℝ)) α 0 := by
    rw [geomSchedule_div_zero (by positivity : (1 : ℝ) / (n : ℝ) ≠ 0) m]
    calc T = Real.exp L := by rw [hLdef, Real.exp_log hT0]
      _ ≤ Real.exp L' := Real.exp_le_exp.2 hLL'
      _ ≤ (1 + α) ^ m := hcool
  -- and it starts cold
  have hcold : geomSchedule (1 / (n : ℝ)) α 0 ≤ 1 / (n : ℝ) :=
    le_of_eq (geomSchedule_zero _ _)
  exact ⟨α, m, geomSchedule (1 / (n : ℝ)) α, hmpos, hm32, hα0, hα1,
    fun j => geomSchedule_pos (by positivity) (by linarith) j,
    fun j => geomSchedule_succ _ α j, hbud, hflat, hflat (m - 1) (by omega),
    hcoolgoal, hcold⟩

/-! ## 3.  A fully concrete instance (`CLAUDE.md` §11) -/

/-- **Non-vacuity of the cold-start witness**, at `n = 3`, `ε = 1`, `R = 2` — so
`nR² = 12 ≥ e` and the cold-start ceiling is `1/3`.  Every hypothesis is discharged by
computation, mirroring `general_rate_annealing_witness_concrete`. -/
theorem cold_start_annealing_witness_concrete :
    ∃ (α : ℝ) (m : ℕ) (σsq : ℕ → ℝ),
      0 < m ∧ (32 : ℝ) ≤ (m : ℝ) ∧ 0 < α ∧ α < 1 ∧
      (∀ j, 0 < σsq j) ∧
      (∀ j, σsq (j + 1) = σsq j * (1 + α)) ∧
      ((1 : ℝ) - α ^ 2)⁻¹ ^ (3 + 1) ≤ 1 + varBudget (1 / 2) / (m : ℝ) ∧
      (∀ j, m ≤ j + 1 →
        (4 : ℝ) ≤ 2 * σsq j * Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (3 + 1))) ∧
      (4 : ℝ) ≤ 2 * σsq (m - 1) * Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (3 + 1)) ∧
      (12 : ℝ) ≤ σsq m / σsq 0 ∧
      σsq 0 ≤ 1 / 3 := by
  have h12 : ((3 : ℕ) : ℝ) * (2 : ℝ) ^ 2 = 12 := by norm_num
  have hR : Real.exp 1 ≤ ((3 : ℕ) : ℝ) * (2 : ℝ) ^ 2 := by
    rw [h12]; linarith [Real.exp_one_lt_d9]
  obtain ⟨α, m, σsq, hm, hm32, hα0, hα1, hpos, hrate, hbud, hflat, hflat1, hcool, hcold⟩ :=
    cold_start_annealing_witness 3 (ε := 1) (R := 2) one_pos (by norm_num) hR
  refine ⟨α, m, σsq, hm, hm32, hα0, hα1, hpos, hrate, hbud, fun j hj => ?_, ?_, ?_, ?_⟩
  · have := hflat j hj; norm_num at this ⊢; linarith
  · have := hflat1; norm_num at this ⊢; linarith
  · rw [h12] at hcool; exact hcool
  · have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [h3] at hcold; exact hcold

end Arlib.GaussianCooling

/-! ## Axiom audit (`CLAUDE.md` §4)

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Arlib.GaussianCooling.log_generalRate_const_ge
#print axioms Arlib.GaussianCooling.cold_start_amp
#print axioms Arlib.GaussianCooling.le_two_mul_pow_pred
#print axioms Arlib.GaussianCooling.cold_start_annealing_witness
#print axioms Arlib.GaussianCooling.cold_start_annealing_witness_concrete
