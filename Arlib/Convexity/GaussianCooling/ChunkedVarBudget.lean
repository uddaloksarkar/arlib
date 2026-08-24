/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.Schedule
import Arlib.Convexity.GaussianCooling.Variance
import Arlib.Convexity.GaussianCooling.Chain

/-!
# The chunked, variance-adaptive variance budget (Cousins–Vempala)

Work in progress: the crux first.
-/

namespace Arlib.GaussianCooling.Chunked

open scoped BigOperators

/-! ## Numeric input -/

/-- `e^t ≤ 1 + c·t` for `1 < c` and `0 ≤ t ≤ (c−1)/c`.  Via `e^t ≤ (1−t)⁻¹ ≤ 1 + c·t`.
The `c = 2` case is `Arlib.GaussianCooling.exp_le_one_add_two_mul`; the chunked accounting
needs `c = 5/4` and `c = 7/6`, where the admissible range of `t` shrinks accordingly. -/
theorem exp_le_one_add_mul {c t : ℝ} (hc : 1 < c) (ht0 : 0 ≤ t) (ht : t ≤ (c - 1) / c) :
    Real.exp t ≤ 1 + c * t := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hct : c * t ≤ c - 1 := by
    rw [le_div_iff₀ hc0] at ht; linarith
  have ht1 : t < 1 := by nlinarith
  have h1 : (0 : ℝ) < 1 - t := by linarith
  have hinv : Real.exp t ≤ (1 - t)⁻¹ := by
    rw [le_inv_comm₀ (Real.exp_pos t) h1, ← Real.exp_neg]
    linarith [Real.add_one_le_exp (-t)]
  have h2 : (1 - t)⁻¹ ≤ 1 + c * t := by
    rw [inv_le_iff_one_le_mul₀ h1]
    nlinarith [mul_nonneg ht0 (show (0 : ℝ) ≤ c - 1 - c * t by linarith)]
  linarith

/-- `(1 + x)^p ≤ e^{p·x}` for `0 ≤ x`. -/
theorem one_add_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (p : ℕ) :
    (1 + x) ^ p ≤ Real.exp ((p : ℝ) * x) := by
  have hstep : (1 + x) ^ p ≤ (Real.exp x) ^ p :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) p
  rw [Real.exp_nat_mul]
  exact hstep

/-! ## The crux: `σ` cancels inside a chunk -/

/-- **The `σ`-cancellation, in the paper's form** (`1409.6011/vol3_journal.tex`,
`lem:accuracy`, the display after `claim:fast-var-bound`).

A chunk is the set of phases until `σ²` doubles.  Its per-phase relative-second-moment
excess is `2σ²/(k·N)` with `N = C²n` and `k` the number of sample points per phase, and it
has at most `2N/σ²` phases.  Then

  `(1 + 2σ²/(kN))^p ≤ 1 + 5/k`   whenever `p ≤ 2N/σ²`.

**`σ` cancels**: the per-phase excess is proportional to `σ²` and the number of phases is
proportional to `1/σ²`, so a chunk costs `O(1/k)` no matter where it sits.  This is the
whole reason the accelerated (variance-adaptive) rate `α = σ²/(2C²n)` is affordable, i.e.
the reason the algorithm is `O*(n³)` and not `O*(n⁴)`.

`k ≥ 20` is what the numeric step `e^{4/k} ≤ 1 + 5/k` needs (it is false at `k = 9`); in the
algorithm `k` is `Θ(n log²(nR²)/ε²)`, so this is never a constraint. -/
theorem chunk_var_bound {p : ℕ} {k N σsq : ℝ} (hk : 20 ≤ k) (hN : 0 < N) (hσ : 0 < σsq)
    (hp : (p : ℝ) ≤ 2 * N / σsq) :
    (1 + 2 * σsq / (k * N)) ^ p ≤ 1 + 5 / k := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hx0 : (0 : ℝ) ≤ 2 * σsq / (k * N) := by positivity
  -- `p·x ≤ (2N/σ²)·(2σ²/(kN)) = 4/k`
  have hpx : (p : ℝ) * (2 * σsq / (k * N)) ≤ 4 / k := by
    have h := mul_le_mul_of_nonneg_right hp hx0
    have heq : 2 * N / σsq * (2 * σsq / (k * N)) = 4 / k := by
      field_simp; ring
    rwa [heq] at h
  -- `e^{4/k} ≤ 1 + (5/4)·(4/k) = 1 + 5/k`
  have hnum : Real.exp (4 / k) ≤ 1 + 5 / k := by
    have ht : 4 / k ≤ ((5 : ℝ) / 4 - 1) / (5 / 4) := by
      rw [show ((5 : ℝ) / 4 - 1) / (5 / 4) = 1 / 5 by norm_num, div_le_div_iff₀ hk0 (by norm_num)]
      linarith
    have h := exp_le_one_add_mul (c := 5 / 4) (t := 4 / k) (by norm_num) (by positivity) ht
    have heq : (1 : ℝ) + 5 / 4 * (4 / k) = 1 + 5 / k := by ring
    linarith [heq ▸ h]
  calc (1 + 2 * σsq / (k * N)) ^ p ≤ Real.exp ((p : ℝ) * (2 * σsq / (k * N))) :=
        one_add_pow_le_exp hx0 p
    _ ≤ Real.exp (4 / k) := Real.exp_le_exp.2 hpx
    _ ≤ 1 + 5 / k := hnum

/-- **The paper's chunk bound is false if the phase count is rounded *up*.**

`lem:accuracy` writes the exponent as `2C²n/σ²`, an upper bound on the number of phases in
the chunk, and the bound `1 + 5/k` is correct for that exponent (`chunk_var_bound`).  It is
**not** correct for `⌈2C²n/σ²⌉`: at `N = C²n = 100`, `σ² = 99`, `k = 100` the ceiling is `3`
while `2N/σ² = 2.02…`, and

  `(1 + 198/10000)³ = 1.0605… > 1.05 = 1 + 5/k`.

So a *constructive* schedule, which must use an integer number of phases per chunk, cannot
use the constant `5`; `chunk_var_bound_ceil` pays `7` instead. -/
theorem not_chunk_var_bound_ceil_five :
    ¬ ((1 + 2 * (99 : ℝ) / (100 * 100)) ^ (⌈2 * (100 : ℝ) / 99⌉₊) ≤ 1 + 5 / 100) := by
  have hceil : (⌈2 * (100 : ℝ) / 99⌉₊) = 3 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [hceil]
  norm_num

/-- **The `σ`-cancellation with an integer phase count.**  With `p = ⌈2N/σ²⌉` — the count a
schedule can actually use — the same argument gives `1 + 7/k` in place of `1 + 5/k`, at the
cost of `k ≥ 42` instead of `k ≥ 20`.  The extra `2/k` is the single extra phase the
ceiling can add, whose excess is `2σ²/(kN) ≤ 2/k` because `σ² ≤ N`.

`not_chunk_var_bound_ceil_five` shows the constant `5` is unavailable here. -/
theorem chunk_var_bound_ceil {k N σsq : ℝ} (hk : 42 ≤ k) (hN : 0 < N) (hσ0 : 0 < σsq)
    (hσN : σsq ≤ N) :
    (1 + 2 * σsq / (k * N)) ^ (⌈2 * N / σsq⌉₊) ≤ 1 + 7 / k := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hx0 : (0 : ℝ) ≤ 2 * σsq / (k * N) := by positivity
  set p : ℕ := ⌈2 * N / σsq⌉₊ with hpdef
  have hple : (p : ℝ) ≤ 2 * N / σsq + 1 := by
    have := Nat.ceil_lt_add_one (a := 2 * N / σsq) (by positivity)
    rw [← hpdef] at this
    linarith
  -- `x ≤ 2/k`, since `σ² ≤ N`
  have hxle : 2 * σsq / (k * N) ≤ 2 / k := by
    rw [div_le_div_iff₀ (by positivity) hk0]
    nlinarith
  have hpx : (p : ℝ) * (2 * σsq / (k * N)) ≤ 6 / k := by
    have h := mul_le_mul_of_nonneg_right hple hx0
    have heq : (2 * N / σsq + 1) * (2 * σsq / (k * N))
        = 4 / k + 2 * σsq / (k * N) := by
      field_simp; ring
    rw [heq] at h
    have : (4 : ℝ) / k + 2 * σsq / (k * N) ≤ 4 / k + 2 / k := by linarith
    have h6 : (4 : ℝ) / k + 2 / k = 6 / k := by ring
    linarith
  have hnum : Real.exp (6 / k) ≤ 1 + 7 / k := by
    have ht : 6 / k ≤ ((7 : ℝ) / 6 - 1) / (7 / 6) := by
      rw [show ((7 : ℝ) / 6 - 1) / (7 / 6) = 1 / 7 by norm_num, div_le_div_iff₀ hk0 (by norm_num)]
      linarith
    have h := exp_le_one_add_mul (c := 7 / 6) (t := 6 / k) (by norm_num) (by positivity) ht
    have heq : (1 : ℝ) + 7 / 6 * (6 / k) = 1 + 7 / k := by ring
    linarith [heq ▸ h]
  calc (1 + 2 * σsq / (k * N)) ^ p ≤ Real.exp ((p : ℝ) * (2 * σsq / (k * N))) :=
        one_add_pow_le_exp hx0 p
    _ ≤ Real.exp (6 / k) := Real.exp_le_exp.2 hpx
    _ ≤ 1 + 7 / k := hnum

/-! ## The chunked, variance-adaptive schedule

The schedule is built chunk by chunk.  Chunk `j` starts at the nominal variance
`s_j = 2^j·s₀`, runs at the **variance-adaptive** rate `a_j = s_j/(2N)` (Cousins–Vempala's
`α = σ²/(2C²n)`, with `N = C²n`) for `p_j = ⌈2N/s_j⌉ = ⌈1/a_j⌉` phases, and ends at a
variance at least `2s_j = s_{j+1}` (`two_le_chunkCool`).  So the rate **doubles from chunk
to chunk**: cooling accelerates as `σ` grows, which is exactly the mechanism the fixed rate
`α = 1/n` lacks. -/

/-- The nominal variance at the start of chunk `j`: `s_j = 2^j·s₀`. -/
noncomputable def chunkStart (s₀ : ℝ) (j : ℕ) : ℝ := 2 ^ j * s₀

/-- The cooling rate used throughout chunk `j`: Cousins–Vempala's `α = σ²/(2C²n)` evaluated
at the chunk's starting variance, with `N = C²n`. -/
noncomputable def chunkRate (N s₀ : ℝ) (j : ℕ) : ℝ := chunkStart s₀ j / (2 * N)

/-- The number of phases in chunk `j`: `⌈1/a_j⌉ = ⌈2N/s_j⌉`, the paper's `2C²n/σ²` rounded
up to an integer. -/
noncomputable def chunkPhases (N s₀ : ℝ) (j : ℕ) : ℕ := ⌈2 * N / chunkStart s₀ j⌉₊

/-- The **cooling factor** of chunk `j`: `(1 + a_j)^{p_j}`, i.e. `σ_end²/σ_start²` for the
geometric segment the chunk runs (`chunk_eq_geomSchedule`). -/
noncomputable def chunkCool (N s₀ : ℝ) (j : ℕ) : ℝ :=
  (1 + chunkRate N s₀ j) ^ chunkPhases N s₀ j

/-- The **variance factor** of chunk `j`: the paper's
`(1 + 2σ²/(kC²n))^{#phases}` at `σ² = s_j`, `C²n = N`.  `chunkStep_estimator_factor_le`
proves this is an upper bound for the actual per-phase estimator factor
`1 + (E(Y²)/E(Y)² − 1)/k` along the chunk. -/
noncomputable def chunkVar (k N s₀ : ℝ) (j : ℕ) : ℝ :=
  (1 + 2 * chunkStart s₀ j / (k * N)) ^ chunkPhases N s₀ j

theorem chunkStart_pos {s₀ : ℝ} (hs : 0 < s₀) (j : ℕ) : 0 < chunkStart s₀ j :=
  mul_pos (by positivity) hs

theorem chunkStart_succ (s₀ : ℝ) (j : ℕ) :
    chunkStart s₀ (j + 1) = 2 * chunkStart s₀ j := by
  unfold chunkStart; ring

theorem chunkRate_pos {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    0 < chunkRate N s₀ j :=
  div_pos (chunkStart_pos hs j) (by linarith)

/-- `p_j · a_j ≥ 1`: the chunk is long enough for Bernoulli to double the variance.  This is
`Nat.le_ceil` and nothing else. -/
theorem one_le_chunkPhases_mul_rate {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    1 ≤ (chunkPhases N s₀ j : ℝ) * chunkRate N s₀ j := by
  have hs0 := chunkStart_pos hs j
  have ha0 := chunkRate_pos hN hs j
  have hceil : 2 * N / chunkStart s₀ j ≤ (chunkPhases N s₀ j : ℝ) := Nat.le_ceil _
  have hone : 2 * N / chunkStart s₀ j * chunkRate N s₀ j = 1 := by
    unfold chunkRate
    field_simp
  nlinarith

/-- **Each chunk really doubles the variance.**  `(1 + a_j)^{p_j} ≥ 2`, by Bernoulli
(`1 + p·a ≤ (1+a)^p`) and `p_j·a_j ≥ 1`. -/
theorem two_le_chunkCool {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    2 ≤ chunkCool N s₀ j := by
  have ha0 := chunkRate_pos hN hs j
  have hb := one_add_mul_le_pow (a := chunkRate N s₀ j) (by linarith) (chunkPhases N s₀ j)
  have := one_le_chunkPhases_mul_rate hN hs j
  unfold chunkCool
  linarith

/-- **The chunk is a geometric segment of the repo's `geomSchedule`**, and it reaches the
next chunk's nominal start: `s_{j+1} ≤ geomSchedule s_j a_j p_j`.  So the chunks concatenate
into one increasing variance schedule whose rate is `a_j` on chunk `j`. -/
theorem chunkStart_succ_le_geomSchedule {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    chunkStart s₀ (j + 1)
      ≤ geomSchedule (chunkStart s₀ j) (chunkRate N s₀ j) (chunkPhases N s₀ j) := by
  have hs0 := chunkStart_pos hs j
  have h := two_le_chunkCool hN hs j
  unfold geomSchedule
  rw [chunkStart_succ]
  have : chunkStart s₀ j * 2 ≤ chunkStart s₀ j * chunkCool N s₀ j :=
    mul_le_mul_of_nonneg_left h hs0.le
  unfold chunkCool at this
  linarith

/-- **The chunked variance budget, per chunk.**  `chunk_var_bound_ceil` at the chunk's own
starting variance: as long as the chunk starts below the top variance `N = C²n`, its
variance factor is at most `1 + 7/k` — *independently of `j`*.  This is the `σ`-cancellation
in the form the schedule uses. -/
theorem chunkVar_le {k N s₀ : ℝ} (hk : 42 ≤ k) (hN : 0 < N) (hs : 0 < s₀) {j : ℕ}
    (hjN : chunkStart s₀ j ≤ N) :
    chunkVar k N s₀ j ≤ 1 + 7 / k :=
  chunk_var_bound_ceil hk hN (chunkStart_pos hs j) hjN

theorem chunkVar_nonneg {k N s₀ : ℝ} (hk : 0 < k) (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    0 ≤ chunkVar k N s₀ j := by
  have hs0 := chunkStart_pos hs j
  refine pow_nonneg ?_ _
  have : (0 : ℝ) ≤ 2 * chunkStart s₀ j / (k * N) := by positivity
  linarith

/-! ## The product over chunks -/

/-- **Total cooling over `J` chunks is at least `2^J`.**  Each chunk doubles
(`two_le_chunkCool`); there is no upper bound of the `< 11/10` kind that
`Arlib.GaussianCooling.geomSchedule_total_cooling_lt` forces on the fixed rate. -/
theorem pow_two_le_prod_chunkCool {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (J : ℕ) :
    (2 : ℝ) ^ J ≤ ∏ j ∈ Finset.range J, chunkCool N s₀ j := by
  have h : ∏ _j ∈ Finset.range J, (2 : ℝ) ≤ ∏ j ∈ Finset.range J, chunkCool N s₀ j :=
    Finset.prod_le_prod (fun _ _ => by norm_num) (fun j _ => two_le_chunkCool hN hs j)
  simpa using h

/-- Every chunk before the last starts below the top variance `N`, given `2^J·s₀ ≤ 2N`. -/
theorem chunkStart_le_of_fit {N s₀ : ℝ} (hs : 0 < s₀) {J : ℕ} (hfit : 2 ^ J * s₀ ≤ 2 * N)
    {j : ℕ} (hj : j < J) : chunkStart s₀ j ≤ N := by
  have h2' : (2 : ℝ) ^ j * 2 ≤ 2 ^ J := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by norm_num) hj
  have := mul_le_mul_of_nonneg_right h2' hs.le
  unfold chunkStart
  nlinarith

/-- **Total variance cost over `J` chunks is at most `(1 + 7/k)^J`.**  The paper's
`(1 + 5/k)^{log C²n}` factor, with the constant `5` replaced by `7` because a constructive
schedule must round the per-chunk phase count up (`not_chunk_var_bound_ceil_five`).

Note what is *not* here: any dependence on where the chunks sit, i.e. on `σ`. -/
theorem prod_chunkVar_le {k N s₀ : ℝ} {J : ℕ} (hk : 42 ≤ k) (hN : 0 < N) (hs : 0 < s₀)
    (hfit : 2 ^ J * s₀ ≤ 2 * N) :
    ∏ j ∈ Finset.range J, chunkVar k N s₀ j ≤ (1 + 7 / k) ^ J := by
  have hk0 : (0 : ℝ) < k := by linarith
  have h : ∏ j ∈ Finset.range J, chunkVar k N s₀ j ≤ ∏ _j ∈ Finset.range J, (1 + 7 / k) :=
    Finset.prod_le_prod (fun j _ => chunkVar_nonneg hk0 hN hs j)
      (fun j hj => chunkVar_le hk hN hs (chunkStart_le_of_fit hs hfit (Finset.mem_range.1 hj)))
  simpa using h

/-! ## A genuinely concatenated schedule

The nominal `chunkStart` values above are ideal comparison points.  Because
`chunkPhases` rounds up, a chunk can end *strictly above* its next nominal comparison
point.  Consequently, restarting the next segment at `chunkStart s₀ (j+1)` would insert a
downward jump and would not be an annealing schedule.

The definitions below remove that artefact.  The first chunk starts at `s₀`, and every
later chunk starts at the **actual endpoint** of the preceding geometric segment.  This is
the concrete concatenation that can eventually be flattened into the phase index of the
volume estimator.
-/

/-- The first phase count at which the fixed-rate segment starting at `s` has doubled.
Outside the positive-parameter regime it defaults to `0`; all theorems below work under
`0 < N` and `0 < s`, where the crossing exists. -/
noncomputable def chunkCrossingPhases (N s : ℝ) : ℕ :=
  by
    classical
    exact if h : ∃ p : ℕ, 2 * s ≤ geomSchedule s (s / (2 * N)) p then Nat.find h else 0

/-- The paper's rounded upper bound is a phase by which a positive chunk has doubled. -/
theorem ceil_crosses_chunk {N s : ℝ} (hN : 0 < N) (hs : 0 < s) :
    2 * s ≤ geomSchedule s (s / (2 * N)) ⌈2 * N / s⌉₊ := by
  let p : ℕ := ⌈2 * N / s⌉₊
  have hceil : 2 * N / s ≤ (p : ℝ) := Nat.le_ceil _
  have ha0 : 0 ≤ s / (2 * N) := (div_pos hs (mul_pos (by norm_num) hN)).le
  have hpa : 1 ≤ (p : ℝ) * (s / (2 * N)) := by
    have hone : 2 * N / s * (s / (2 * N)) = 1 := by field_simp
    nlinarith
  have hbern := one_add_mul_le_pow (a := s / (2 * N)) (by linarith) p
  unfold geomSchedule
  have hcool : 2 ≤ (1 + s / (2 * N)) ^ p := by linarith
  change 2 * s ≤ s * (1 + s / (2 * N)) ^ p
  nlinarith

/-- A positive chunk always reaches twice its starting variance. -/
theorem chunk_crossing_exists {N s : ℝ} (hN : 0 < N) (hs : 0 < s) :
    ∃ p : ℕ, 2 * s ≤ geomSchedule s (s / (2 * N)) p :=
  ⟨⌈2 * N / s⌉₊, ceil_crosses_chunk hN hs⟩

/-- The chosen crossing phase really doubles the segment. -/
theorem chunkCrossingPhases_spec {N s : ℝ} (hN : 0 < N) (hs : 0 < s) :
    2 * s ≤ geomSchedule s (s / (2 * N)) (chunkCrossingPhases N s) := by
  have hex := chunk_crossing_exists hN hs
  rw [chunkCrossingPhases, dif_pos hex]
  exact Nat.find_spec hex

/-- Every phase strictly before `chunkCrossingPhases` is still below twice the chunk's
starting variance.  This is the fact the source uses when replacing the current `σ²` by
`2s` in its per-phase variance factor. -/
theorem geomSchedule_lt_two_mul_of_lt_crossing {N s : ℝ} (hN : 0 < N) (hs : 0 < s)
    {t : ℕ} (ht : t < chunkCrossingPhases N s) :
    geomSchedule s (s / (2 * N)) t < 2 * s := by
  have hex := chunk_crossing_exists hN hs
  have hnot : ¬ 2 * s ≤ geomSchedule s (s / (2 * N)) t := by
    intro ht_cross
    have hmin := Nat.find_min' hex ht_cross
    rw [chunkCrossingPhases, dif_pos hex] at ht
    omega
  exact lt_of_not_ge hnot

/-- The first crossing occurs no later than the paper's rounded phase bound. -/
theorem chunkCrossingPhases_le_ceil {N s : ℝ} (hN : 0 < N) (hs : 0 < s) :
    chunkCrossingPhases N s ≤ ⌈2 * N / s⌉₊ := by
  have hex := chunk_crossing_exists hN hs
  rw [chunkCrossingPhases, dif_pos hex]
  exact Nat.find_min' hex (ceil_crosses_chunk hN hs)

/-- Actual variance at the start of chunk `j`.  The successor is the endpoint of the
preceding geometric segment, so no reset or discontinuity is hidden in this definition. -/
noncomputable def adaptiveChunkStart (N s₀ : ℝ) : ℕ → ℝ
  | 0 => s₀
  | j + 1 =>
      let s := adaptiveChunkStart N s₀ j
      geomSchedule s (s / (2 * N)) (chunkCrossingPhases N s)

/-- Rate of the actual chunk `j`. -/
noncomputable def adaptiveChunkRate (N s₀ : ℝ) (j : ℕ) : ℝ :=
  adaptiveChunkStart N s₀ j / (2 * N)

/-- Number of phases of the actual chunk `j`. -/
noncomputable def adaptiveChunkPhases (N s₀ : ℝ) (j : ℕ) : ℕ :=
  chunkCrossingPhases N (adaptiveChunkStart N s₀ j)

/-- Cooling factor of the actual chunk `j`. -/
noncomputable def adaptiveChunkCool (N s₀ : ℝ) (j : ℕ) : ℝ :=
  (1 + adaptiveChunkRate N s₀ j) ^ adaptiveChunkPhases N s₀ j

/-- Variance-product contribution of actual chunk `j`, after averaging `k` samples in
each phase and using the paper's within-chunk bound. -/
noncomputable def adaptiveChunkVar (k N s₀ : ℝ) (j : ℕ) : ℝ :=
  (1 + 2 * adaptiveChunkStart N s₀ j / (k * N)) ^
    adaptiveChunkPhases N s₀ j

/-- Actual per-phase variance factor used in the source's chunk product.  The input
variance is the local geometric schedule, not merely the chunk's comparison start. -/
noncomputable def adaptivePhaseVarFactor (k N s₀ : ℝ) (j t : ℕ) : ℝ :=
  1 + geomSchedule (adaptiveChunkStart N s₀ j) (adaptiveChunkRate N s₀ j) t / (k * N)

/-- Product of the actual local variance factors in chunk `j`. -/
noncomputable def adaptiveChunkActualVar (k N s₀ : ℝ) (j : ℕ) : ℝ :=
  ∏ t ∈ Finset.range (adaptiveChunkPhases N s₀ j), adaptivePhaseVarFactor k N s₀ j t

/-- The defining concatenation equation: the next chunk starts at the exact endpoint of
the current one. -/
theorem adaptiveChunkStart_succ (N s₀ : ℝ) (j : ℕ) :
    adaptiveChunkStart N s₀ (j + 1) =
      geomSchedule (adaptiveChunkStart N s₀ j) (adaptiveChunkRate N s₀ j)
        (adaptiveChunkPhases N s₀ j) := by
  simp [adaptiveChunkStart, adaptiveChunkRate, adaptiveChunkPhases]

/-- The same concatenation equation, factored into the chunk cooling factor. -/
theorem adaptiveChunkStart_succ_eq_mul (N s₀ : ℝ) (j : ℕ) :
    adaptiveChunkStart N s₀ (j + 1) =
      adaptiveChunkStart N s₀ j * adaptiveChunkCool N s₀ j := by
  rw [adaptiveChunkStart_succ]
  rfl

/-- Every actual chunk start is positive. -/
theorem adaptiveChunkStart_pos {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) :
    ∀ j : ℕ, 0 < adaptiveChunkStart N s₀ j := by
  intro j
  induction j with
  | zero => simpa [adaptiveChunkStart] using hs
  | succ j ih =>
      rw [adaptiveChunkStart_succ]
      have ha : 0 < adaptiveChunkRate N s₀ j := by
        unfold adaptiveChunkRate
        exact div_pos ih (mul_pos (by norm_num) hN)
      exact geomSchedule_pos ih (by linarith) _

/-- Every actual chunk rate is positive. -/
theorem adaptiveChunkRate_pos {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    0 < adaptiveChunkRate N s₀ j := by
  unfold adaptiveChunkRate
  exact div_pos (adaptiveChunkStart_pos hN hs j) (mul_pos (by norm_num) hN)

/-- Before the terminal variance `N`, every chunk rate is at most `1/2` (and hence below
`1`), as required by the general-rate Gaussian second-moment estimate. -/
theorem adaptiveChunkRate_le_half {N s₀ : ℝ} (hN : 0 < N) {j : ℕ}
    (hjN : adaptiveChunkStart N s₀ j ≤ N) : adaptiveChunkRate N s₀ j ≤ 1 / 2 := by
  unfold adaptiveChunkRate
  rw [div_le_iff₀ (mul_pos (by norm_num) hN)]
  nlinarith

theorem adaptiveChunkRate_lt_one {N s₀ : ℝ} (hN : 0 < N) {j : ℕ}
    (hjN : adaptiveChunkStart N s₀ j ≤ N) : adaptiveChunkRate N s₀ j < 1 :=
  lt_of_le_of_lt (adaptiveChunkRate_le_half hN hjN) (by norm_num)

/-- The actual chunk has a positive number of phases. -/
theorem adaptiveChunkPhases_pos {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    0 < adaptiveChunkPhases N s₀ j := by
  have hspec := chunkCrossingPhases_spec hN (adaptiveChunkStart_pos hN hs j)
  unfold adaptiveChunkPhases
  by_contra hzero
  have hz : chunkCrossingPhases N (adaptiveChunkStart N s₀ j) = 0 := by omega
  rw [hz, geomSchedule_zero] at hspec
  linarith [adaptiveChunkStart_pos hN hs j]

/-- The actual endpoint follows the advertised constant rate at every phase in chunk
`j`; this is the phase-level rate equation consumed by the Gaussian-cooling lemmas. -/
theorem adaptiveChunk_geom_succ {N s₀ : ℝ} (_hN : 0 < N) (_hs : 0 < s₀) (j t : ℕ) :
    geomSchedule (adaptiveChunkStart N s₀ j) (adaptiveChunkRate N s₀ j) (t + 1) =
      geomSchedule (adaptiveChunkStart N s₀ j) (adaptiveChunkRate N s₀ j) t *
        (1 + adaptiveChunkRate N s₀ j) := by
  simp only [geomSchedule, pow_succ]
  ring

/-- Every actual chunk cools by at least a factor two. -/
theorem two_le_adaptiveChunkCool {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    2 ≤ adaptiveChunkCool N s₀ j := by
  have hs0 := adaptiveChunkStart_pos hN hs j
  have hspec := chunkCrossingPhases_spec hN hs0
  unfold geomSchedule at hspec
  unfold adaptiveChunkCool adaptiveChunkRate adaptiveChunkPhases
  have hspec' : adaptiveChunkStart N s₀ j * 2 ≤
      adaptiveChunkStart N s₀ j *
        (1 + adaptiveChunkStart N s₀ j / (2 * N)) ^
          chunkCrossingPhases N (adaptiveChunkStart N s₀ j) := by
    simpa [mul_comm] using hspec
  exact (mul_le_mul_iff_of_pos_left hs0).mp hspec'

/-- Every phase before the endpoint of an actual chunk has variance below twice that
chunk's start. -/
theorem adaptiveChunk_phase_lt_two {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) {j t : ℕ}
    (ht : t < adaptiveChunkPhases N s₀ j) :
    geomSchedule (adaptiveChunkStart N s₀ j) (adaptiveChunkRate N s₀ j) t <
      2 * adaptiveChunkStart N s₀ j := by
  exact geomSchedule_lt_two_mul_of_lt_crossing hN (adaptiveChunkStart_pos hN hs j) ht

/-- Chunk starts at least double from one actual chunk to the next. -/
theorem two_mul_adaptiveChunkStart_le_succ {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀)
    (j : ℕ) :
    2 * adaptiveChunkStart N s₀ j ≤ adaptiveChunkStart N s₀ (j + 1) := by
  rw [adaptiveChunkStart_succ_eq_mul]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left (two_le_adaptiveChunkCool hN hs j)
      (adaptiveChunkStart_pos hN hs j).le

/-- After `J` concatenated chunks the variance has grown by at least `2^J`. -/
theorem pow_two_mul_le_adaptiveChunkStart {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) :
    ∀ J : ℕ, (2 : ℝ) ^ J * s₀ ≤ adaptiveChunkStart N s₀ J := by
  intro J
  induction J with
  | zero => simp [adaptiveChunkStart]
  | succ J ih =>
      rw [pow_succ]
      calc
        (2 : ℝ) ^ J * 2 * s₀ = 2 * ((2 : ℝ) ^ J * s₀) := by ring
        _ ≤ 2 * adaptiveChunkStart N s₀ J := by linarith
        _ ≤ adaptiveChunkStart N s₀ (J + 1) :=
          two_mul_adaptiveChunkStart_le_succ hN hs J

/-- Exact telescoping of the cooling factors of the concatenated schedule. -/
theorem adaptiveChunkStart_eq_start_mul_prod (N s₀ : ℝ) : ∀ J : ℕ,
    adaptiveChunkStart N s₀ J =
      s₀ * ∏ j ∈ Finset.range J, adaptiveChunkCool N s₀ j := by
  intro J
  induction J with
  | zero => simp [adaptiveChunkStart]
  | succ J ih =>
      rw [adaptiveChunkStart_succ_eq_mul, ih, Finset.prod_range_succ]
      ring

/-- The constructive `1+7/k` variance bound for each actual chunk. -/
theorem adaptiveChunkVar_le {k N s₀ : ℝ} (hk : 42 ≤ k) (hN : 0 < N) (hs : 0 < s₀)
    {j : ℕ} (hjN : adaptiveChunkStart N s₀ j ≤ N) :
    adaptiveChunkVar k N s₀ j ≤ 1 + 7 / k := by
  have hs0 := adaptiveChunkStart_pos hN hs j
  have hbase : 1 ≤ 1 + 2 * adaptiveChunkStart N s₀ j / (k * N) := by
    have hk0 : 0 < k := by linarith
    have : 0 ≤ 2 * adaptiveChunkStart N s₀ j / (k * N) := by positivity
    linarith
  have hp := chunkCrossingPhases_le_ceil hN hs0
  calc
    adaptiveChunkVar k N s₀ j ≤
        (1 + 2 * adaptiveChunkStart N s₀ j / (k * N)) ^
          ⌈2 * N / adaptiveChunkStart N s₀ j⌉₊ := by
      unfold adaptiveChunkVar adaptiveChunkPhases
      exact pow_le_pow_right₀ hbase hp
    _ ≤ 1 + 7 / k := chunk_var_bound_ceil hk hN hs0 hjN

/-- Nonnegativity needed to multiply the per-chunk bounds. -/
theorem adaptiveChunkVar_nonneg {k N s₀ : ℝ} (hk : 0 < k) (hN : 0 < N) (hs : 0 < s₀)
    (j : ℕ) : 0 ≤ adaptiveChunkVar k N s₀ j := by
  unfold adaptiveChunkVar
  refine pow_nonneg ?_ _
  have : (0 : ℝ) ≤ 2 * adaptiveChunkStart N s₀ j / (k * N) :=
    div_nonneg (mul_nonneg (by norm_num) (adaptiveChunkStart_pos hN hs j).le)
      (mul_nonneg hk.le hN.le)
  linarith

/-- The source's actual product inside a chunk is bounded by `adaptiveChunkVar`.  The key
step is `adaptiveChunk_phase_lt_two`, which is why chunks stop at the *first* doubling
time rather than at the rounded upper bound. -/
theorem adaptiveChunkActualVar_le {k N s₀ : ℝ} (hk : 0 < k) (hN : 0 < N) (hs : 0 < s₀)
    (j : ℕ) : adaptiveChunkActualVar k N s₀ j ≤ adaptiveChunkVar k N s₀ j := by
  have hden : 0 < k * N := mul_pos hk hN
  have hprod :
      ∏ t ∈ Finset.range (adaptiveChunkPhases N s₀ j), adaptivePhaseVarFactor k N s₀ j t ≤
        ∏ _t ∈ Finset.range (adaptiveChunkPhases N s₀ j),
          (1 + 2 * adaptiveChunkStart N s₀ j / (k * N)) :=
    Finset.prod_le_prod
      (fun t ht => by
        unfold adaptivePhaseVarFactor
        have hσt := geomSchedule_pos
          (σ₀sq := adaptiveChunkStart N s₀ j) (α := adaptiveChunkRate N s₀ j)
          (adaptiveChunkStart_pos hN hs j)
          (by linarith [adaptiveChunkRate_pos hN hs j]) t
        have : 0 ≤
            geomSchedule (adaptiveChunkStart N s₀ j) (adaptiveChunkRate N s₀ j) t /
              (k * N) := div_nonneg hσt.le hden.le
        linarith)
      (fun t ht => by
        unfold adaptivePhaseVarFactor
        have hphase := adaptiveChunk_phase_lt_two hN hs (Finset.mem_range.1 ht)
        have hdiv :
            geomSchedule (adaptiveChunkStart N s₀ j) (adaptiveChunkRate N s₀ j) t /
                (k * N) ≤
              2 * adaptiveChunkStart N s₀ j / (k * N) :=
          (div_le_div_iff_of_pos_right hden).2 hphase.le
        linarith)
  unfold adaptiveChunkActualVar adaptiveChunkVar
  simpa using hprod

/-- Total accelerated-regime variance product.  The hypothesis says that all chunks that
are actually run start before the terminal variance `N`; unlike the nominal construction,
this theorem refers to the exact recursive starts and hence contains no hidden reset. -/
theorem prod_adaptiveChunkVar_le {k N s₀ : ℝ} {J : ℕ} (hk : 42 ≤ k) (hN : 0 < N)
    (hs : 0 < s₀) (hbelow : ∀ j < J, adaptiveChunkStart N s₀ j ≤ N) :
    ∏ j ∈ Finset.range J, adaptiveChunkVar k N s₀ j ≤ (1 + 7 / k) ^ J := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hprod :
      ∏ j ∈ Finset.range J, adaptiveChunkVar k N s₀ j ≤
        ∏ _j ∈ Finset.range J, (1 + 7 / k) :=
    Finset.prod_le_prod (fun j _ => adaptiveChunkVar_nonneg hk0 hN hs j)
      (fun j hj => adaptiveChunkVar_le hk hN hs (hbelow j (Finset.mem_range.1 hj)))
  simpa using hprod

/-- The chunk product fits an exponential variance budget `κ` once the sample count obeys
`7J ≤ kκ`.  This is the exact arithmetic interface needed by the product-estimator step
of `lem:accuracy`; combining it with `exp κ - 1 ≤ ε²/5` gives the Chebyshev budget. -/
theorem prod_adaptiveChunkVar_le_exp {k N s₀ κ : ℝ} {J : ℕ} (hk : 42 ≤ k) (hN : 0 < N)
    (hs : 0 < s₀) (hbelow : ∀ j < J, adaptiveChunkStart N s₀ j ≤ N)
    (hsamples : 7 * (J : ℝ) ≤ k * κ) :
    ∏ j ∈ Finset.range J, adaptiveChunkVar k N s₀ j ≤ Real.exp κ := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hx0 : (0 : ℝ) ≤ 7 / k := by positivity
  have harg : (J : ℝ) * (7 / k) ≤ κ := by
    rw [show (J : ℝ) * (7 / k) = (7 * (J : ℝ)) / k by ring]
    rw [div_le_iff₀ hk0]
    nlinarith
  calc
    ∏ j ∈ Finset.range J, adaptiveChunkVar k N s₀ j ≤ (1 + 7 / k) ^ J :=
      prod_adaptiveChunkVar_le hk hN hs hbelow
    _ ≤ Real.exp ((J : ℝ) * (7 / k)) := one_add_pow_le_exp hx0 J
    _ ≤ Real.exp κ := Real.exp_le_exp.2 harg

/-- Full two-level product from `lem:accuracy`: actual per-phase factors, grouped into
actual chunks, fit the exponential variance budget. -/
theorem prod_adaptiveChunkActualVar_le_exp {k N s₀ κ : ℝ} {J : ℕ} (hk : 42 ≤ k)
    (hN : 0 < N) (hs : 0 < s₀) (hbelow : ∀ j < J, adaptiveChunkStart N s₀ j ≤ N)
    (hsamples : 7 * (J : ℝ) ≤ k * κ) :
    ∏ j ∈ Finset.range J, adaptiveChunkActualVar k N s₀ j ≤ Real.exp κ := by
  have hk0 : (0 : ℝ) < k := by linarith
  calc
    ∏ j ∈ Finset.range J, adaptiveChunkActualVar k N s₀ j ≤
        ∏ j ∈ Finset.range J, adaptiveChunkVar k N s₀ j :=
      Finset.prod_le_prod
        (fun j _ => by
          unfold adaptiveChunkActualVar
          exact Finset.prod_nonneg fun t ht => by
            unfold adaptivePhaseVarFactor
            have hσt := geomSchedule_pos
              (σ₀sq := adaptiveChunkStart N s₀ j) (α := adaptiveChunkRate N s₀ j)
              (adaptiveChunkStart_pos hN hs j)
              (by linarith [adaptiveChunkRate_pos hN hs j]) t
            have : 0 ≤
                geomSchedule (adaptiveChunkStart N s₀ j) (adaptiveChunkRate N s₀ j) t /
                  (k * N) := by positivity
            linarith)
        (fun j _ => adaptiveChunkActualVar_le hk0 hN hs j)
    _ ≤ Real.exp κ := prod_adaptiveChunkVar_le_exp hk hN hs hbelow hsamples

/-- Total number of accelerated phases in `J` actual chunks. -/
noncomputable def adaptiveTotalPhases (N s₀ : ℝ) (J : ℕ) : ℕ :=
  ∑ j ∈ Finset.range J, adaptiveChunkPhases N s₀ j

/-- A phase-count bound with the exact ceiling correction.  It is stated as the sum of
the reciprocal actual starts; the following corollary turns this into a geometric bound. -/
theorem adaptiveTotalPhases_le_sum {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (J : ℕ) :
    (adaptiveTotalPhases N s₀ J : ℝ) ≤
      ∑ j ∈ Finset.range J, (2 * N / adaptiveChunkStart N s₀ j + 1) := by
  unfold adaptiveTotalPhases
  push_cast
  exact Finset.sum_le_sum fun j hj => by
    have hpos : 0 < 2 * N / adaptiveChunkStart N s₀ j :=
      div_pos (mul_pos (by norm_num) hN) (adaptiveChunkStart_pos hN hs j)
    have h := Nat.ceil_lt_add_one (a := 2 * N / adaptiveChunkStart N s₀ j) hpos.le
    have hp := chunkCrossingPhases_le_ceil hN (adaptiveChunkStart_pos hN hs j)
    calc
      (adaptiveChunkPhases N s₀ j : ℝ) ≤
          (⌈2 * N / adaptiveChunkStart N s₀ j⌉₊ : ℝ) := by
        unfold adaptiveChunkPhases
        exact_mod_cast hp
      _ ≤ 2 * N / adaptiveChunkStart N s₀ j + 1 := h.le

/-- The reciprocal phase-count contribution falls by at least a factor two from one
actual chunk to the next. -/
theorem two_mul_recip_succ_le_recip {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    2 * (2 * N / adaptiveChunkStart N s₀ (j + 1)) ≤
      2 * N / adaptiveChunkStart N s₀ j := by
  have hden := two_mul_adaptiveChunkStart_le_succ hN hs j
  have hdiv : 2 * N / adaptiveChunkStart N s₀ (j + 1) ≤
      2 * N / (2 * adaptiveChunkStart N s₀ j) :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hN.le)
      (mul_pos (by norm_num) (adaptiveChunkStart_pos hN hs j)) hden
  have heq : 2 * N / (2 * adaptiveChunkStart N s₀ j) =
      (2 * N / adaptiveChunkStart N s₀ j) / 2 := by
    field_simp
  rw [heq] at hdiv
  linarith

/-- Geometric-series invariant for the reciprocal chunk starts. -/
theorem sum_recip_add_tail_le {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) : ∀ J : ℕ,
    (∑ j ∈ Finset.range J, 2 * N / adaptiveChunkStart N s₀ j) +
        2 * (2 * N / adaptiveChunkStart N s₀ J) ≤ 4 * N / s₀ := by
  intro J
  induction J with
  | zero =>
      simp [adaptiveChunkStart]
      ring_nf
      exact le_rfl
  | succ J ih =>
      rw [Finset.sum_range_succ]
      have hhalf := two_mul_recip_succ_le_recip hN hs J
      linarith

/-- The sum of the reciprocal actual chunk starts is at most its infinite geometric-series
bound `4N/s₀`. -/
theorem sum_recip_le {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (J : ℕ) :
    ∑ j ∈ Finset.range J, 2 * N / adaptiveChunkStart N s₀ j ≤ 4 * N / s₀ := by
  have h := sum_recip_add_tail_le hN hs J
  have htail : 0 ≤ 2 * (2 * N / adaptiveChunkStart N s₀ J) := by
    exact mul_nonneg (by norm_num)
      (div_nonneg (mul_nonneg (by norm_num) hN.le) (adaptiveChunkStart_pos hN hs J).le)
  linarith

/-- The phase count is at most `4N/s₀ + J`.  This is the finite geometric-series form of
the paper's `O(N/s₀)` accelerated-regime phase count, with one extra phase per chunk from
integer rounding. -/
theorem adaptiveTotalPhases_le {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (J : ℕ) :
    (adaptiveTotalPhases N s₀ J : ℝ) ≤ 4 * N / s₀ + J := by
  have hsum := adaptiveTotalPhases_le_sum hN hs J
  have hrecip := sum_recip_le hN hs J
  have hone :
      (∑ j ∈ Finset.range J, (2 * N / adaptiveChunkStart N s₀ j + 1)) =
        (∑ j ∈ Finset.range J, 2 * N / adaptiveChunkStart N s₀ j) + J := by
    rw [Finset.sum_add_distrib]
    simp
  rw [hone] at hsum
  exact hsum.trans (by linarith)

/-! ## Axiom audit -/

#print axioms adaptiveChunkStart_pos
#print axioms adaptiveChunkStart_succ_eq_mul
#print axioms adaptiveChunkRate_lt_one
#print axioms two_le_adaptiveChunkCool
#print axioms pow_two_mul_le_adaptiveChunkStart
#print axioms prod_adaptiveChunkVar_le
#print axioms prod_adaptiveChunkVar_le_exp
#print axioms prod_adaptiveChunkActualVar_le_exp
#print axioms adaptiveTotalPhases_le

end Arlib.GaussianCooling.Chunked
