/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.HoldingTime
import Arlib.MarkovChains.Continuous.HitAndRunMixing
import Arlib.MarkovChains.Continuous.EllFloor
import Arlib.Convexity.LogConcaveIso

/-!
# The polynomial bound transfers to the ball walk — at the `s`-conductance

`Arlib/MarkovChains/Continuous/SpeedyToUniform.lean` proves polynomial-time mixing for the
**lazy speedy walk**, whose stationary measure is `Arlib.MarkovChains.ellProb K δ`.  The
kernel a volume sampler in this repository actually iterates is the **lazy ball walk**,
`Arlib.MarkovChains.lazy (Arlib.MarkovChains.ballWalk K δ)`, whose stationary measure is
already exactly `Arlib.uniformOn volume K`.  This file asks whether the speedy walk's
polynomial conductance bound transfers to it, and answers: **yes, with constant exactly `1`,
provided the sets of relative volume below the smoothness parameter are discarded** — that is,
at the level of the `s`-conductance, not the conductance.

## The obstruction, and why the `s`-discount removes it

`Arlib/MarkovChains/Continuous/HoldingTime.lean` already proves the **exact conductance
relation** (`conductanceOn_ballWalk_mul_volume_inter`, and its normalised twin):

    Φ_ball(A) · vol(A ∩ K)  =  Φ_speedy(A) · ellMeasure(A),

i.e. `Φ_ball(A) = Φ_speedy(A) · avg_A(ℓ)` where `avg_A(ℓ) = (∫_{A∩K} ℓ)/vol(A ∩ K)`.  That
average is exponentially small for a set hugging a sharp corner of `K`
(`Arlib.MarkovChains.ell_cube_corner_le`, `EllFloor.lean`: `ℓ ≤ 2⁻ⁿ` at the corner of
`[-1,1]ⁿ`, at **every** step size).  So no polynomial lower bound on the *ordinary*
conductance of the ball walk can exist for the class of convex bodies:
`conductance_ballWalk_uniformOn_le_of_ell_le` below is that statement, machine-checked.

The repair is the Lovász–Simonovits `s`-conductance, already defined in this repository as
`Arlib.MarkovChains.conductanceS` (`HitAndRunMixing.lean`),

    Φ_s = inf { flow(S,Sᶜ) / (π(S) − s) : s < π(S) ≤ 1/2 },

with the *unnormalised* flow in the numerator and the *discounted* mass `π(S) − s` in the
denominator.  The point of this file is that **the discount pays for the smoothness deficit
exactly**: `IsSmooth K δ sm` says `∫_K ℓ ≥ (1 − sm)·vol(K)`, hence
`ellMeasure(S) ≥ vol(S ∩ K) − sm·vol(K)` for *every* `S` (`volume_inter_le_ellMeasure_add`),
hence `flow_π(S,Sᶜ) ≥ Φ_speedy · (π(S) − sm)`, and dividing by `π(S) − s ≤ π(S) − sm` gives
back `Φ_speedy` with **no loss at all** whenever `sm ≤ s`.  There is no `1 − sm/s` factor and
no `1 − sm` factor: the normalising constant `∫_K ℓ` cancels between the flow and the mass.

## Main results

**The crux** (`§2`).

* `Arlib.MarkovChains.mul_sub_le_flow_ballWalk` —
  `Φ_speedy · (vol(S ∩ K) − sm·vol(K)) ≤ flow (ballWalk K δ) (vol|_K) S Sᶜ`
  for every measurable `S` with `2·vol(S ∩ K) ≤ vol(K)`.  No convexity.

**The transfer** (`§3`).

* `Arlib.MarkovChains.le_conductanceSOn_ballWalk_uniformOn` — setwise:
  `Φ_speedy ≤ Φ_s(ballWalk K δ, uniformOn volume K)(S)` for `S ∈ MidSets` and `sm ≤ s`.
* `Arlib.MarkovChains.le_conductanceS_ballWalk_uniformOn` — the infimum form,
  `Φ_speedy ≤ Φ_s(ballWalk K δ, uniformOn volume K)`.
* `Arlib.MarkovChains.le_conductanceS_lazy_ballWalk_uniformOn` — the same for the **lazy**
  ball walk, at `Φ_speedy/2`; `conductanceSOn_lazy` proves the factor `2` is exact.

**The polynomial instantiation, fully discharged** (`§4`).

* `Arlib.MarkovChains.le_conductanceS_lazy_ballWalk_of_ball_subset` — for a convex body with
  `B(0,1) ⊆ K ⊆ B(0,R)`, `2 ≤ n`, `0 < δ < 1` and every `s ≥ 1 − (1−δ)ⁿ`,

      min(1/16, (1/(8R))·(δ/(2n))/64) / 2  ≤  Φ_s(lazy (ballWalk K δ), uniformOn volume K).

  **No binders.**  `Arlib.hiso_ellProb_of_ball_bound` (`Arlib/Convexity/LogConcaveIso.lean`)
  supplies the isoperimetric input at `κ = 1/(8R)`,
  `Arlib.MarkovChains.conductance_speedyWalk_ge` turns it into the speedy conductance bound,
  and `Arlib.MarkovChains.isSmooth_of_ball_subset` supplies `sm = 1 − (1−δ)ⁿ`.

**The obstruction, machine-checked** (`§5`).

* `Arlib.MarkovChains.conductanceOn_ballWalk_le_of_ell_le` — `ℓ ≤ c` on `A ∩ K` forces
  `Φ_ball(A) ≤ c`.
* `Arlib.MarkovChains.conductance_ballWalk_uniformOn_le_of_ell_le` — hence
  `conductance (ballWalk K δ) (uniformOn volume K) ≤ c` if one admissible set is bad.

**Total variation** (`§6`).

* `Arlib.MarkovChains.tvLe_iterate_lazy_ballWalk_of_sConductance` — composed with
  `Arlib.MarkovChains.tvLe_iterate_of_sConductance`.  **Conditional**: it inherits that
  theorem's `hLSs` binder, the Lovász–Simonovits `s`-conductance decay bound, which is *not*
  proved in this repository and is *false on a space with atoms* (see `HitAndRunMixing.lean`,
  `§ A non-vacuity witness for the hLSs binder`).

**Non-vacuity** (`§7`).

* `Arlib.MarkovChains.exists_ballWalkTransfer_witness` — for `2 ≤ n` and `0 < δ ≤ 1/(4n)` the
  unit ball satisfies every guard at once, with `phi > 0`, `sm ≤ s = 1/4`, and a member of
  `MidSets (uniformOn volume K) s` (the concentric ball of relative volume exactly `1/2`,
  `uniformOn_unitBall_halfVolumeBall`), so `conductanceS` is not the empty infimum `⊤`.

## What is *not* proved

1. **No mixing-time or runtime claim.**  Everything in `§§2–5` is about conductance.  `§6` is
   a total-variation statement conditional on an unproved binder.  Nothing here says how long
   any sampler runs.
2. **No machine-checked positive-measure exponential lower bound on the loss.**  The
   obstruction is proved as an *implication* (`conductanceOn_ballWalk_le_of_ell_le`), and
   `EllFloor.lean` proves `ℓ ≤ 2⁻ⁿ` only **pointwise** at the cube's corner.  A single point
   is Lebesgue-null, so the two do not compose into "`conductance (ballWalk cube δ) ≤ 2⁻ⁿ`".
   Establishing that needs a positive-measure corner neighbourhood on which `ℓ` is
   exponentially small, which nothing in this repository proves.
3. **The threshold is not free.**  `s ≥ 1 − (1−δ)ⁿ ≈ nδ`.  A consumer needing a small `s`
   must take `δ` small, and `δ` is a factor in the bound, so the step count grows like
   `δ⁻² = Θ((n/s)²)`.  This is the same genre of trade-off as the arithmetic route of
   `SpeedyToUniform.lean`; what the `s`-conductance route removes is the *bias* (the ball
   walk's stationary measure is exactly uniform, so there is no `s/(1−s)` floor on the error),
   not the `δ`-dependence.

## Scope

**No `def`, `structure`, `class` or named `Prop` is introduced anywhere in this file.**  Every
declaration is a `theorem`.  Every hypothesis is an inline hypothesis of the theorem that
consumes it.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 0. `s`-conductance bookkeeping -/

section General

variable {Om : Type*} [MeasurableSpace Om]

/-- **Laziness halves the `s`-conductance of every set, exactly**, for every threshold `s`:

    Φ_s(lazy P)(S) = Φ_s(P)(S) / 2.

Same proof as `Arlib.MarkovChains.conductanceOn_lazy`: the holding term of `flow_lazy` is
charged `pi (Sᶜ ∩ S) = pi ∅ = 0`, so only the factor `1/2` survives, and the discounted
denominator `pi S - s` is untouched because `lazy P` has the same stationary measure. -/
theorem conductanceSOn_lazy (P : Kernel Om Om) (pi : Measure Om) (s : ℝ≥0∞) {S : Set Om}
    (hS : MeasurableSet S) :
    conductanceSOn (lazy P) pi s S = conductanceSOn P pi s S / 2 := by
  rw [conductanceSOn, conductanceSOn, flow_lazy P pi S hS.compl, Set.compl_inter_self,
    measure_empty, mul_zero, add_zero, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **A setwise `s`-conductance bound is an `s`-conductance bound.**  `conductanceS` is the
infimum of `conductanceSOn` over `MidSets pi s`, so bounding every member bounds it.

This is the `s`-analogue of `Arlib.MarkovChains.le_conductance`, and is *not*
`Arlib.MarkovChains.le_conductanceS`, which routes through the ordinary conductance and
therefore requires a bound valid for **every** set of mass in `(0, 1/2]` — exactly what the
ball walk does not have. -/
theorem le_conductanceS_of_forall_midSets (P : Kernel Om Om) (pi : Measure Om) (s c : ℝ≥0∞)
    (h : ∀ S : Set Om, MeasurableSet S → s < pi S → pi S ≤ 1 / 2 →
      c ≤ conductanceSOn P pi s S) :
    c ≤ conductanceS P pi s :=
  le_iInf₂ fun _ hS => h _ hS.1 hS.2.1 hS.2.2

/-- **The `s`-conductance is at most the `s`-conductance of any admissible set.** -/
theorem conductanceS_le_conductanceSOn (P : Kernel Om Om) (pi : Measure Om) {s : ℝ≥0∞}
    {S : Set Om} (hS : MeasurableSet S) (hSs : s < pi S) (hShalf : pi S ≤ 1 / 2) :
    conductanceS P pi s ≤ conductanceSOn P pi s S :=
  iInf₂_le S ⟨hS, hSs, hShalf⟩

/-- **A reversible chain's escape flow is at least `Φ · min(π S, π Sᶜ)`**, with no positivity
hypothesis on `S`.

This is the standard "the conductance infimum is really over `min(π S, π Sᶜ)`" statement.  The
degenerate cases are free: if either side of the `min` is `0` the left-hand side is `0`.  For
`π S ≤ 1/2` the bound is `conductance_le_conductanceOn` read as a product; for `π S > 1/2` it
is the same statement at `Sᶜ`, transported by detailed balance
(`flow P pi S Sᶜ = flow P pi Sᶜ S`). -/
theorem mul_min_le_flow_of_le_conductance {P : Kernel Om Om} [IsMarkovKernel P]
    {pi : Measure Om} [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {phi : ℝ≥0∞}
    (hphi : phi ≤ conductance P pi) {S : Set Om} (hS : MeasurableSet S) :
    phi * min (pi S) (pi Sᶜ) ≤ flow P pi S Sᶜ := by
  have hsum : pi S + pi Sᶜ = 1 := by rw [measure_add_measure_compl hS, measure_univ]
  rcases eq_or_ne (min (pi S) (pi Sᶜ)) 0 with h0 | h0
  · rw [h0, mul_zero]
    exact zero_le
  have hS0 : pi S ≠ 0 := fun h => h0 (le_antisymm (h ▸ min_le_left _ _) zero_le)
  have hSc0 : pi Sᶜ ≠ 0 := fun h => h0 (le_antisymm (h ▸ min_le_right _ _) zero_le)
  rcases le_or_gt (pi S) (1 / 2) with hle | hgt
  · have hmin : min (pi S) (pi Sᶜ) = pi S := by
      refine min_eq_left ?_
      have hstep : pi S + pi S ≤ pi S + pi Sᶜ := by
        calc pi S + pi S ≤ 1 / 2 + 1 / 2 := by gcongr
          _ = 1 := ENNReal.add_halves 1
          _ = pi S + pi Sᶜ := hsum.symm
      exact (ENNReal.add_le_add_iff_left (measure_ne_top pi S)).1 hstep
    rw [hmin]
    have hd : phi ≤ flow P pi S Sᶜ / pi S :=
      hphi.trans (conductance_le_conductanceOn P pi hS (pos_iff_ne_zero.2 hS0) hle)
    calc phi * pi S ≤ (flow P pi S Sᶜ / pi S) * pi S := by gcongr
      _ = flow P pi S Sᶜ := ENNReal.div_mul_cancel hS0 (measure_ne_top pi S)
  · have hchalf : pi Sᶜ ≤ 1 / 2 := by
      have hstep : 1 / 2 + pi Sᶜ ≤ pi S + pi Sᶜ := by gcongr
      have h1 : 1 / 2 + pi Sᶜ ≤ 1 / 2 + 1 / 2 := by
        calc 1 / 2 + pi Sᶜ ≤ pi S + pi Sᶜ := hstep
          _ = 1 := hsum
          _ = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
      exact (ENNReal.add_le_add_iff_left (by simp)).1 h1
    have hmin : min (pi S) (pi Sᶜ) = pi Sᶜ := min_eq_right (hchalf.trans hgt.le)
    rw [hmin, hrev S Sᶜ hS hS.compl]
    have hd : phi ≤ flow P pi Sᶜ S / pi Sᶜ := by
      have := hphi.trans
        (conductance_le_conductanceOn P pi hS.compl (pos_iff_ne_zero.2 hSc0) hchalf)
      rwa [conductanceOn, compl_compl] at this
    calc phi * pi Sᶜ ≤ (flow P pi Sᶜ S / pi Sᶜ) * pi Sᶜ := by gcongr
      _ = flow P pi Sᶜ S := ENNReal.div_mul_cancel hSc0 (measure_ne_top pi Sᶜ)

end General

/-! ## 1. Smoothness is a bound on the `ell`-deficit of *every* set -/

/-- **The localised form of `IsSmooth`.**  For every measurable `S`,

    vol(S ∩ K)  ≤  ellMeasure K δ S  +  s · vol(K).

Assumes `IsSmooth K δ s`, `s ≤ 1` and `vol K ≠ ⊤`; no convexity, no positivity of `δ`.

`IsSmooth K δ s` is a statement about the average of `ell` over `K` only.  This lemma is the
observation that the *global* deficit `vol(K) - ∫_K ell ≤ s·vol(K)` dominates the *local*
deficit `vol(S ∩ K) - ∫_{S∩K} ell` of every `S` at once
(`Arlib.MarkovChains.ellMeasure_add_volume_le`).  It is therefore useless for sets of volume
below `s·vol(K)` — which is precisely the class the `s`-conductance discards. -/
theorem volume_inter_le_ellMeasure_add {K : Set (EuclideanSpace ℝ (Fin n))} (δ : ℝ)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) {sm : ℝ≥0∞}
    (hsm : IsSmooth K δ sm) (hsm1 : sm ≤ 1) (hKtop : volume K ≠ ⊤) :
    volume (S ∩ K) ≤ ellMeasure K δ S + sm * volume K := by
  have h1 : volume (S ∩ K) + ellMeasure K δ Set.univ ≤ ellMeasure K δ S + volume K :=
    ellMeasure_add_volume_le K δ hS
  have h2 : (1 - sm) * volume K ≤ ellMeasure K δ Set.univ := ellMeasure_univ_ge_of_isSmooth hsm
  have hsplit : volume K = sm * volume K + (1 - sm) * volume K := by
    rw [← add_mul, add_tsub_cancel_of_le hsm1, one_mul]
  have hfin : (1 - sm) * volume K ≠ ⊤ := by
    refine ne_top_of_le_ne_top hKtop ?_
    calc (1 - sm) * volume K ≤ 1 * volume K := by gcongr; exact tsub_le_self
      _ = volume K := one_mul _
  refine (ENNReal.add_le_add_iff_right hfin).1 ?_
  calc volume (S ∩ K) + (1 - sm) * volume K
      ≤ volume (S ∩ K) + ellMeasure K δ Set.univ := by gcongr
    _ ≤ ellMeasure K δ S + volume K := h1
    _ = ellMeasure K δ S + sm * volume K + (1 - sm) * volume K := by
        rw [add_assoc, ← hsplit]

/-! ## 2. The crux: the ball walk's escape flow, from below -/

/-- **The crux.**  For every measurable `S` occupying at most half of `K`,

    Φ_speedy · (vol(S ∩ K) − s·vol(K))  ≤  flow (ballWalk K δ) (vol|_K) S Sᶜ,

where `Φ_speedy` is any lower bound for `conductance (speedyWalk K δ) (ellProb K δ)` and `s`
is any smoothness parameter of `K` at step `δ`.

Assumes `MeasurableSet K`, `0 < δ`, `0 < vol K < ⊤`, `IsSmooth K δ s`, `s ≤ 1`, and
`2·vol(S ∩ K) ≤ vol(K)`.  No convexity.

The proof is three exact identities and one inequality:

* `flow_ballWalk_compl_eq_flow_speedyWalk` — the two chains have the *same* unnormalised
  escape flow (`HoldingTime.lean`);
* `flow_smul_measure` — rescaling `ellMeasure` to `ellProb` rescales the flow by `L = ∫_K ell`;
* `mul_min_le_flow_of_le_conductance` — the speedy walk's conductance bound in product form;
* `volume_inter_le_ellMeasure_add` — `L·ellProb(S) = ellMeasure(S) ≥ vol(S ∩ K) − s·vol(K)`,
  and the same at `Sᶜ`, which is larger because `S` occupies at most half of `K`.

The normalising constant `L` cancels exactly: the flow carries a factor `L` and the mass
`ellProb` carries `L⁻¹`.  **Nothing is lost to the smoothness deficit except the additive
`s·vol(K)`** — there is no multiplicative `(1-s)` anywhere. -/
theorem mul_sub_le_flow_ballWalk {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {δ : ℝ} (hδ : 0 < δ) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {sm : ℝ≥0∞}
    (hsm : IsSmooth K δ sm) (hsm1 : sm ≤ 1) {phi : ℝ≥0∞}
    (hphi : phi ≤ conductance (speedyWalk K δ) (ellProb K δ))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (hhalf : 2 * volume (S ∩ K) ≤ volume K) :
    phi * (volume (S ∩ K) - sm * volume K)
      ≤ flow (ballWalk K δ) (volume.restrict K) S Sᶜ := by
  haveI : IsProbabilityMeasure (ellProb K δ) :=
    isProbabilityMeasure_ellProb_of_volume hK hK0 hKtop hδ
  set L : ℝ≥0∞ := ellMeasure K δ Set.univ with hLdef
  have hL0 : L ≠ 0 := ellMeasure_univ_ne_zero hK hK0 hδ
  have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top hKtop (ellMeasure_univ_le K δ)
  -- the two flows agree, and rescaling the stationary measure rescales the flow
  have hflow : flow (ballWalk K δ) (volume.restrict K) S Sᶜ
      = L * flow (speedyWalk K δ) (ellProb K δ) S Sᶜ := by
    rw [flow_ballWalk_compl_eq_flow_speedyWalk hK δ hS, ellProb, flow_smul_measure,
      ← mul_assoc, ENNReal.mul_inv_cancel hL0 hLtop, one_mul]
  -- the speedy walk's conductance bound, in product form
  have hmin : phi * min (ellProb K δ S) (ellProb K δ Sᶜ)
      ≤ flow (speedyWalk K δ) (ellProb K δ) S Sᶜ :=
    mul_min_le_flow_of_le_conductance (isReversible_speedyWalk_prob hK δ) hphi hS
  -- `L · ellProb T = ellMeasure T`
  have hLmul : ∀ T : Set (EuclideanSpace ℝ (Fin n)), L * ellProb K δ T = ellMeasure K δ T := by
    intro T
    rw [ellProb, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel hL0 hLtop, one_mul]
  -- the two mass bounds
  have hmass1 : volume (S ∩ K) - sm * volume K ≤ L * ellProb K δ S := by
    rw [hLmul]
    exact tsub_le_iff_right.2 (volume_inter_le_ellMeasure_add δ hS hsm hsm1 hKtop)
  have hmass2 : volume (S ∩ K) - sm * volume K ≤ L * ellProb K δ Sᶜ := by
    rw [hLmul]
    have hcompl : Sᶜ ∩ K = K \ S := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
      tauto
    have hsplit : volume (S ∩ K) + volume (Sᶜ ∩ K) = volume K := by
      have h := measure_inter_add_sdiff (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) K hS
      rw [Set.inter_comm K S] at h
      rw [hcompl]
      exact h
    have hle : volume (S ∩ K) ≤ volume (Sᶜ ∩ K) := by
      have hfin : volume (S ∩ K) ≠ ⊤ :=
        ne_top_of_le_ne_top hKtop (measure_mono Set.inter_subset_right)
      refine (ENNReal.add_le_add_iff_left hfin).1 ?_
      calc volume (S ∩ K) + volume (S ∩ K) = 2 * volume (S ∩ K) := by ring
        _ ≤ volume K := hhalf
        _ = volume (S ∩ K) + volume (Sᶜ ∩ K) := hsplit.symm
    calc volume (S ∩ K) - sm * volume K ≤ volume (Sᶜ ∩ K) - sm * volume K :=
          tsub_le_tsub_right hle _
      _ ≤ ellMeasure K δ Sᶜ :=
          tsub_le_iff_right.2 (volume_inter_le_ellMeasure_add δ hS.compl hsm hsm1 hKtop)
  have hmono : Monotone (fun x : ℝ≥0∞ => L * x) := fun _ _ h => mul_le_mul_left' h L
  have hmm : min (L * ellProb K δ S) (L * ellProb K δ Sᶜ)
      = L * min (ellProb K δ S) (ellProb K δ Sᶜ) := hmono.map_min.symm
  calc phi * (volume (S ∩ K) - sm * volume K)
      ≤ phi * min (L * ellProb K δ S) (L * ellProb K δ Sᶜ) := by
        gcongr
        exact le_min hmass1 hmass2
    _ = L * (phi * min (ellProb K δ S) (ellProb K δ Sᶜ)) := by
        rw [hmm]; ring
    _ ≤ L * flow (speedyWalk K δ) (ellProb K δ) S Sᶜ := by gcongr
    _ = flow (ballWalk K δ) (volume.restrict K) S Sᶜ := hflow.symm

/-! ## 3. The `s`-conductance of the ball walk, set by set and in the infimum -/

/-- **`2 · (1/2) = 1` in `ℝ≥0∞`.** -/
theorem two_mul_one_half : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
  rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

/-- **The transfer, set by set.**  For every measurable `S` with

    s < uniformOn volume K S ≤ 1/2      (i.e. `S ∈ MidSets (uniformOn volume K) s`)

and every smoothness parameter `sm ≤ s` of `K` at step `δ`,

    Φ_speedy  ≤  Φ_s(ballWalk K δ, uniformOn volume K)(S) = flow(S,Sᶜ)/(π(S) − s).

Assumes `MeasurableSet K`, `0 < δ`, `0 < vol K < ⊤`, `IsSmooth K δ sm`, `sm ≤ 1`, `sm ≤ s`,
and a conductance bound `phi ≤ conductance (speedyWalk K δ) (ellProb K δ)`.  **No convexity**
— convexity enters only when the speedy bound and the smoothness certificate are produced.

**There is no loss.**  `mul_sub_le_flow_ballWalk` gives
`flow_π(S,Sᶜ) ≥ phi · (π(S) − sm)`, and the `s`-conductance denominator is `π(S) − s`, which
is *smaller* because `sm ≤ s`.  The smoothness deficit is absorbed exactly by the
`s`-discount: the transfer constant is `1`, not `1 − sm/s`, and not `(1 − sm)`.

Contrast `Arlib.MarkovChains.conductanceOn_ballWalk_le_conductanceOn_speedyWalk`
(`HoldingTime.lean`), which says the *undiscounted* conductances satisfy
`Φ_ball(A) ≤ Φ_speedy(A)`, with the loss equal to the average of `ell` over `A` — a loss that
is genuinely exponential for a set hugging a corner of `K`.  Discarding the sets of mass
below `s` is exactly what removes it. -/
theorem le_conductanceSOn_ballWalk_uniformOn {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {sm : ℝ≥0∞} (hsm : IsSmooth K δ sm) (hsm1 : sm ≤ 1) {phi : ℝ≥0∞}
    (hphi : phi ≤ conductance (speedyWalk K δ) (ellProb K δ)) {s : ℝ≥0∞} (hs : sm ≤ s)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (hSs : s < Arlib.uniformOn volume K S) (hShalf : Arlib.uniformOn volume K S ≤ 1 / 2) :
    phi ≤ conductanceSOn (ballWalk K δ) (Arlib.uniformOn volume K) s S := by
  have hpiS : Arlib.uniformOn volume K S = (volume K)⁻¹ * volume (S ∩ K) := by
    rw [Arlib.uniformOn_def, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS]
  have hVpi : volume K * Arlib.uniformOn volume K S = volume (S ∩ K) := by
    rw [hpiS, ← mul_assoc, ENNReal.mul_inv_cancel hK0 hKtop, one_mul]
  have hhalf : 2 * volume (S ∩ K) ≤ volume K := by
    have hstep : volume K * Arlib.uniformOn volume K S ≤ volume K * (1 / 2) := by gcongr
    rw [hVpi] at hstep
    calc 2 * volume (S ∩ K) ≤ 2 * (volume K * (1 / 2)) := by gcongr
      _ = volume K * (2 * (1 / 2)) := by ring
      _ = volume K := by rw [two_mul_one_half, mul_one]
  have hd0 : Arlib.uniformOn volume K S - s ≠ 0 := (tsub_pos_of_lt hSs).ne'
  have hdtop : Arlib.uniformOn volume K S - s ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_le_ne_top (by norm_num) hShalf) tsub_le_self
  have hflowpi : flow (ballWalk K δ) (Arlib.uniformOn volume K) S Sᶜ
      = (volume K)⁻¹ * flow (ballWalk K δ) (volume.restrict K) S Sᶜ := by
    rw [Arlib.uniformOn_def, flow_smul_measure]
  rw [conductanceSOn, ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdtop), hflowpi]
  have hexp : volume K * (Arlib.uniformOn volume K S - s) = volume (S ∩ K) - s * volume K := by
    rw [ENNReal.mul_sub (fun _ _ => hKtop), hVpi, mul_comm (volume K) s]
  have hkey : volume K * (phi * (Arlib.uniformOn volume K S - s))
      ≤ flow (ballWalk K δ) (volume.restrict K) S Sᶜ := by
    calc volume K * (phi * (Arlib.uniformOn volume K S - s))
        = phi * (volume K * (Arlib.uniformOn volume K S - s)) := by ring
      _ = phi * (volume (S ∩ K) - s * volume K) := by rw [hexp]
      _ ≤ phi * (volume (S ∩ K) - sm * volume K) := by gcongr
      _ ≤ flow (ballWalk K δ) (volume.restrict K) S Sᶜ :=
          mul_sub_le_flow_ballWalk hK hδ hK0 hKtop hsm hsm1 hphi hS hhalf
  calc phi * (Arlib.uniformOn volume K S - s)
      = (volume K)⁻¹ * (volume K * (phi * (Arlib.uniformOn volume K S - s))) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hK0 hKtop, one_mul]
    _ ≤ (volume K)⁻¹ * flow (ballWalk K δ) (volume.restrict K) S Sᶜ := by gcongr

/-- **The polynomial bound lands on the ball walk, at the `s`-conductance.**

    Φ_speedy  ≤  Φ_s(ballWalk K δ, uniformOn volume K)      for every `s ≥ sm`,

where `sm` is any `(δ, sm)`-smoothness parameter of `K`.

Assumes `MeasurableSet K`, `0 < δ`, `0 < vol K < ⊤`, `IsSmooth K δ sm`, `sm ≤ 1`, `sm ≤ s`,
and `phi ≤ conductance (speedyWalk K δ) (ellProb K δ)`.

This is the theorem that answers the question "does the polynomial bound transfer?".  It does,
**with constant exactly `1`**, provided the small sets are discarded at a threshold at least
the smoothness parameter.  It cannot be improved to the ordinary conductance: see
`conductanceOn_ballWalk_le_of_ell_le` below and `Arlib.MarkovChains.ell_cube_corner_le`
(`EllFloor.lean`). -/
theorem le_conductanceS_ballWalk_uniformOn {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {sm : ℝ≥0∞} (hsm : IsSmooth K δ sm) (hsm1 : sm ≤ 1) {phi : ℝ≥0∞}
    (hphi : phi ≤ conductance (speedyWalk K δ) (ellProb K δ)) {s : ℝ≥0∞} (hs : sm ≤ s) :
    phi ≤ conductanceS (ballWalk K δ) (Arlib.uniformOn volume K) s :=
  le_conductanceS_of_forall_midSets _ _ _ _ fun _ hSm hSs hShalf =>
    le_conductanceSOn_ballWalk_uniformOn hK hδ hK0 hKtop hsm hsm1 hphi hs hSm hSs hShalf

/-- **The same bound for the kernel a sampler actually runs**, the *lazy* ball walk:

    Φ_speedy / 2  ≤  Φ_s(lazy (ballWalk K δ), uniformOn volume K)      for every `s ≥ sm`.

Assumes exactly the hypotheses of `le_conductanceS_ballWalk_uniformOn`.  The factor `2` is the
exact cost of laziness (`conductanceSOn_lazy`), not a slack.

`Arlib.MarkovChains.lazy (Arlib.MarkovChains.ballWalk K δ)` is the kernel iterated by the
volume sampler in this repository; this theorem is a statement about that kernel's
`s`-conductance and about nothing else.  It is **not** a mixing-time or a runtime claim. -/
theorem le_conductanceS_lazy_ballWalk_uniformOn {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {sm : ℝ≥0∞} (hsm : IsSmooth K δ sm) (hsm1 : sm ≤ 1) {phi : ℝ≥0∞}
    (hphi : phi ≤ conductance (speedyWalk K δ) (ellProb K δ)) {s : ℝ≥0∞} (hs : sm ≤ s) :
    phi / 2 ≤ conductanceS (lazy (ballWalk K δ)) (Arlib.uniformOn volume K) s := by
  refine le_conductanceS_of_forall_midSets _ _ _ _ fun S hSm hSs hShalf => ?_
  rw [conductanceSOn_lazy _ _ _ hSm]
  gcongr
  exact le_conductanceSOn_ballWalk_uniformOn hK hδ hK0 hKtop hsm hsm1 hphi hs hSm hSs hShalf

/-! ## 4. The polynomial instantiation, with every binder discharged -/

/-- **The polynomial `s`-conductance bound for the lazy ball walk on a convex body.**

For a convex body `K` with `B(0,1) ⊆ K ⊆ B(0,R)` and a step `0 < δ < 1`,

    min(1/16, (1/(8R))·(δ/2n)/64) / 2  ≤  Φ_s(lazy (ballWalk K δ), uniformOn volume K)

for every threshold `s ≥ 1 − (1−δ)ⁿ`.

**Every hypothesis is discharged**; the only inputs are `2 ≤ n`, `0 < R`, `0 < δ < 1`,
measurability, convexity, the inball and the circumradius.  In particular there is no
isoperimetry binder: `Arlib.hiso_ellProb_of_ball_bound` (`Arlib/Convexity/LogConcaveIso.lean`)
supplies `κ = 1/(8R)`, `Arlib.MarkovChains.conductance_speedyWalk_ge` (`SpeedyWalk.lean`)
turns it into the speedy walk's conductance bound, and
`Arlib.MarkovChains.isSmooth_of_ball_subset` (`EllFloor.lean`) supplies the smoothness
parameter `1 − (1−δ)ⁿ`.

The bound is `Θ(δ/(nR))` — **polynomial in `n`**, in contrast with the `2⁻ⁿ`-type constant
that `Arlib.MarkovChains.conductance_ballWalk_ge` (`BallWalkConductance.lean`) certifies for
the *undiscounted* conductance of the same kernel.  The two are consistent: the undiscounted
conductance really is exponentially small (`conductanceOn_ballWalk_le_of_ell_le` below), and
the `s`-discount is what removes the offending sets.

**Read the threshold honestly.**  `s ≥ 1 − (1−δ)ⁿ ≈ nδ`, so the sets discarded have relative
volume up to about `nδ`.  Any consumer that needs a small `s` must take `δ` small, and `δ`
sits in the bound as a factor. -/
theorem le_conductanceS_lazy_ballWalk_of_ball_subset (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {R : ℝ} (hR : 0 < R)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {s : ℝ≥0∞}
    (hs : 1 - ENNReal.ofReal ((1 - δ) ^ n) ≤ s) :
    min (1 / 16) (ENNReal.ofReal (1 / (8 * R)) * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64) / 2
      ≤ conductanceS (lazy (ballWalk K δ)) (Arlib.uniformOn volume K) s := by
  have hK0 : volume K ≠ 0 := by
    have h1 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤ volume K :=
      measure_mono hball
    exact ((Metric.measure_ball_pos volume 0 one_pos).trans_le h1).ne'
  have hKtop : volume K ≠ ⊤ := by
    have hsub : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hKR x hx
    exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hsub)
  exact le_conductanceS_lazy_ballWalk_uniformOn hK hδ hK0 hKtop
    (isSmooth_of_ball_subset hK hconv hball hδ hδ1) tsub_le_self
    (conductance_speedyWalk_ge (by omega) hK hconv hK0 hKtop hδ
      (Arlib.hiso_ellProb_of_ball_bound hn hR hδ hK hconv hKR hK0)) hs

/-! ## 5. The obstruction, stated exactly: why the `s`-discount is not optional -/

/-- **The ball walk's conductance is at most the local conductance of the set it is measured
on.**  If `ell K δ ≤ c` everywhere on `A ∩ K` then

    Φ_ball(A)  ≤  c.

Assumes `MeasurableSet K`, `MeasurableSet A`, `vol K ≠ ⊤` and `vol(A ∩ K) ≠ 0`.

This is the exact obstruction.  `Arlib.MarkovChains.conductanceOn_ballWalk_mul_volume_inter`
(`HoldingTime.lean`) says `Φ_ball(A)·vol(A ∩ K) = Φ_speedy(A)·ellMeasure(A)`; bounding
`Φ_speedy(A) ≤ 1` (it is a probability) and `ellMeasure(A) ≤ c·vol(A ∩ K)` gives the claim.

Combined with `Arlib.MarkovChains.ell_cube_corner_le` (`EllFloor.lean`: `ell ≤ 2⁻ⁿ` at the
corner of the cube `[-1,1]ⁿ`, at **every** step size `δ`), this is the reason the *ordinary*
conductance of the ball walk cannot be bounded below by anything better than `2⁻ⁿ` on a body
with a sharp corner.  The exponential smallness is a property of the chain, not of the proof.

Scope caveat: `ell_cube_corner_le` is a **pointwise** bound at the corner point itself, and a
single point is Lebesgue-null, so this lemma does not compose with it into a machine-checked
exponential upper bound on `conductance (ballWalk cube δ) (uniformOn volume cube)`.  Doing so
needs a positive-measure neighbourhood of the corner on which `ell` is exponentially small,
which nothing in this repository proves.  What *is* machine-checked here is the implication:
any such neighbourhood immediately caps the conductance. -/
theorem conductanceOn_ballWalk_le_of_ell_le {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hKtop : volume K ≠ ⊤) (h0 : volume (A ∩ K) ≠ 0) {c : ℝ≥0∞}
    (hc : ∀ x ∈ A ∩ K, ell K δ x ≤ c) :
    conductanceOn (ballWalk K δ) (volume.restrict K) A ≤ c := by
  have htop : volume (A ∩ K) ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono Set.inter_subset_right)
  have hell : ellMeasure K δ A ≤ c * volume (A ∩ K) := by
    rw [ellMeasure_apply_eq_setLIntegral K δ hA]
    calc ∫⁻ x in A ∩ K, ell K δ x ≤ ∫⁻ _ in A ∩ K, c :=
          setLIntegral_mono' (hA.inter hK) hc
      _ = c * volume (A ∩ K) := by rw [setLIntegral_const]
  refine le_of_mul_le_mul_right_of_ne ?_ h0 htop
  calc conductanceOn (ballWalk K δ) (volume.restrict K) A * volume (A ∩ K)
      = conductanceOn (speedyWalk K δ) (ellMeasure K δ) A * ellMeasure K δ A :=
        conductanceOn_ballWalk_mul_volume_inter hK δ hA hKtop
    _ ≤ 1 * (c * volume (A ∩ K)) := by
        gcongr
        exact conductanceOn_le_one _ _ _
    _ = c * volume (A ∩ K) := one_mul _

/-- **The undiscounted conductance of the ball walk, capped by one bad set.**  If some
measurable `A` of relative volume in `(0, 1/2]` has `ell K δ ≤ c` throughout `A ∩ K`, then

    conductance (ballWalk K δ) (uniformOn volume K)  ≤  c.

Assumes `MeasurableSet K`, `MeasurableSet A`, `0 < vol K < ⊤`, and the two mass guards on `A`.

This is the precise sense in which the `s`-conductance of §3 is *necessary* and not a
convenience: no theorem of the form "`Φ(ballWalk) ≥ polynomial`" can hold for a class of
bodies containing one with an exponentially bad `ell`-region, however small that region is,
as long as it has positive measure. -/
theorem conductance_ballWalk_uniformOn_le_of_ell_le {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hApos : 0 < Arlib.uniformOn volume K A) (hAhalf : Arlib.uniformOn volume K A ≤ 1 / 2)
    {c : ℝ≥0∞} (hc : ∀ x ∈ A ∩ K, ell K δ x ≤ c) :
    conductance (ballWalk K δ) (Arlib.uniformOn volume K) ≤ c := by
  have hpiA : Arlib.uniformOn volume K A = (volume K)⁻¹ * volume (A ∩ K) := by
    rw [Arlib.uniformOn_def, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
  have h0 : volume (A ∩ K) ≠ 0 := by
    intro h
    rw [hpiA, h, mul_zero] at hApos
    exact absurd rfl hApos.ne'
  calc conductance (ballWalk K δ) (Arlib.uniformOn volume K)
      ≤ conductanceOn (ballWalk K δ) (Arlib.uniformOn volume K) A :=
        conductance_le_conductanceOn _ _ hA hApos hAhalf
    _ = conductanceOn (ballWalk K δ) (volume.restrict K) A := by
        rw [Arlib.uniformOn_def,
          conductanceOn_smul _ _ (ENNReal.inv_ne_zero.2 hKtop) (ENNReal.inv_ne_top.2 hK0)]
    _ ≤ c := conductanceOn_ballWalk_le_of_ell_le hK δ hA hKtop h0 hc

/-! ## 6. Composing to a total-variation bound -/

/-- **Mixing of the lazy ball walk to the uniform measure, from the `s`-conductance.**

Started from an `M`-warm `sigma`, the lazy ball walk is within total variation `ε` of
`Arlib.uniformOn volume K` after `2·log(2M/ε)/phi²` steps, provided

* `2·phi ≤ conductance (speedyWalk K δ) (ellProb K δ)` — the speedy walk's polynomial bound;
* `sm ≤ ofReal (ε/(2M))` — the smoothness parameter is below the discard threshold.

**`hLSs` is a binder, not a theorem.**  It is the Lovász–Simonovits `s`-conductance bound
`d_TV(σ_m,π) ≤ H_s + (H_s/s)(1 − Φ_s²/2)^m`, threaded verbatim from
`Arlib.MarkovChains.tvLe_iterate_of_sConductance` (`HitAndRunMixing.lean`), which records
both that it is unproved here and that it is *false on a space with atoms*.  This theorem is
therefore **conditional**; it is not a claim that the lazy ball walk provably mixes.

Note the price hidden in `sm ≤ ofReal (ε/(2M))`: with `sm = 1 − (1−δ)ⁿ ≈ nδ` this forces
`δ ≲ ε/(2Mn)`, and `δ` sits in `phi` as a factor, so the step count grows like `(Mn/ε)²`.
That is the same genre of trade-off as the arithmetic route of
`Arlib/MarkovChains/Continuous/SpeedyToUniform.lean` — the `s`-conductance route removes the
*bias* (the ball walk's stationary measure is exactly uniform) but not the `δ`-dependence.

There is no bias term in the conclusion: `Arlib.uniformOn volume K` is the ball walk's own
stationary measure (`Arlib.MarkovChains.invariant_ballWalk`), not a surrogate. -/
theorem tvLe_iterate_lazy_ballWalk_of_sConductance {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {sm : ℝ≥0∞} (hsm : IsSmooth K δ sm) (hsm1 : sm ≤ 1)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {M phi eps : ℝ} (hM : 1 ≤ M) (hphi0 : 0 < phi) (hphi1 : phi ≤ 1) (heps0 : 0 < eps)
    (heps1 : eps ≤ 1)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) sigma (Arlib.uniformOn volume K))
    (hspeedy : ENNReal.ofReal (2 * phi) ≤ conductance (speedyWalk K δ) (ellProb K δ))
    (hsms : sm ≤ ENNReal.ofReal (eps / (2 * M)))
    (hLSs : ∀ (s H : ℝ≥0∞) (ph : ℝ), 0 < ph → ph ≤ 1 → 0 < s → s ≤ 1 / 2 →
        ENNReal.ofReal ph ≤ conductanceS (lazy (ballWalk K δ)) (Arlib.uniformOn volume K) s →
        ∀ mu : Measure (EuclideanSpace ℝ (Fin n)), IsProbabilityMeasure mu →
        SmallSetDiscrepancy mu (Arlib.uniformOn volume K) s H →
        ∀ t : ℕ, Arlib.TVLe (iterate (lazy (ballWalk K δ)) mu t) (Arlib.uniformOn volume K)
          (H + H / s * ENNReal.ofReal ((1 - ph ^ 2 / 2) ^ t)))
    {m : ℕ} (hm : lsThresholdS M phi eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (lazy (ballWalk K δ)) sigma m) (Arlib.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hdouble : ENNReal.ofReal (2 * phi) = 2 * ENNReal.ofReal phi := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have htwo : (2 : ℝ≥0∞) * ENNReal.ofReal phi / 2 = ENNReal.ofReal phi := by
    rw [mul_comm, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  have hcond : ENNReal.ofReal phi
      ≤ conductanceS (lazy (ballWalk K δ)) (Arlib.uniformOn volume K)
          (ENNReal.ofReal (eps / (2 * M))) := by
    have h := le_conductanceS_lazy_ballWalk_uniformOn hK hδ hK0 hKtop hsm hsm1 hspeedy hsms
    rwa [hdouble, htwo] at h
  exact tvLe_iterate_of_sConductance hM hphi0 hphi1 heps0 heps1 hwarm hcond hLSs hm

/-! ## 7. Non-vacuity (`CLAUDE.md` §11)

Every theorem above is a `∀` over guards that could in principle be unsatisfiable, and
`conductanceS P pi s = ⊤` whenever `MidSets pi s = ∅`, which would make §3 vacuously true.
The unit ball discharges every guard at once **and** provides a member of `MidSets`. -/

/-- **The relative volume of a concentric ball.**  For `0 < r ≤ 1`,

    uniformOn volume (ball 0 1) (ball 0 r) = ofReal (rⁿ). -/
theorem uniformOn_unitBall_ball {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
      = ENNReal.ofReal (r ^ n) := by
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := Metric.ball_subset_ball hr1
  rw [Arlib.uniformOn_apply volume measurableSet_ball measurableSet_ball,
    Set.inter_eq_self_of_subset_left hsub,
    Measure.addHaar_ball_of_pos volume 0 hr0, finrank_euclideanSpace_fin,
    ENNReal.mul_div_cancel_right volume_unitBall_ne_zero volume_unitBall_ne_top]

/-- **A concentric ball of relative volume exactly `1/2`.**  For `n ≠ 0` the ball of radius
`(1/2)^(1/n)` occupies exactly half the unit ball, so it is a member of
`MidSets (uniformOn volume (ball 0 1)) s` for every `s < 1/2`. -/
theorem uniformOn_unitBall_halfVolumeBall (hn : n ≠ 0) :
    Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ((1 / 2 : ℝ) ^ ((n : ℝ)⁻¹)))
      = 1 / 2 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hr0 : (0 : ℝ) < (1 / 2 : ℝ) ^ ((n : ℝ)⁻¹) := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (1 / 2 : ℝ) ^ ((n : ℝ)⁻¹) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have hrn : ((1 / 2 : ℝ) ^ ((n : ℝ)⁻¹)) ^ n = 1 / 2 := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ ((n : ℝ)⁻¹)) n,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 2), inv_mul_cancel₀ hnR, Real.rpow_one]
  rw [uniformOn_unitBall_ball hr0 hr1, hrn, ofReal_one_half]

/-- **Bernoulli, in the form the witness needs**: `3/4 ≤ (1 − δ)ⁿ` for `0 < δ ≤ 1/(4n)`. -/
theorem three_quarters_le_one_sub_pow (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    (hδn : δ ≤ 1 / (4 * (n : ℝ))) : (3 / 4 : ℝ) ≤ (1 - δ) ^ n := by
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmul : δ * (4 * (n : ℝ)) ≤ 1 := (le_div_iff₀ (by positivity)).1 hδn
  have hnd : (n : ℝ) * δ ≤ 1 / 4 := by nlinarith
  have hδsmall : δ ≤ 1 / 4 := by nlinarith
  have hb := one_add_mul_le_pow (a := -δ) (by linarith) n
  calc (3 / 4 : ℝ) ≤ 1 + (n : ℝ) * (-δ) := by nlinarith
    _ ≤ (1 + -δ) ^ n := hb
    _ = (1 - δ) ^ n := by ring_nf

/-- **`1 − (1−δ)ⁿ ≤ 1/4` for `0 < δ ≤ 1/(4n)`**, in `ℝ≥0∞`: the smoothness parameter of
`isSmooth_of_ball_subset` sits below the discard threshold `1/4`. -/
theorem isSmooth_param_le_quarter (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    (hδn : δ ≤ 1 / (4 * (n : ℝ))) :
    1 - ENNReal.ofReal ((1 - δ) ^ n) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  have h34 : ENNReal.ofReal (3 / 4 : ℝ) ≤ ENNReal.ofReal ((1 - δ) ^ n) :=
    ENNReal.ofReal_le_ofReal (three_quarters_le_one_sub_pow hn hδ hδn)
  refine tsub_le_iff_right.2 ?_
  calc (1 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (3 / 4 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal ((1 - δ) ^ n) := by gcongr

/-- **The non-vacuity witness.**  For every dimension `n ≥ 2` and every step
`0 < δ ≤ 1/(4n)` there are a body `K` — the unit ball — a threshold `s`, a smoothness
parameter `sm`, a conductance bound `phi` and a test set `S` such that, simultaneously:

* `K` is a measurable convex body with `0 < vol K < ⊤`;
* `IsSmooth K δ sm` holds and `sm ≤ s`, so the hypotheses of
  `le_conductanceS_lazy_ballWalk_uniformOn` are met;
* `0 < phi` and `phi ≤ conductance (speedyWalk K δ) (ellProb K δ)` — the transferred bound is
  a bound on a **strictly positive** quantity, not the vacuous `0 ≤ …`;
* `S ∈ MidSets (uniformOn volume K) s` — so `conductanceS` is an infimum over a **non-empty**
  family, hence not the vacuous `⊤`;
* the conclusion of `le_conductanceS_lazy_ballWalk_uniformOn` holds for these data.

This rules out the two ways §3 could have been empty: an uninhabited hypothesis bundle, and
an infimum over the empty set. -/
theorem exists_ballWalkTransfer_witness (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    (hδn : δ ≤ 1 / (4 * (n : ℝ))) :
    ∃ (K S : Set (EuclideanSpace ℝ (Fin n))) (phi sm s : ℝ≥0∞),
      MeasurableSet K ∧ Convex ℝ K ∧ volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
        IsSmooth K δ sm ∧ sm ≤ 1 ∧ sm ≤ s ∧
        0 < phi ∧ phi ≤ conductance (speedyWalk K δ) (ellProb K δ) ∧
        S ∈ MidSets (Arlib.uniformOn volume K) s ∧
        phi / 2 ≤ conductanceS (lazy (ballWalk K δ)) (Arlib.uniformOn volume K) s := by
  have hn1 : 1 ≤ n := by omega
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hmul : δ * (4 * (n : ℝ)) ≤ 1 := (le_div_iff₀ (by positivity)).1 hδn
  have hδ4 : δ ≤ 1 / 4 := by nlinarith
  have hδ1 : δ < 1 := by linarith
  have hKR : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, ‖x‖ ≤ (1 : ℝ) := by
    intro x hx
    rw [mem_ball, dist_zero_right] at hx
    exact hx.le
  refine ⟨Metric.ball 0 1, Metric.ball 0 ((1 / 2 : ℝ) ^ ((n : ℝ)⁻¹)),
    min (1 / 16) (ENNReal.ofReal (1 / (8 * (1 : ℝ))) *
      ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64),
    1 - ENNReal.ofReal ((1 - δ) ^ n), ENNReal.ofReal (1 / 4 : ℝ),
    measurableSet_ball, convex_ball _ _, volume_unitBall_ne_zero, volume_unitBall_ne_top,
    isSmooth_of_ball_subset measurableSet_ball (convex_ball _ _) Set.Subset.rfl hδ hδ1,
    tsub_le_self, isSmooth_param_le_quarter hn1 hδ hδn,
    lt_min (by norm_num) (ENNReal.div_pos (by positivity) (by norm_num)),
    conductance_speedyWalk_ge hn1 measurableSet_ball (convex_ball _ _)
      volume_unitBall_ne_zero volume_unitBall_ne_top hδ
      (Arlib.hiso_ellProb_of_ball_bound hn one_pos hδ measurableSet_ball (convex_ball _ _)
        hKR volume_unitBall_ne_zero),
    ⟨measurableSet_ball, ?_, ?_⟩,
    le_conductanceS_lazy_ballWalk_of_ball_subset hn measurableSet_ball (convex_ball _ _)
      Set.Subset.rfl one_pos hKR hδ hδ1 (isSmooth_param_le_quarter hn1 hδ hδn)⟩
  · rw [uniformOn_unitBall_halfVolumeBall (by omega), ← ofReal_one_half]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
  · rw [uniformOn_unitBall_halfVolumeBall (by omega)]

/-! ## Axiom audit

Every theorem of this file, re-checked at elaboration time.  Each must print exactly
`[propext, Classical.choice, Quot.sound]`; anything else (in particular `sorryAx`) means the
file is not finished. -/

#print axioms conductanceSOn_lazy
#print axioms le_conductanceS_of_forall_midSets
#print axioms conductanceS_le_conductanceSOn
#print axioms mul_min_le_flow_of_le_conductance
#print axioms volume_inter_le_ellMeasure_add
#print axioms mul_sub_le_flow_ballWalk
#print axioms two_mul_one_half
#print axioms le_conductanceSOn_ballWalk_uniformOn
#print axioms le_conductanceS_ballWalk_uniformOn
#print axioms le_conductanceS_lazy_ballWalk_uniformOn
#print axioms le_conductanceS_lazy_ballWalk_of_ball_subset
#print axioms conductanceOn_ballWalk_le_of_ell_le
#print axioms conductance_ballWalk_uniformOn_le_of_ell_le
#print axioms tvLe_iterate_lazy_ballWalk_of_sConductance
#print axioms uniformOn_unitBall_ball
#print axioms uniformOn_unitBall_halfVolumeBall
#print axioms three_quarters_le_one_sub_pow
#print axioms isSmooth_param_le_quarter
#print axioms exists_ballWalkTransfer_witness

end Arlib.MarkovChains
