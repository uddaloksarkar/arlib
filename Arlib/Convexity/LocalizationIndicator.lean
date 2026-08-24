/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.LovaszVempalaIso
import Arlib.Convexity.LocalizationClosed

/-!
# The Localization Lemma at indicator integrands: what Theorem 2.1 must be given

**Read this first — the target was not reached.**  This file does **not** contain
`hloc_indicator` and does **not** contain `thm21_uncond`.  It does not discharge the binder
`hloc` of `Arlib.thm21_of_localization` (`Arlib/Convexity/LovaszVempalaIso.lean:733`), and it
does not prove Lovász–Vempala Theorem 2.1 unconditionally.  What it does contain is a
determination about *which* localisation conclusion Theorem 2.1 needs, one third of it
machine-checked as a counterexample, together with the one-dimensional and needle-level halves
of the statement that conclusion feeds.

## The task, and the verdict

`hloc` is the Localization Lemma applied to the **indicator-based** pair

    g₁ = 1_{T₁} − A·1_K,     g₂ = A·h·1_K − 1_{(K∖T₁)∖T₂},

and the two routes to it are the ones named in `AUDIT.md` items **(C)** and **(F)**:
mollify-and-pass-to-the-limit, or weaken `Continuous` inside the needle extraction.

**Both are closed as routes to `hloc`.**  The second was, however, only *half* closed before,
and this file closes the other half: `Continuous` can be weakened, exactly as far as
"continuous at the points of the limit body", and no further.

* **Dropping `Continuous` outright is refuted in this repository.**
  `Arlib.exists_transverse_oscillation_eq_one`
  (`Arlib/Convexity/LocalizationMeasurable.lean`) exhibits a measurable set whose transverse
  oscillation is `1` on *every* body of positive volume, so the moduli of
  `Arlib.exists_tendsto_transverse_modulus` (`Arlib/Convexity/LocalizationTransverse.lean:112`)
  — the **unique** place the limit passage consumes continuity — do not tend to `0` for
  indicators.  And `Arlib.exists_null_measurableSet_needleIntegral_eq_one` shows a *null* set
  can carry needle mass `1`, which kills every almost-everywhere reroute (`L¹` density, Lusin,
  Vitali–Carathéodory, in-measure approximation) at once.

  **What is new here is the matching positive result.**
  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt` weakens
  `Continuous gᵢ` to `Measurable gᵢ` plus `∀ y ∈ ⋂ k, D k, ContinuousAt gᵢ y`, and
  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_indicatorPair` instantiates that at
  the very pair `hloc` is about, the hypothesis becoming `Disjoint (⋂ k, D k) (frontier ·)` for
  each of `K`, `T₁`, `S₃`.  Together with the counterexample above this **brackets this route's**
  obstruction: continuity off the limit body is irrelevant; one frontier point on the limit body
  defeats the transverse-modulus passage, which is the only limit passage available here.  (The
  counterexample refutes the *route*, not the needle statement, and nothing below claims more.)  It still does not give `hloc`, because nothing in the chain controls where the limit
  body lands relative to `frontier T₁` — see that theorem's docstring for the two further gaps.

* **Mollification is closed at the *equality* slot.**  The approximation machinery already
  exists: `Arlib.Convexity.LocalizationLSC` reaches lower semicontinuous integrands, and
  `Arlib.Convexity.IsoOpenClosed` even removes its `η`-slack, by **scaling** a nonnegative
  minorant instead of shifting it, so that `∫_K g₁ = 0` holds *exactly*
  (`Arlib.exists_compact_body_continuous_pair`).  But a minorant is one-sided: the needle
  conclusion it transports is

      0 ≤ ∫ W · (1_{T₁} − A·1_K) ∘ γ,    i.e.   A·∫_α^β D ≤ ∫_{γ⁻¹T₁ ∩ [α,β]} D,

  the `≥`-half of `hloc`'s equality and nothing more.  Getting the `≤`-half back needs a
  continuous **majorant** of `1_{T₁}` with the same exact mass, i.e. `T₁` closed as well as
  open; inside a connected `K` that forces `T₁ ∈ {∅, K}`.

  **The `≥`-half alone is not enough, and that is the new content here.**
  `Arlib.needle_iso` — the one-dimensional core of §2 — consumes its `hmass` in *both*
  directions: `≥` at `hT₁pos`/`hkey` (`LovaszVempalaIso.lean:467-473`), and `≤` (through
  `A ≤ 1/2`) in the closing `nlinarith`.  `Arlib.not_needle_iso_of_one_lower` below refutes
  the `≥`-only statement outright, keeping `0 ≤ A` and `A ≤ 1/2`, so this is a fact about the
  statement and not an artefact of one proof.

## Where `Continuous` is actually consumed, and how far it can be weakened

The needle extraction reads its integrand hypotheses in exactly two places.
`Arlib.exists_needleIntegral_eq_zero_and_pos_affine`
(`Arlib/Convexity/LocalizationAffine.lean:364`) — the analytic core — asks only for `Measurable`
plus two *transverse moduli* `δ k → 0` with `|g y − g (a + φ (y − a) • v)| ≤ δ k` on `D k`.
Everything above it (`Arlib/Convexity/LocalizationTransverse.lean:192`,
`Arlib/Convexity/LocalizationClosed.lean:380`) uses `Continuous g` for
`hg.measurable` and for one call to `Arlib.exists_tendsto_transverse_modulus`
(`Arlib/Convexity/LocalizationTransverse.lean:112`), which manufactures those moduli.

`Arlib.exists_tendsto_transverse_modulus_of_continuousAt` shows that call needs far less:
continuity **at the points of `⋂ k, C k`** and boundedness suffice, because the only use of
continuity inside it is that a sublevel set of the transverse oscillation be a *neighbourhood of
each point of the limit body*, so that `Arlib.eventually_subset_of_antitone_isCompact` can push
the tail of the chain into it.  For `g = 1_S · f` with `f` continuous that hypothesis is exactly
`(⋂ k, C k) ∩ frontier S = ∅`.

This brackets the obstruction *for this route* from both sides, and is the whole of what this
file adds on the localisation side: continuity **off** the limit body is irrelevant, and
continuity **at** the points of the limit body cannot be dropped from the modulus argument,
since `Arlib.exists_transverse_oscillation_eq_one` produces a measurable set whose transverse
oscillation is `1` on every body of positive volume.  That is a refutation of the *route*, not
of the needle conclusion for discontinuous integrands, which is left open.

## What *would* suffice, and why it is a different development

Two lower bounds — one on each of `T₁` and `T₂` — do suffice, with no equality anywhere:
`Arlib.needle_iso_two_lower`.  Both are of the form "the needle mass of an open set is at
least its ambient fraction", which is exactly what a minorant delivers.  So the obstruction
is **not** the one-sidedness; it is the *count*.

A single run of the chain `Arlib.exists_flat_cut_chain_collinear_compact_ge` maintains one
equality `∫_{D m} g₁ = 0` and one inequality `0 < ∫_{D m} g₂`: the cut bisects `g₁`, so both
halves inherit the equality, and at least one half inherits the strict inequality.  Two
inequalities besides the positivity means **two** quantities to bisect on a one-parameter
pencil, and a one-parameter family with its antipodal map is `S¹`, on which Borsuk–Ulam
bisects one integrand and no more.

**A correction to an earlier phrasing of this paragraph, which said "Borsuk–Ulam — absent from
Mathlib".**  Borsuk–Ulam is *not* missing: `Arlib.Topology.OddMap` and
`Arlib.Topology.HamSandwich` prove it and derive
`Arlib.exists_halfSpace_bisecting_pair_of_finrank`, a genuine two-integrand ham sandwich for
signed integrands.  What that cut does not do is pass through a **prescribed codim-2 flat** —
`Arlib/Convexity/LocalizationAssembly.lean:38-44` says so in as many words, "prescribes
neither" direction nor position — and passing through every prescribed flat of a countable
dense family is exactly what `Arlib.minor_eq_of_pencil_exhaustion` consumes to force the limit
body collinear.  So the gap is real, but its name is *positional* control of a two-integrand
bisection, not the absence of Borsuk–Ulam, and
`Arlib/Convexity/LocalizationAssembly.lean:42-44` avoids it precisely because only one
integrand ever needs bisecting.

The other escape, a genuine limit passage over a *sequence* of needles, needs compactness of
the family of needle profiles plus continuity of `(γ, W) ↦ ∫ W · 1_{T₁} ∘ γ` — and the second
is false for indicators for the same reason as above (needle integrals see Lebesgue-null
sets).  `Arlib.Convexity.LocalizationLSC` says as much in its own docstring.

## Main results

* `Arlib.needle_iso_two_lower` — **the one-dimensional theorem from two lower bounds.**
  `Arlib.needle_iso` with `∫_{Z₁} D = A·∫_α^β D` replaced by `A·∫_α^β D ≤ ∫_{Z₁} D` *and*
  `A·∫_α^β D ≤ ∫_{Z₂} D`.  `0 ≤ A` and `A ≤ 1/2` become unnecessary; `0 ≤ G` on `[α,β]` is
  added (every consumer has it).  Proved from `Arlib.needle_iso` as a black box.
* `Arlib.counter_isPartition3`, `Arlib.not_needle_iso_of_one_lower` — **the refutation of the
  one-sided form**, in the idiom of `Arlib.not_hIso_two`: the `≥`-only statement written out
  verbatim and negated, with an explicit interval witness.
* `Arlib.needle_iso_of_chord_two_lower` — the same on a needle inside the body: this is
  `Arlib.needle_iso_of_chord` with its closing call redirected.
* `Arlib.exists_tendsto_transverse_modulus_of_continuousAt`,
  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt` — **the exact
  weakening of `Continuous` the needle extraction admits**: `Measurable` plus continuity at the
  points of the *limit body* `⋂ k, D k` alone.  See "Where `Continuous` is actually consumed"
  below.  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt_recovers`
  is the drop-in check that the continuous form follows.
* `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_indicatorPair` — that weakening
  instantiated at the **indicator pair** `g₁ = 1_{T₁} − A·1_K`, `g₂ = A·1_K·h − 1_{S₃}` of
  `hloc`, the frontier side condition being `Disjoint (⋂ k, D k) (frontier ·)` for each of the
  three sets.  It still does **not** discharge `hloc`; the three reasons are at its docstring.
* `Arlib.thm21_of_localization_two_lower` — **Theorem 2.1 for the uniform density from the
  two-sided binder `hloc₂`**, whose ambient antecedents are `A·vol K ≤ vol T₁` and
  `A·vol K ≤ vol T₂` — exactly the `min(vol T₁, vol T₂)` shape the `hIso` binder of
  `Arlib.MarkovChains.conductance_hitAndRun_ge` wants, and with no `A ≤ 1/2` side condition.

## Honesty

`hloc₂` is **not weaker** than `hloc`, and it is not claimed to be: `hloc`'s equality gives
the `T₁` bound but says nothing about `T₂`, and for the present one-bisection chain `hloc₂` is
strictly *harder* (three constraints against two).  Its value is that it is the **sharp**
interface — `Arlib.not_needle_iso_of_one_lower` shows the `T₂` bound cannot be dropped — and
that both of its clauses are of the one-sided shape an approximation argument can produce, so
it is the statement a future two-constraint (Borsuk–Ulam) chain should be pointed at.

Nothing below is a `def`, `structure`, `class` or named `Prop`; every declaration is a
`theorem`, and none of them is named for a statement it does not prove.  The two binders that
do appear — `hloc₂` of `Arlib.thm21_of_localization_two_lower` and the universally quantified
statement negated by `Arlib.not_needle_iso_of_one_lower` — are written out inline at their
declarations.
-/

namespace Arlib

open MeasureTheory Set

/-! ### The one-dimensional needle inequality from two lower bounds -/

section OneDim

/-- **The one-dimensional needle inequality of Lovász–Vempala §2, from two *lower* bounds
instead of the mass equality.**

`Arlib.needle_iso` asks for the exact needle mass identity `∫_{Z₁} D = A·∫_α^β D`.  This
variant asks instead for the two one-sided bounds

    A · ∫_α^β D ≤ ∫_{Z₁} D    and    A · ∫_α^β D ≤ ∫_{Z₂} D,

and reaches the same conclusion.  Two interface improvements come for free:

* the hypothesis `A ≤ 1/2` of `Arlib.needle_iso` is **not needed** — in each branch of the
  proof the constant actually fed to `Arlib.needle_iso` is `∫_{Zᵢ} D / ∫_α^β D` for the
  *smaller* of the two parts, which is `≤ 1/2` automatically;
* `0 ≤ A` is not needed either.

The price is `hG0`, nonnegativity of `G` on `[α, β]` (`Arlib.needle_iso` does not ask for it),
which is what makes the conclusion monotone in `A`.  Every consumer has it: `G` is the
step-length weight `h`, which is nonnegative by hypothesis.

The proof is a case split on which of `∫_{Z₁} D`, `∫_{Z₂} D` is at most half of `∫_α^β D` —
at least one is, since the three parts sum to the whole — followed by `Arlib.needle_iso`
applied at that part's exact fraction, used as a black box.  In the second branch the two
parts are exchanged by `Arlib.IsPartition3.symm` and `min_comm`/`max_comm`.

**This hypothesis is genuinely stronger than the `≥`-half of the equality alone**: see
`Arlib.not_needle_iso_of_one_lower`, which refutes the statement obtained by dropping
`hmass₂`. -/
theorem needle_iso_two_lower {D G : ℝ → ℝ} {α β A M : ℝ} (hαβ : α ≤ β)
    (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t) (hlc : LogConcaveOn (Set.Icc α β) D)
    (hDint : IntervalIntegrable D volume α β)
    (hG0 : ∀ t ∈ Set.Icc α β, 0 ≤ G t)
    (hGM : ∀ t ∈ Set.Icc α β, G t ≤ M) (hM0 : 0 ≤ M) (hM3 : M ≤ 1 / 3)
    (hGDint : IntervalIntegrable (fun t => G t * D t) volume α β)
    {Z₁ Z₂ Z₃ : Set ℝ} (hpart : IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃)
    (hm₁ : MeasurableSet Z₁) (hm₂ : MeasurableSet Z₂) (hm₃ : MeasurableSet Z₃)
    (hmass₁ : A * (∫ t in α..β, D t) ≤ ∫ t in Z₁, D t)
    (hmass₂ : A * (∫ t in α..β, D t) ≤ ∫ t in Z₂, D t)
    (hcross : ∀ s ∈ Z₁, ∀ t ∈ Z₂,
      3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t)) :
    A * (∫ t in α..β, G t * D t) ≤ ∫ t in Z₃, D t := by
  have hT0 : 0 ≤ ∫ t in α..β, D t := intervalIntegral.integral_nonneg hαβ hD0
  have hT₁0 : 0 ≤ ∫ t in Z₁, D t :=
    setIntegral_nonneg hm₁ fun t ht => hD0 t (hpart.subset₁ ht)
  have hT₂0 : 0 ≤ ∫ t in Z₂, D t :=
    setIntegral_nonneg hm₂ fun t ht => hD0 t (hpart.subset₂ ht)
  have hT₃0 : 0 ≤ ∫ t in Z₃, D t :=
    setIntegral_nonneg hm₃ fun t ht => hD0 t (hpart.subset₃ ht)
  have hsum : (∫ t in α..β, D t) = (∫ t in Z₁, D t) + (∫ t in Z₂, D t) + ∫ t in Z₃, D t :=
    integral_of_isPartition3 hαβ hDint hpart hm₂ hm₃
  have hGDnn : 0 ≤ ∫ t in α..β, G t * D t :=
    intervalIntegral.integral_nonneg hαβ fun t ht => mul_nonneg (hG0 t ht) (hD0 t ht)
  have hGD : (∫ t in α..β, G t * D t) ≤ M * ∫ t in α..β, D t := by
    have hmono : (∫ t in α..β, G t * D t) ≤ ∫ t in α..β, M * D t := by
      refine intervalIntegral.integral_mono_on hαβ hGDint (hDint.const_mul M) ?_
      intro t ht
      exact mul_le_mul_of_nonneg_right (hGM t ht) (hD0 t ht)
    rwa [intervalIntegral.integral_const_mul] at hmono
  rcases eq_or_lt_of_le hT0 with hT | hTpos
  · -- the whole needle carries no mass: then `∫ G·D = 0` and the claim is `0 ≤ ∫_{Z₃} D`
    have hzero : (∫ t in α..β, G t * D t) = 0 := by
      refine le_antisymm ?_ hGDnn
      rw [← hT] at hGD
      simpa using hGD
    rw [hzero, mul_zero]
    exact hT₃0
  · by_cases hhalf : (∫ t in Z₁, D t) ≤ (∫ t in α..β, D t) / 2
    · -- run `needle_iso` at the exact fraction of `Z₁`
      have hstar : (∫ t in Z₁, D t)
          = ((∫ t in Z₁, D t) / ∫ t in α..β, D t) * ∫ t in α..β, D t :=
        (div_mul_cancel₀ _ hTpos.ne').symm
      have hmain := needle_iso hαβ hD0 hlc hDint hGM hM0 hM3 hGDint hpart hm₁ hm₂ hm₃
        (div_nonneg hT₁0 hT0) (by rw [div_le_iff₀ hTpos]; linarith) hstar hcross
      have hAle : A ≤ (∫ t in Z₁, D t) / ∫ t in α..β, D t := by
        rw [le_div_iff₀ hTpos]; exact hmass₁
      exact le_trans (mul_le_mul_of_nonneg_right hAle hGDnn) hmain
    · -- otherwise `Z₂` is the small part; exchange the roles of `Z₁` and `Z₂`
      have hhalf' : (∫ t in α..β, D t) / 2 < ∫ t in Z₁, D t := not_le.mp hhalf
      have hhalf₂ : (∫ t in Z₂, D t) ≤ (∫ t in α..β, D t) / 2 := by linarith
      have hstar : (∫ t in Z₂, D t)
          = ((∫ t in Z₂, D t) / ∫ t in α..β, D t) * ∫ t in α..β, D t :=
        (div_mul_cancel₀ _ hTpos.ne').symm
      have hcross' : ∀ s ∈ Z₂, ∀ t ∈ Z₁,
          3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t) := by
        intro s hs t ht
        rw [min_comm, max_comm]
        exact hcross t ht s hs
      have hmain := needle_iso hαβ hD0 hlc hDint hGM hM0 hM3 hGDint hpart.symm hm₂ hm₁ hm₃
        (div_nonneg hT₂0 hT0) (by rw [div_le_iff₀ hTpos]; linarith) hstar hcross'
      have hAle : A ≤ (∫ t in Z₂, D t) / ∫ t in α..β, D t := by
        rw [le_div_iff₀ hTpos]; exact hmass₂
      exact le_trans (mul_le_mul_of_nonneg_right hAle hGDnn) hmain

/-- The three intervals of `Arlib.not_needle_iso_of_one_lower` really do partition `[0,1]`. -/
theorem counter_isPartition3 :
    IsPartition3 (Set.Icc (0 : ℝ) 1) (Set.Ico 0 (83 / 100)) (Set.Ioc (98 / 100) 1)
      (Set.Icc (83 / 100) (98 / 100)) := by
  refine ⟨Set.Subset.antisymm ?_ ?_, ?_, ?_, ?_⟩
  · rintro x ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) <;> constructor <;> linarith
  · rintro x ⟨h1, h2⟩
    rcases lt_or_ge x (83 / 100) with h | h
    · exact Or.inl (Or.inl ⟨h1, h⟩)
    rcases le_or_gt x (98 / 100) with h' | h'
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl (Or.inr ⟨h', h2⟩)
  · exact Set.disjoint_left.mpr fun x hx hx' => by
      have := hx.2; have := hx'.1; linarith
  · exact Set.disjoint_left.mpr fun x hx hx' => by
      have := hx.2; have := hx'.1; linarith
  · exact Set.disjoint_left.mpr fun x hx hx' => by
      have := hx.1; have := hx'.2; linarith

/-- **One lower bound is not enough: `Arlib.needle_iso_two_lower` is false without `hmass₂`.**

This is the negation, written out verbatim, of the statement obtained from
`Arlib.needle_iso_two_lower` by deleting the second mass hypothesis
`A · ∫_α^β D ≤ ∫_{Z₂} D`.  Since the witness has `G ≡ 1/3 ≥ 0`, it refutes *a fortiori* the
same statement without `hG0` — hence also `Arlib.needle_iso` with its mass *equality*
`∫_{Z₁} D = A·∫_α^β D` relaxed to the `≥`-half, which is the only half that any approximation
of `1_{T₁}` from below can deliver (see the module docstring).  The hypotheses `0 ≤ A` and
`A ≤ 1/2` of `Arlib.needle_iso` are kept, so the refutation is not an artefact of dropping
them.

**The witness.**  `α = 0`, `β = 1`, `D ≡ 1` (log-concave), `G ≡ 1/3`, `M = 1/3`, `A = 1/2`, and

    Z₁ = [0, 83/100),   Z₂ = (98/100, 1],   Z₃ = [83/100, 98/100].

The cross-ratio hypothesis holds with room to spare: for `s ∈ Z₁`, `t ∈ Z₂` one has `s < t`,
so the inequality reads `s·(1 − t) ≤ t − s`, and `s(1−t) < (83/100)(2/100) = 83/5000` while
`t − s > 15/100`.  The mass hypothesis holds: `A·∫D = 1/2 ≤ 83/100 = ∫_{Z₁} D`.  But the
conclusion fails: `A·∫ G·D = 1/6 > 15/100 = ∫_{Z₃} D`.

So the needle carrying most of its mass in `Z₁` and almost none in `Z₂` is admissible for the
one-sided hypothesis and defeats the conclusion.  This is exactly the configuration that the
*equality* `∫_{Z₁} D = A·∫_α^β D` excludes through its `≤`-half — the half that no lower
approximation of an indicator can produce. -/
theorem not_needle_iso_of_one_lower :
    ¬ ∀ (D G : ℝ → ℝ) (α β A M : ℝ), α ≤ β →
      (∀ t ∈ Set.Icc α β, 0 ≤ D t) → LogConcaveOn (Set.Icc α β) D →
      IntervalIntegrable D volume α β →
      (∀ t ∈ Set.Icc α β, 0 ≤ G t) → (∀ t ∈ Set.Icc α β, G t ≤ M) → 0 ≤ M → M ≤ 1 / 3 →
      IntervalIntegrable (fun t => G t * D t) volume α β →
      ∀ Z₁ Z₂ Z₃ : Set ℝ, IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃ →
      MeasurableSet Z₁ → MeasurableSet Z₂ → MeasurableSet Z₃ →
      0 ≤ A → A ≤ 1 / 2 →
      A * (∫ t in α..β, D t) ≤ (∫ t in Z₁, D t) →
      (∀ s ∈ Z₁, ∀ t ∈ Z₂,
        3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t)) →
      A * (∫ t in α..β, G t * D t) ≤ ∫ t in Z₃, D t := by
  intro H
  -- the three set integrals of the constant weight
  have hIco : (∫ _t in Set.Ico (0 : ℝ) (83 / 100), (1 : ℝ)) = 83 / 100 := by
    rw [setIntegral_const]
    simp only [smul_eq_mul, mul_one, MeasureTheory.measureReal_def, Real.volume_Ico]
    norm_num
  have hIcc : (∫ _t in Set.Icc (83 / 100 : ℝ) (98 / 100), (1 : ℝ)) = 15 / 100 := by
    rw [setIntegral_const]
    simp only [smul_eq_mul, mul_one, MeasureTheory.measureReal_def, Real.volume_Icc]
    norm_num
  have hcross : ∀ s ∈ Set.Ico (0 : ℝ) (83 / 100), ∀ t ∈ Set.Ioc (98 / 100 : ℝ) 1,
      3 * (1 / 3 : ℝ) * ((min s t - 0) * (1 - max s t))
        ≤ (1 - 0) * (max s t - min s t) := by
    rintro s ⟨hs1, hs2⟩ t ⟨ht1, ht2⟩
    have hst : s ≤ t := by linarith
    rw [min_eq_left hst, max_eq_right hst]
    nlinarith
  have hcon := H (fun _ => 1) (fun _ => 1 / 3) 0 1 (1 / 2) (1 / 3) zero_le_one
    (fun _ _ => zero_le_one) (logConcaveOn_const (convex_Icc 0 1) zero_le_one)
    intervalIntegrable_const (fun _ _ => by norm_num) (fun _ _ => le_rfl) (by norm_num) le_rfl
    (by simp)
    (Set.Ico 0 (83 / 100)) (Set.Ioc (98 / 100) 1) (Set.Icc (83 / 100) (98 / 100))
    counter_isPartition3 measurableSet_Ico measurableSet_Ioc measurableSet_Icc
    (by norm_num) le_rfl
    (by rw [intervalIntegral.integral_const, hIco]; norm_num) hcross
  rw [intervalIntegral.integral_const, hIcc] at hcon
  norm_num at hcon

end OneDim

/-! ### The same on a needle inside the body, and Theorem 2.1 from the two-sided binder -/

section Ambient

variable {n : ℕ}

/-- **`Arlib.needle_iso_of_chord` with the mass equality replaced by the two lower bounds.**

Every hypothesis except the mass one is verbatim that of `Arlib.needle_iso_of_chord`, and the
proof is that theorem's proof with its closing call to `Arlib.needle_iso` replaced by
`Arlib.needle_iso_two_lower`; the construction of the needle supremum `M` and of the
cross-ratio condition on the needle is untouched, because neither ever mentions the mass
hypothesis.  As there, `0 ≤ A` and `A ≤ 1/2` are not needed.

The copy is forced by the one-declaration-per-file discipline: nothing between the statement of
`Arlib.needle_iso_of_chord` and its final line can be reused as a lemma, because the
intermediate data (`M`, `Z₁`, `Z₂`, `Z₃`, `hcross`) is built inside its proof. -/
theorem needle_iso_of_chord_two_lower {K T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) (hdisj : Disjoint T₁ T₂)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hh3 : ∀ x ∈ K, h x ≤ 1 / 3)
    (hchord : ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      h x ≤ min 1 (crossRatioDist K u v) / 3)
    {p e : EuclideanSpace ℝ (Fin n)} {α β : ℝ} (hαβ : α ≤ β)
    (hseg : ∀ r ∈ Set.Icc α β, needleMap p e r ∈ K)
    {D : ℝ → ℝ} (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t) (hlc : LogConcaveOn (Set.Icc α β) D)
    (hDint : IntervalIntegrable D volume α β)
    (hGDint : IntervalIntegrable (fun t => h (needleMap p e t) * D t) volume α β)
    {A : ℝ}
    (hmass₁ : A * (∫ t in α..β, D t)
      ≤ ∫ t in needleMap p e ⁻¹' T₁ ∩ Set.Icc α β, D t)
    (hmass₂ : A * (∫ t in α..β, D t)
      ≤ ∫ t in needleMap p e ⁻¹' T₂ ∩ Set.Icc α β, D t) :
    A * (∫ t in α..β, h (needleMap p e t) * D t)
      ≤ ∫ t in needleMap p e ⁻¹' ((K \ T₁) \ T₂) ∩ Set.Icc α β, D t := by
  classical
  have hcont : Continuous (needleMap p e) := by
    show Continuous fun t : ℝ => p + t • e
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hmeas : Measurable (needleMap p e) := hcont.measurable
  set Z₁ := needleMap p e ⁻¹' T₁ ∩ Set.Icc α β with hZ₁def
  set Z₂ := needleMap p e ⁻¹' T₂ ∩ Set.Icc α β with hZ₂def
  set Z₃ := needleMap p e ⁻¹' ((K \ T₁) \ T₂) ∩ Set.Icc α β with hZ₃def
  have hm₁ : MeasurableSet Z₁ := (hT₁.preimage hmeas).inter measurableSet_Icc
  have hm₂ : MeasurableSet Z₂ := (hT₂.preimage hmeas).inter measurableSet_Icc
  -- the three parameter sets partition `[α, β]`
  have hpart : IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine Set.Subset.antisymm ?_ ?_
      · rintro r ((⟨-, hr⟩ | ⟨-, hr⟩) | ⟨-, hr⟩) <;> exact hr
      · intro r hr
        by_cases h1 : needleMap p e r ∈ T₁
        · exact Or.inl (Or.inl ⟨h1, hr⟩)
        by_cases h2 : needleMap p e r ∈ T₂
        · exact Or.inl (Or.inr ⟨h2, hr⟩)
        · exact Or.inr ⟨⟨⟨hseg r hr, h1⟩, h2⟩, hr⟩
    · exact Set.disjoint_left.mpr fun r hr₁ hr₂ =>
        Set.disjoint_left.mp hdisj hr₁.1 hr₂.1
    · exact Set.disjoint_left.mpr fun r hr₁ hr₃ => hr₃.1.1.2 hr₁.1
    · exact Set.disjoint_left.mpr fun r hr₂ hr₃ => hr₃.1.2 hr₂.1
  have hm₃ : MeasurableSet Z₃ := by
    have : Z₃ = Set.Icc α β \ (Z₁ ∪ Z₂) := by
      refine Set.Subset.antisymm (fun r hr => ⟨hr.2, ?_⟩) (fun r hr => ?_)
      · rintro (h1 | h2)
        exacts [hr.1.1.2 h1.1, hr.1.2 h2.1]
      · have hr3 : r ∈ Z₁ ∪ Z₂ ∪ Z₃ := by rw [hpart.union]; exact hr.1
        rcases hr3 with (h1 | h2) | h3
        exacts [absurd (Or.inl h1) hr.2, absurd (Or.inr h2) hr.2, h3]
    rw [this]
    exact measurableSet_Icc.diff (hm₁.union hm₂)
  -- the supremum of `h` along the needle
  set M := sSup ((fun r => h (needleMap p e r)) '' Set.Icc α β) with hMdef
  have hIccne : (Set.Icc α β).Nonempty := Set.nonempty_Icc.mpr hαβ
  have hbdd : BddAbove ((fun r => h (needleMap p e r)) '' Set.Icc α β) := by
    refine ⟨1 / 3, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact hh3 _ (hseg r hr)
  have hGM : ∀ r ∈ Set.Icc α β, h (needleMap p e r) ≤ M := fun r hr =>
    le_csSup hbdd ⟨r, hr, rfl⟩
  have hM3 : M ≤ 1 / 3 := by
    refine csSup_le (hIccne.image _) ?_
    rintro y ⟨r, hr, rfl⟩
    exact hh3 _ (hseg r hr)
  have hM0 : 0 ≤ M := le_trans (hh0 _) (hGM α ⟨le_rfl, hαβ⟩)
  -- the cross condition on the needle
  have hcross : ∀ s ∈ Z₁, ∀ t ∈ Z₂,
      3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t) := by
    intro s hs t ht
    have hsK : needleMap p e s ∈ K := hseg s hs.2
    have htK : needleMap p e t ∈ K := hseg t ht.2
    have hnee : needleMap p e s ≠ needleMap p e t := fun heq =>
      Set.disjoint_left.mp hdisj hs.1 (heq ▸ ht.1)
    have hst : s ≠ t := fun heq => hnee (by rw [heq])
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
      refine needle_crossRatio_transfer hKb hs.2.1 hlt ht.2.2
        (hseg α ⟨le_rfl, hαβ⟩) (hseg β ⟨hαβ, le_rfl⟩) hsK htK hnee ?_
      exact three_mul_sSup_le_crossRatioDist hchord hαβ hseg hs.1 ht.1 hst
    · rw [min_eq_right hgt.le, max_eq_left hgt.le]
      refine needle_crossRatio_transfer hKb ht.2.1 hgt hs.2.2
        (hseg α ⟨le_rfl, hαβ⟩) (hseg β ⟨hαβ, le_rfl⟩) htK hsK (Ne.symm hnee) ?_
      rw [crossRatioDist_comm hKb (Ne.symm hnee) htK hsK]
      exact three_mul_sSup_le_crossRatioDist hchord hαβ hseg hs.1 ht.1 hst
  exact needle_iso_two_lower hαβ hD0 hlc hDint (fun r _ => hh0 _) hGM hM0 hM3 hGDint hpart
    hm₁ hm₂ hm₃ hmass₁ hmass₂ hcross

/-- **Theorem 2.1 of Lovász–Vempala for the uniform density, from the two-sided localisation
binder.**

This is `Arlib.thm21_of_localization` with its binder `hloc` replaced by the binder `hloc₂`
below, whose needle conclusion asks for **two lower bounds**

    A·∫_α^β D ≤ ∫_{γ⁻¹T₁ ∩ [α,β]} D    and    A·∫_α^β D ≤ ∫_{γ⁻¹T₂ ∩ [α,β]} D

in place of the single equality `∫_{γ⁻¹T₁ ∩ [α,β]} D = A·∫_α^β D`, and whose ambient antecedent
is likewise two-sided.  `0 ≤ A` and `A ≤ 1/2` are no longer needed anywhere.

**The two ambient antecedents are exactly the `min` the consumer wants.**  At
`A = min(vol T₁, vol T₂)/vol K` both read as identities, and the conclusion becomes
`E(h)·min(vol T₁, vol T₂) ≤ vol((K∖T₁)∖T₂)` — the shape of the `hIso` binder of
`Arlib.MarkovChains.conductance_hitAndRun_ge`, without the `A ≤ 1/2` side condition that
`Arlib.thm21_of_localization` needs to get there.

**`hloc₂` is *not* weaker than `hloc`, and this file does not discharge it.**  See the module
docstring: `hloc` gives the `T₁` bound but not the `T₂` one, and `hloc₂` is *harder* for a
one-bisection chain, being three simultaneous constraints rather than two.  What
`Arlib.not_needle_iso_of_one_lower` establishes is that the `T₂` bound cannot simply be
dropped — so `hloc₂` is the sharp interface, not a convenience. -/
theorem thm21_of_localization_two_lower {K T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) (hdisj : Disjoint T₁ T₂)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hh3 : ∀ x ∈ K, h x ≤ 1 / 3)
    (hchord : ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      h x ≤ min 1 (crossRatioDist K u v) / 3)
    {A : ℝ}
    (hmassK₁ : A * (volume K).toReal ≤ (volume T₁).toReal)
    (hmassK₂ : A * (volume K).toReal ≤ (volume T₂).toReal)
    (hloc₂ : A * (volume K).toReal ≤ (volume T₁).toReal →
      A * (volume K).toReal ≤ (volume T₂).toReal →
      (volume ((K \ T₁) \ T₂)).toReal < A * ∫ x in K, h x →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        IntervalIntegrable (fun t => h (needleMap p e t) * D t) volume α β ∧
        A * (∫ t in α..β, D t) ≤ (∫ t in needleMap p e ⁻¹' T₁ ∩ Set.Icc α β, D t) ∧
        A * (∫ t in α..β, D t) ≤ (∫ t in needleMap p e ⁻¹' T₂ ∩ Set.Icc α β, D t) ∧
        (∫ t in needleMap p e ⁻¹' ((K \ T₁) \ T₂) ∩ Set.Icc α β, D t)
          < A * ∫ t in α..β, h (needleMap p e t) * D t) :
    A * (∫ x in K, h x) ≤ (volume ((K \ T₁) \ T₂)).toReal := by
  by_contra hcon
  obtain ⟨p, e, α, β, D, hαβ, hseg, hD0, hlc, hDint, hGDint, hmass₁, hmass₂, hstrict⟩ :=
    hloc₂ hmassK₁ hmassK₂ (not_le.mp hcon)
  exact absurd (needle_iso_of_chord_two_lower hKb hT₁ hT₂ hdisj hh0 hh3 hchord hαβ hseg hD0 hlc
    hDint hGDint hmass₁ hmass₂) (not_le.mpr hstrict)

end Ambient


/-! ### Where `Continuous` is actually consumed: only at the limit body -/

section ContinuityAtLimit

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The needle-axis retraction `y ↦ a + φ (y - a) • v` is continuous.

A local copy of the (`private`) `Arlib.continuous_axisPoint` of
`Arlib/Convexity/LocalizationTransverse.lean`. -/
theorem continuous_axisRetract (a v : E) (φ : E →ₗ[ℝ] ℝ) :
    Continuous fun y : E => a + φ (y - a) • v :=
  continuous_const.add
    (((φ.continuous_of_finiteDimensional).comp
      (continuous_id.sub continuous_const)).smul continuous_const)

/-- **The transverse-thinness bridge from continuity at the limit body alone.**

`Arlib.exists_tendsto_transverse_modulus`
(`Arlib/Convexity/LocalizationTransverse.lean:112`) asks `g` to be continuous *everywhere*.  It
is not: the exact moduli

`δ k = sSup {|g y - g (a + φ (y - a) • v)| : y ∈ C k}`

tend to `0` as soon as `g` is continuous **at each point of `⋂ k, C k`**, the body the chain
shrinks to, and bounded.  Boundedness alone gives `BddAbove` for the `sSup`, exactly as before.

The reason is that the existing proof uses continuity for one thing only — that
`{y | |g y - g (a + φ (y - a) • v)| < ε/2}` is *open* and contains `⋂ k, C k`, so that
`Arlib.eventually_subset_of_antitone_isCompact` puts the tail of the chain inside it.  Openness
is not needed at points far from the limit body: it suffices that
`{y | |g y - g (a + φ (y - a) • v)| ≤ ε/2}` be a **neighbourhood of each point of `⋂ k, C k`**,
which is what the `interior` below records.  At `y₀ ∈ ⋂ k, C k` the retraction fixes `y₀`
(`haxis`), so continuity of `g` at `y₀` controls both `g y` and `g (a + φ (y - a) • v)` — the
latter through continuity of the retraction — within `ε/4` of `g y₀`, and the triangle
inequality closes the gap. -/
theorem exists_tendsto_transverse_modulus_of_continuousAt {C : ℕ → Set E}
    (hC : ∀ k, IsCompact (C k)) (hmono : ∀ k, C (k + 1) ⊆ C k) {a v : E} {φ : E →ₗ[ℝ] ℝ}
    (haxis : ∀ y ∈ ⋂ k, C k, y = a + φ (y - a) • v)
    {g : E → ℝ} (hg : ∀ y ∈ ⋂ k, C k, ContinuousAt g y) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ k, ∀ y ∈ C k, |g y - g (a + φ (y - a) • v)| ≤ δ k := by
  classical
  have hπc : Continuous fun y : E => a + φ (y - a) • v := continuous_axisRetract a v φ
  set h : E → ℝ := fun y => |g y - g (a + φ (y - a) • v)| with hhdef
  have hh0 : ∀ y, 0 ≤ h y := fun _ => abs_nonneg _
  have habs : ∀ p q : ℝ, |p - q| ≤ |p| + |q| := fun p q => by
    simpa [sub_eq_add_neg] using abs_add_le p (-q)
  have hbdd : ∀ k, BddAbove (h '' C k) := by
    intro k
    refine ⟨2 * M, ?_⟩
    rintro z ⟨y, _, rfl⟩
    exact le_trans (habs _ _) (by linarith [hM y, hM (a + φ (y - a) • v)])
  set δ : ℕ → ℝ := fun k => sSup (h '' C k) with hδdef
  have hle : ∀ k, ∀ y ∈ C k, h y ≤ δ k := fun k y hy =>
    le_csSup (hbdd k) ⟨y, hy, rfl⟩
  have hδ0 : ∀ k, 0 ≤ δ k := by
    intro k
    rcases (C k).eq_empty_or_nonempty with he | ⟨y, hy⟩
    · rw [hδdef]; simp [he]
    · exact le_trans (hh0 y) (hle k y hy)
  refine ⟨δ, ?_, hle⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsub : (⋂ k, C k) ⊆ interior {y | h y ≤ ε / 2} := by
    intro y₀ hy₀
    have hfix : a + φ (y₀ - a) • v = y₀ := (haxis y₀ hy₀).symm
    have hball : Metric.ball (g y₀) (ε / 4) ∈ 𝓝 (g y₀) :=
      Metric.ball_mem_nhds _ (by linarith)
    have hpre : g ⁻¹' Metric.ball (g y₀) (ε / 4) ∈ 𝓝 y₀ := (hg y₀ hy₀) hball
    have hπat : Tendsto (fun y : E => a + φ (y - a) • v) (𝓝 y₀) (𝓝 y₀) := by
      have := hπc.continuousAt (x := y₀)
      rwa [ContinuousAt, hfix] at this
    have hpre₂ : (fun y : E => a + φ (y - a) • v) ⁻¹' (g ⁻¹' Metric.ball (g y₀) (ε / 4))
        ∈ 𝓝 y₀ := hπat hpre
    refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Filter.inter_mem hpre hpre₂) ?_)
    rintro y ⟨hy1, hy2⟩
    have h1 : |g y - g y₀| < ε / 4 := by
      have := Metric.mem_ball.mp hy1
      rwa [Real.dist_eq] at this
    have h2 : |g (a + φ (y - a) • v) - g y₀| < ε / 4 := by
      have := Metric.mem_ball.mp hy2
      rwa [Real.dist_eq] at this
    have := habs (g y - g y₀) (g (a + φ (y - a) • v) - g y₀)
    simp only [sub_sub_sub_cancel_right] at this
    show h y ≤ ε / 2
    rw [hhdef]
    linarith
  obtain ⟨N, hN⟩ := eventually_subset_of_antitone_isCompact hC hmono isOpen_interior hsub
  refine ⟨N, fun k hk => ?_⟩
  have hub : δ k ≤ ε / 2 := by
    rcases (C k).eq_empty_or_nonempty with he | ⟨y0, hy0⟩
    · rw [hδdef]; simp only [he, Set.image_empty, Real.sSup_empty]; linarith
    · refine csSup_le ⟨h y0, ⟨y0, hy0, rfl⟩⟩ ?_
      rintro z ⟨y, hy, rfl⟩
      have hmem : y ∈ {y | h y ≤ ε / 2} := interior_subset (hN k hk hy)
      exact hmem
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hδ0 k)]
  linarith

/-- **A single thinness modulus for two integrands, from continuity at the limit body.**

`Arlib.exists_tendsto_transverse_modulus_pair` with `Continuous` weakened to `ContinuousAt` on
`⋂ k, C k`; the pointwise maximum of the two moduli, exactly as there. -/
theorem exists_tendsto_transverse_modulus_pair_of_continuousAt {C : ℕ → Set E}
    (hC : ∀ k, IsCompact (C k)) (hmono : ∀ k, C (k + 1) ⊆ C k) {a v : E} {φ : E →ₗ[ℝ] ℝ}
    (haxis : ∀ y ∈ ⋂ k, C k, y = a + φ (y - a) • v)
    {g₁ g₂ : E → ℝ} (hg₁ : ∀ y ∈ ⋂ k, C k, ContinuousAt g₁ y)
    (hg₂ : ∀ y ∈ ⋂ k, C k, ContinuousAt g₂ y) {M : ℝ}
    (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      (∀ k, ∀ y ∈ C k, |g₁ y - g₁ (a + φ (y - a) • v)| ≤ δ k) ∧
      ∀ k, ∀ y ∈ C k, |g₂ y - g₂ (a + φ (y - a) • v)| ≤ δ k := by
  obtain ⟨δ₁, hδ₁lim, hδ₁⟩ :=
    exists_tendsto_transverse_modulus_of_continuousAt hC hmono haxis hg₁ hM₁
  obtain ⟨δ₂, hδ₂lim, hδ₂⟩ :=
    exists_tendsto_transverse_modulus_of_continuousAt hC hmono haxis hg₂ hM₂
  refine ⟨fun k => max (δ₁ k) (δ₂ k), ?_, fun k y hy => le_max_of_le_left (hδ₁ k y hy),
    fun k y hy => le_max_of_le_right (hδ₂ k y hy)⟩
  simpa using hδ₁lim.max hδ₂lim

end ContinuityAtLimit


/-! ### The needle from continuity at the limit body alone -/

section NeedleContinuousAt

open Filter Topology

variable {m : ℕ}

/-- **`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact` with `Continuous` replaced by
`Measurable` plus continuity at the points of `⋂ k, D k`.**

The original (`Arlib/Convexity/LocalizationTransverse.lean:192`) consumes its two `Continuous`
hypotheses in exactly two ways, and nowhere else:

* `hg₁.measurable`, `hg₂.measurable`, feeding
  `Arlib.exists_needleIntegral_eq_zero_and_pos_affine`
  (`Arlib/Convexity/LocalizationAffine.lean:364`), whose integrand hypotheses are already only
  `Measurable` plus the two transverse moduli;
* `Arlib.exists_tendsto_transverse_modulus_pair`, which manufactures those moduli.

`Arlib.exists_tendsto_transverse_modulus_pair_of_continuousAt` replaces the second use, so this
statement holds with the integrands merely measurable, bounded, and continuous **at each point
of the limit body**. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact_of_continuousAt (hm : m ≠ 0)
    {a v : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ} (hφv : φ v = 1)
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDcomp : ∀ k, IsCompact (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k))
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (0 : ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t)
    (haxis : ∀ y ∈ ⋂ k, D k, y = a + φ (y - a) • v)
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁m : Measurable g₁) (hg₂m : Measurable g₂)
    (hg₁ : ∀ y ∈ ⋂ k, D k, ContinuousAt g₁ y) (hg₂ : ∀ y ∈ ⋂ k, D k, ContinuousAt g₂ y)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (a + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (a + t • v) := by
  obtain ⟨δ, hδ0, hδ₁, hδ₂⟩ :=
    exists_tendsto_transverse_modulus_pair_of_continuousAt hDcomp hDmono haxis hg₁ hg₂ hM₁ hM₂
  refine exists_needleIntegral_eq_zero_and_pos_affine hm hφv hDconv
    (fun k => (hDcomp k).isClosed.measurableSet) (fun k => (hDcomp k).measure_lt_top.ne)
    hDpos (fun k => ?_) hslab hspan hg₁m hg₂m hM₁ hM₂ hδ₁ hδ₂ hδ0
    hzero hεpos hge
  exact isBounded_iff_forall_norm_le.mp (hDcomp k).isBounded

/-- **The localisation needle from a collinear limit body, for integrands continuous only *at*
that limit body.**

This is `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear`
(`Arlib/Convexity/LocalizationClosed.lean:380`) with its two `Continuous` hypotheses replaced by

    Measurable gᵢ    and    ∀ y ∈ ⋂ k, D k, ContinuousAt gᵢ y.

It is a strict generalisation: `Continuous g` gives both (see
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt_recovers`).  The new
hypothesis is stated on `⋂ k, D k`, which is available *before* the axis is produced, so nothing
about the ordering of the argument changes.

**What this does and does not buy for indicator integrands.**  For `g = S.indicator f` with `f`
continuous, `ContinuousAt g y` holds at every `y ∉ frontier S`
(`ContinuousOn.continuousAt_indicator`), so the hypothesis becomes the geometric side condition
"the limit body misses the frontier".  It is *not* removable: by
`Arlib.exists_transverse_oscillation_eq_one`
(`Arlib/Convexity/LocalizationMeasurable.lean:550`) there is a measurable set whose transverse
oscillation is `1` on **every** body of positive volume, so no modulus tends to `0` for a
general measurable set, and by `Arlib.exists_null_measurableSet_needleIntegral_eq_one` a
Lebesgue-null set can carry needle mass `1`, which blocks every almost-everywhere reroute.  A
single point of the limit body on `frontier S` is therefore fatal **to any transverse-modulus
limit passage** — the only limit passage this repository has — so this theorem is the sharp
statement for that route.  It is *not* a statement-level counterexample: neither cited theorem
refutes the needle conclusion itself for a discontinuous integrand, and none is claimed to. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt (hm : m ≠ 0)
    {a : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ}
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDcomp : ∀ k, IsCompact (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k))
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (0 : ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t)
    (hcol : Collinear ℝ (⋂ k, D k))
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁m : Measurable g₁) (hg₂m : Measurable g₂)
    (hg₁ : ∀ y ∈ ⋂ k, D k, ContinuousAt g₁ y) (hg₂ : ∀ y ∈ ⋂ k, D k, ContinuousAt g₂ y)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ), φ v = 1 ∧ (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  obtain ⟨b, v, hb, hφv, haxis⟩ := exists_axis_of_collinear hDcomp hDmono hspan hcol
  have hshift : ∀ y : Fin (m + 1) → ℝ, φ (y - b) = φ (y - a) := by
    intro y; rw [map_sub, map_sub, hb]
  obtain ⟨W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_compact_of_continuousAt hm hφv
    hDconv hDcomp hDmono hDpos (fun k y hy => by rw [hshift]; exact hslab k y hy)
    (fun k t ht => by
      obtain ⟨y, hy, hyt⟩ := hspan k t ht
      exact ⟨y, hy, by rw [hshift]; exact hyt⟩)
    haxis hg₁m hg₂m hg₁ hg₂ hM₁ hM₂ hzero hεpos hge
  exact ⟨b, v, W, hφv, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩

/-- **The weakening is a drop-in.**

`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear` is recovered from
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt` by supplying
`hg.measurable` and `fun y _ => hg.continuousAt`, so no consumer of the continuous form loses
anything.  This is the check that the new hypotheses are genuinely *weaker* and not merely
different. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt_recovers (hm : m ≠ 0)
    {a : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ}
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDcomp : ∀ k, IsCompact (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k))
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (0 : ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t)
    (hcol : Collinear ℝ (⋂ k, D k))
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ), φ v = 1 ∧ (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) :=
  exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt hm hDconv hDcomp hDmono
    hDpos hslab hspan hcol hg₁.measurable hg₂.measurable (fun _ _ => hg₁.continuousAt)
    (fun _ _ => hg₂.continuousAt) hM₁ hM₂ hzero hεpos hge

end NeedleContinuousAt


/-! ### The needle at the Lovász–Vempala indicator pair -/

section IndicatorPair

open Filter Topology

variable {m : ℕ}

/-- `|1_S · f| ≤ c` whenever `|f| ≤ c` and `0 ≤ c`. -/
theorem abs_indicator_le {E : Type*} {S : Set E} {f : E → ℝ} {c : ℝ} (hf : ∀ x, |f x| ≤ c)
    (hc : 0 ≤ c) (x : E) : |S.indicator f x| ≤ c := by
  classical
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]; exact hf x
  · rw [Set.indicator_of_notMem hx]; simpa using hc

/-- **The localisation needle at the indicator pair of Lovász–Vempala Theorem 2.1.**

`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt` instantiated at

    g₁ = 1_{T₁} − A · 1_K,      g₂ = A · 1_K · h − 1_{S₃},

the pair `Arlib.thm21_of_localization`'s `hloc` is the Localization Lemma for (with
`S₃ = (K ∖ T₁) ∖ T₂`).  Neither integrand is continuous, so the continuous form
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear` does **not** apply to it; what is
asked instead is the geometric side condition that the limit body `⋂ k, D k` misses the three
frontiers, which is exactly `ContinuousAt` for indicators
(`ContinuousOn.continuousAt_indicator`).

**This does not discharge `hloc`.**  Three things separate it from that binder, and only the
first is about continuity:

1. the frontier-disjointness hypotheses are *not* available: the limit body is produced by the
   bisection chain and there is no control on where it lands relative to `frontier T₁`.  They
   are not removable either — see the counterexamples cited at
   `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt`;
2. `hslab`/`hspan` ask every body of the chain to lie in *and* span one fixed slab, which the
   flat-cut chain does not deliver (module docstring of `Arlib.Convexity.LocalizationClosed`,
   "What is still missing");
3. `hloc` is stated over `EuclideanSpace ℝ (Fin n)` and in the `needleMap`/`LogConcaveOn`
   idiom, whereas this lives over `Fin (m + 1) → ℝ` with a `ConcaveOn (· ^ (1/m))` profile. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_collinear_indicatorPair (hm : m ≠ 0)
    {a : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ}
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDcomp : ∀ k, IsCompact (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k))
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (0 : ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t)
    (hcol : Collinear ℝ (⋂ k, D k))
    {K T₁ S₃ : Set (Fin (m + 1) → ℝ)}
    (hKm : MeasurableSet K) (hT₁m : MeasurableSet T₁) (hS₃m : MeasurableSet S₃)
    (hKfr : Disjoint (⋂ k, D k) (frontier K))
    (hT₁fr : Disjoint (⋂ k, D k) (frontier T₁))
    (hS₃fr : Disjoint (⋂ k, D k) (frontier S₃))
    {h : (Fin (m + 1) → ℝ) → ℝ} (hh : Continuous h) (hh1 : ∀ x, |h x| ≤ 1)
    {A : ℝ} (hA1 : |A| ≤ 1)
    (hzero : ∀ k, (∫ y in D k,
        (T₁.indicator (fun _ => (1 : ℝ)) y - A * K.indicator (fun _ => (1 : ℝ)) y)) = 0)
    {ε : ℝ} (hεpos : 0 < ε)
    (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k,
        (A * K.indicator h y - S₃.indicator (fun _ => (1 : ℝ)) y)) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ), φ v = 1 ∧ (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * (T₁.indicator (fun _ => (1 : ℝ)) (b + t • v)
          - A * K.indicator (fun _ => (1 : ℝ)) (b + t • v))) = 0 ∧
      0 < ∫ t : ℝ, W t * (A * K.indicator h (b + t • v)
          - S₃.indicator (fun _ => (1 : ℝ)) (b + t • v)) := by
  classical
  have hone : ∀ (S : Set (Fin (m + 1) → ℝ)) (x : Fin (m + 1) → ℝ),
      |S.indicator (fun _ => (1 : ℝ)) x| ≤ 1 :=
    fun S x => abs_indicator_le (fun _ => by norm_num) zero_le_one x
  have hKh : ∀ x, |K.indicator h x| ≤ 1 := fun x => abs_indicator_le hh1 zero_le_one x
  refine exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt hm hDconv hDcomp
    hDmono hDpos hslab hspan hcol
    (g₁ := fun y => T₁.indicator (fun _ => (1 : ℝ)) y - A * K.indicator (fun _ => (1 : ℝ)) y)
    (g₂ := fun y => A * K.indicator h y - S₃.indicator (fun _ => (1 : ℝ)) y)
    ((measurable_const.indicator hT₁m).sub ((measurable_const.indicator hKm).const_mul A))
    (((hh.measurable).indicator hKm).const_mul A |>.sub (measurable_const.indicator hS₃m))
    (fun y hy => ?_) (fun y hy => ?_) (M := 2) (fun x => ?_) (fun x => ?_) hzero hεpos hge
  · exact (continuousOn_const.continuousAt_indicator
      (Set.disjoint_left.mp hT₁fr hy)).sub (continuousAt_const.mul
      (continuousOn_const.continuousAt_indicator (Set.disjoint_left.mp hKfr hy)))
  · exact (continuousAt_const.mul (hh.continuousOn.continuousAt_indicator
      (Set.disjoint_left.mp hKfr hy))).sub (continuousOn_const.continuousAt_indicator
      (Set.disjoint_left.mp hS₃fr hy))
  · have h1 := hone T₁ x
    have h2 := hone K x
    have h3 : |A * K.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
      rw [abs_mul]
      have : |A| * |K.indicator (fun _ => (1 : ℝ)) x| ≤ 1 * 1 :=
        mul_le_mul hA1 h2 (abs_nonneg _) zero_le_one
      linarith
    calc |T₁.indicator (fun _ => (1 : ℝ)) x - A * K.indicator (fun _ => (1 : ℝ)) x|
        ≤ |T₁.indicator (fun _ => (1 : ℝ)) x| + |A * K.indicator (fun _ => (1 : ℝ)) x| :=
          abs_sub _ _
      _ ≤ 2 := by linarith
  · have h1 := hKh x
    have h2 := hone S₃ x
    have h3 : |A * K.indicator h x| ≤ 1 := by
      rw [abs_mul]
      have : |A| * |K.indicator h x| ≤ 1 * 1 := mul_le_mul hA1 h1 (abs_nonneg _) zero_le_one
      linarith
    calc |A * K.indicator h x - S₃.indicator (fun _ => (1 : ℝ)) x|
        ≤ |A * K.indicator h x| + |S₃.indicator (fun _ => (1 : ℝ)) x| := abs_sub _ _
      _ ≤ 2 := by linarith

/-- `frontier {f < c} ⊆ {c ≤ f}` for continuous `f`: the frontier of a set is the frontier of its
complement, and the complement here is closed. -/
theorem frontier_lt_subset {E : Type*} [TopologicalSpace E] {f : E → ℝ} (hf : Continuous f)
    (c : ℝ) : frontier {y | f y < c} ⊆ {y | c ≤ f y} := by
  intro y hy
  have hcompl : {y : E | f y < c}ᶜ = {y | c ≤ f y} := by ext z; simp [not_lt]
  have hc : IsClosed {y : E | c ≤ f y} := isClosed_le continuous_const hf
  have h1 : y ∈ closure {y : E | f y < c}ᶜ := by
    rw [← frontier_compl] at hy
    exact frontier_subset_closure hy
  rwa [hcompl, hc.closure_eq] at h1

/-- **Non-vacuity of `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_indicatorPair`,
with both frontier hypotheses non-trivial.**

The shrinking boxes `D k = [0,1] × [0, 1/(k+1)]^m` of
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_box`, together with the *open
half-spaces*

    T₁ = {y | y i₀ < 2},    S₃ = {y | y i₀ < -1}    (i₀ ≠ 0 a coordinate of the thin directions),

`K = univ`, `A = 1` and `h = 1`.  Neither `T₁` nor `S₃` is trivial — `T₁` has nonempty
complement and `S₃` is nonempty, so both have a genuine frontier `{y i₀ = 2}`, `{y i₀ = -1}` —
and the limit body `⋂ k, D k`, on which `y i₀ = 0`, misses both.  So the frontier
side conditions of the indicator form are **not** satisfied only vacuously: they are the honest
geometric statement that the needle avoids the discontinuities, and that is achievable together
with every other hypothesis at once. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_collinear_indicatorPair_witness (hm : m ≠ 0) :
    ∃ (K T₁ S₃ : Set (Fin (m + 1) → ℝ)) (g : (Fin (m + 1) → ℝ) → ℝ) (A : ℝ)
      (D : ℕ → Set (Fin (m + 1) → ℝ)) (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ),
      T₁ᶜ.Nonempty ∧ S₃.Nonempty ∧
      Disjoint (⋂ k, D k) (frontier T₁) ∧ Disjoint (⋂ k, D k) (frontier S₃) ∧
      (∀ t, 0 ≤ W t) ∧ (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      (∫ t : ℝ, W t * (T₁.indicator (fun _ => (1 : ℝ)) (b + t • v)
          - A * K.indicator (fun _ => (1 : ℝ)) (b + t • v))) = 0 ∧
      0 < ∫ t : ℝ, W t * (A * K.indicator g (b + t • v)
          - S₃.indicator (fun _ => (1 : ℝ)) (b + t • v)) := by
  classical
  have hm1 : 1 < m + 1 := by omega
  set i₀ : Fin (m + 1) := ⟨1, hm1⟩ with hi₀
  have hi₀0 : i₀ ≠ 0 := by
    simp only [hi₀, Ne, Fin.ext_iff, Fin.val_zero]
    omega
  -- the shrinking boxes
  set r : ℕ → Fin (m + 1) → ℝ := fun k i => if i = 0 then 1 else 1 / ((k : ℝ) + 1) with hr
  have hrpos : ∀ k i, 0 < r k i := by
    intro k i
    rw [hr]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      positivity
  have hrle : ∀ k i, r k i ≤ 1 := by
    intro k i
    rw [hr]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
  set D : ℕ → Set (Fin (m + 1) → ℝ) := fun k => univ.pi fun i => Icc (0 : ℝ) (r k i) with hD
  have hDcomp : ∀ k, IsCompact (D k) := fun k => isCompact_univ_pi fun _ => isCompact_Icc
  have hDconv : ∀ k, Convex ℝ (D k) := fun k => convex_pi fun _ _ => convex_Icc _ _
  have hDmono : ∀ k, D (k + 1) ⊆ D k := by
    intro k y hy
    refine Set.mem_univ_pi.mpr fun i => ?_
    have hyi := Set.mem_univ_pi.mp hy i
    refine Set.Icc_subset_Icc_right ?_ hyi
    rw [hr]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h2 : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
      exact one_div_le_one_div_of_le h1 h2
  have hvol : ∀ k, volume (D k) = ∏ i : Fin (m + 1), ENNReal.ofReal (r k i) := by
    intro k
    rw [hD]
    simp only [volume_pi_pi, Real.volume_Icc, sub_zero]
  have hDpos : ∀ k, 0 < volume (D k) := by
    intro k
    rw [hvol k, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ => (ENNReal.ofReal_pos.mpr (hrpos k i)).ne'
  set φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0 with hφ
  have hslab : ∀ k, ∀ y ∈ D k, φ (y - 0) ∈ Icc (0 : ℝ) 1 := by
    intro k y hy
    have h0 := Set.mem_univ_pi.mp hy 0
    rw [hr] at h0
    simpa [hφ] using h0
  have hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - 0) = t := by
    intro k t ht
    refine ⟨fun i => if i = 0 then t else 0, Set.mem_univ_pi.mpr fun i => ?_, by simp [hφ]⟩
    by_cases hi : i = 0
    · simp only [hi, if_true, hr]
      simpa using ht
    · simp only [hi, if_false]
      exact ⟨le_rfl, (hrpos k i).le⟩
  have hcol : Collinear ℝ (⋂ k, D k) := by
    refine (collinear_iff_of_mem (p₀ := (0 : Fin (m + 1) → ℝ)) ?_).mpr
      ⟨Pi.single 0 1, fun y hy => ⟨y 0, ?_⟩⟩
    · refine Set.mem_iInter.mpr fun k => Set.mem_univ_pi.mpr fun i => ?_
      exact ⟨le_rfl, (hrpos k i).le⟩
    · have hy' : ∀ k, y ∈ D k := fun k => Set.mem_iInter.mp hy k
      have hzero : ∀ i : Fin (m + 1), i ≠ 0 → y i = 0 := by
        intro i hi
        refine le_antisymm ?_ ((Set.mem_univ_pi.mp (hy' 0) i).1)
        by_contra hcon
        rw [not_le] at hcon
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hcon
        have := (Set.mem_univ_pi.mp (hy' n) i).2
        rw [hr] at this
        simp only [hi, if_false] at this
        linarith
      funext i
      by_cases hi : i = 0
      · simp [hi]
      · simp [hi, hzero i hi]
  -- the coordinate `i₀` is bounded by `1` on every body and is `≥ 0` there
  have hcoord : ∀ k, ∀ y ∈ D k, 0 ≤ y i₀ ∧ y i₀ ≤ 1 := by
    intro k y hy
    obtain ⟨h1, h2⟩ := Set.mem_univ_pi.mp hy i₀
    exact ⟨h1, le_trans h2 (hrle k i₀)⟩
  have hproj : Continuous fun y : Fin (m + 1) → ℝ => y i₀ := continuous_apply i₀
  set T₁ : Set (Fin (m + 1) → ℝ) := {y | y i₀ < 2} with hT₁
  set S₃ : Set (Fin (m + 1) → ℝ) := {y | y i₀ < -1} with hS₃
  have hT₁m : MeasurableSet T₁ := (isOpen_lt hproj continuous_const).measurableSet
  have hS₃m : MeasurableSet S₃ := (isOpen_lt hproj continuous_const).measurableSet
  have hT₁fr : Disjoint (⋂ k, D k) (frontier T₁) := by
    rw [Set.disjoint_left]
    intro y hy hyf
    have h1 : (2 : ℝ) ≤ y i₀ := frontier_lt_subset hproj 2 hyf
    have h2 := (hcoord 0 y (Set.mem_iInter.mp hy 0)).2
    linarith
  have hS₃fr : Disjoint (⋂ k, D k) (frontier S₃) := by
    rw [Set.disjoint_left]
    intro y hy hyf
    have h2 := (hcoord 0 y (Set.mem_iInter.mp hy 0)).1
    -- the frontier lies in `closure S₃ ⊆ {y i₀ ≤ -1}`, which the body's `0 ≤ y i₀` refutes
    have h3 : y i₀ ≤ -1 := by
      have hmem : y ∈ closure S₃ := frontier_subset_closure hyf
      have hcl : closure S₃ ⊆ {y : Fin (m + 1) → ℝ | y i₀ ≤ -1} :=
        closure_minimal (fun z hz => le_of_lt (show z i₀ < -1 from hz))
          (isClosed_le hproj continuous_const)
      exact hcl hmem
    linarith
  -- the two mass hypotheses
  have hDm : ∀ k, MeasurableSet (D k) := fun k => (hDcomp k).isClosed.measurableSet
  have hzero : ∀ k, (∫ y in D k,
      (T₁.indicator (fun _ => (1 : ℝ)) y - (1 : ℝ) * Set.univ.indicator (fun _ => (1 : ℝ)) y))
        = 0 := by
    intro k
    have hcongr : (∫ y in D k,
        (T₁.indicator (fun _ => (1 : ℝ)) y - (1 : ℝ) * Set.univ.indicator (fun _ => (1 : ℝ)) y))
          = ∫ _ in D k, (0 : ℝ) := by
      refine setIntegral_congr_fun (hDm k) fun y hy => ?_
      have hyT : y ∈ T₁ := by
        have := (hcoord k y hy).2
        show y i₀ < 2
        linarith
      rw [Set.indicator_of_mem hyT, Set.indicator_of_mem (Set.mem_univ y)]
      norm_num
    rw [hcongr, integral_zero]
  have hge : ∀ k, (1 : ℝ) * (volume (D k)).toReal ≤ ∫ y in D k,
      ((1 : ℝ) * Set.univ.indicator (fun _ => (1 : ℝ)) y
        - S₃.indicator (fun _ => (1 : ℝ)) y) := by
    intro k
    have hcongr : (∫ y in D k, ((1 : ℝ) * Set.univ.indicator (fun _ => (1 : ℝ)) y
        - S₃.indicator (fun _ => (1 : ℝ)) y)) = ∫ _ in D k, (1 : ℝ) := by
      refine setIntegral_congr_fun (hDm k) fun y hy => ?_
      have hyS : y ∉ S₃ := by
        have := (hcoord k y hy).1
        show ¬ y i₀ < -1
        linarith
      rw [Set.indicator_of_notMem hyS, Set.indicator_of_mem (Set.mem_univ y)]
      norm_num
    rw [hcongr, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, one_mul]
  obtain ⟨b, v, W, -, hW0, hWsupp, hWint, -, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_collinear_indicatorPair hm hDconv hDcomp hDmono
      hDpos hslab hspan hcol (K := Set.univ) MeasurableSet.univ hT₁m hS₃m
      (by simp) hT₁fr hS₃fr
      (h := fun _ => (1 : ℝ)) continuous_const (fun _ => by norm_num) (A := 1)
      (by norm_num) hzero (ε := 1) one_pos hge
  refine ⟨Set.univ, T₁, S₃, fun _ => (1 : ℝ), 1, D, b, v, W, ⟨fun _ => 3, ?_⟩, ⟨fun _ => -2, ?_⟩,
    hT₁fr, hS₃fr, hW0, hWsupp, hWint, hW₁, hW₂⟩
  · show ¬ ((3 : ℝ) < 2)
    norm_num
  · show (-2 : ℝ) < -1
    norm_num

end IndicatorPair

/-! ### Axiom audit -/

section AxiomCheck

#print axioms Arlib.needle_iso_two_lower
#print axioms Arlib.counter_isPartition3
#print axioms Arlib.not_needle_iso_of_one_lower
#print axioms Arlib.needle_iso_of_chord_two_lower
#print axioms Arlib.thm21_of_localization_two_lower
#print axioms Arlib.continuous_axisRetract
#print axioms Arlib.exists_tendsto_transverse_modulus_of_continuousAt
#print axioms Arlib.exists_tendsto_transverse_modulus_pair_of_continuousAt
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_of_continuousAt
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_of_continuousAt_recovers
#print axioms Arlib.abs_indicator_le
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_indicatorPair
#print axioms Arlib.frontier_lt_subset
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_indicatorPair_witness

end AxiomCheck

end Arlib
