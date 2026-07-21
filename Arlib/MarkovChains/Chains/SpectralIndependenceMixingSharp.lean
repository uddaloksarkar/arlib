/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Spectral independence implies a spectral gap for Glauber — the sharp constant

`Chains.SpectralIndependenceMixing` assembles the monograph's central theorem and
pays for one design choice upstream: `Techniques.ImprovedRandomWalk` multiplies its
induction through by `2γ_j - 1`, so it needs `γ_j ≥ 1/2`, which at the binding
level (two free sites, `γ = 2 - η`) reads **`η ≤ 3/2`** — and the constant is
already `0` there.  `Techniques.ImprovedRandomWalkSharp` now supplies
the same theorem with the level factor `γ_j/(2 - γ_j)` of `[CLV21, Fact A.8]`,
which needs only `0 ≤ γ_j ≤ 2`.  This module repoints the assembly at it.

**Which side conditions actually bind.**  With `γ_j = siGamma n η j = ((n-j) - η)/((n-j) - 1)`
and `d = n - j - 1 ≥ 1` free sites minus one, so that `γ_j = (d + 1 - η)/d`:

| side condition | equivalent constraint | binding level |
| --- | --- | --- |
| `0 ≤ 2γ_j - 1` (old) | `η ≤ 3/2` | `d = 1` |
| `0 ≤ γ_j` (new) | `η ≤ 2` | `d = 1` |
| `γ_j ≤ 2` (both) | `0 ≤ η` | `d = 1` |

So the sharp route's *provability* hypothesis is `η ≤ 2` alone: `0 ≤ η` is not
assumed but **derived**, exactly as in the unsharpened module, by
`nonneg_of_spectralIndependence` at the empty pinning.  This is the first place
the natural guess `0 < η < 2` is wrong — the theorem is true, and stated below,
under `η ≤ 2`.

**Where `0 < η < 2` is the right range.**  It is the range on which the constant
is *positive*, i.e. on which the theorem has content, and there it is two-sided
for a genuine reason.  `sharpStep γ_j = (d + 1 - η)/(d - 1 + η)`
(`sharpStep_siGamma`), so:

* at `η = 2` the numerator vanishes at `d = 1` and the constant is `0`;
* at `η = 0` the *denominator* vanishes at `d = 1` — the level gap is exactly
  `γ = 2` — and Lean's `x/0 = 0` makes the constant `0` again.

The second degeneracy has no analogue in the old route, where `2γ - 1 = 3` at
`γ = 2`.  It is `Techniques.ImprovedRandomWalkSharp.sharpStep_two_lt_two_mul_sub_one`
instantiated, and it is why the sharp theorem is **not** a strict improvement:
`0 ≤ η` is free, and at `η = 0` the old theorem has a positive constant while this
one does not.  The monograph's classical `|η₀| < 1` is `0 < η < 2` for the same
reason.

That loss is confined to one measure.  By
`Techniques.SpectralIndependence.one_sub_marg_le_of_spectralIndependence`, `η = 0`
forces every charged marginal to be `1`, so it can only happen at a point mass
(`pos_of_spectralIndependence_of_marg_lt_one`).  The `3/2 < η < 2` gain is not
confined in any such way.

**What is gained, precisely.**  On the overlap `0 < η ≤ 3/2` both theorems apply
and this one is at least as strong, denominators included
(`improvedFactor_div_le_sharpFactor_div_siGamma`, an instantiation of the abstract
comparison, followed by `spectralGapAtLeast_glauber_of_spectralIndependence_le_sharp`,
which *derives* the old theorem's conclusion from this one's).  On
`3/2 < η < 2` the old route has no statement at all — its side condition is
violated at the level `j = n - 2`, with the strictly negative value `3 - 2η`
(`two_mul_siGamma_sub_one_neg`) — while this one gives a strictly positive
constant (`spectralGapAtLeast_glauber_of_spectralIndependence_sharp_pos`).

**The calibration survives.**  `sharpStep 1 = 1 = 2·1 - 1`, so at `η = 1` every
`Γ_i` is `1`, the sum is `n`, and the constant is exactly `1/n` — the same real
expression the unsharpened module reaches and the same one
`Chains.ProductMeasure.approxTensorization_prodWeight` reaches by approximate
tensorization.  The product-measure corollary is therefore restated through the
sharp route, and `spectralGapAtLeast_glauber_prodWeight_audit_sharp` exhibits the
three proofs of the identical proposition side by side.

**Main declarations.**

* `siGamma_nonneg`, `siGamma_lt_two` — the two side conditions of the sharp
  Improved Random Walk Theorem, checked against `siGamma`: `0 ≤ γ_j` is `η ≤ 2`,
  and `γ_j < 2` (the strict form the comparison needs) is `0 < η`.
* **`sharpStep_siGamma`** — the sharp level factor in closed form,
  `(d + 1 - η)/(d - 1 + η)`, and `sharpStep_siGamma_pos`.
* `sharpStep_one`, `sharpFactor_const_one`, `sharpFactor_siGamma_pos`,
  `sharpFactor_siGamma_div_pos` — the calibration and the positivity of the
  constant.
* **`two_mul_siGamma_sub_one_neg`** — on `3/2 < η` the old side condition fails,
  strictly, at the level `j = n - 2`.  This is the precise sense in which the old
  theorem says nothing there.
* **`spectralGapAtLeast_glauber_of_spectralIndependence_sharp`** — **the headline**:
  spectral independence at every pinning, `η ≤ 2`, gives the Glauber dynamics the
  Poincaré constant `Γ_m/∑_{i≤m} Γ_i` with `Γ_i = ∏_{j<i} γ_j/(2 - γ_j)`.
* `spectralGapAtLeast_glauber_of_spectralIndependence_sharp_pos` — the same with
  the constant certified positive, on `0 < η < 2`.
* **`improvedFactor_div_le_sharpFactor_div_siGamma`** and
  **`spectralGapAtLeast_glauber_of_spectralIndependence_le_sharp`** — the
  comparison, proved rather than asserted, on `0 < η ≤ 3/2`.
* `pos_of_spectralIndependence_of_marg_lt_one` — the lower endpoint of that
  overlap is free for every measure that is not a point mass.
* **`spectralGapAtLeast_glauber_of_spectralIndependence_sharp_one`**,
  `spectralGapAtLeast_glauber_of_pairwiseIndep_sharp`,
  `spectralGapAtLeast_glauber_prodWeight_via_spectralIndependence_sharp`,
  `spectralGapAtLeast_glauber_prodWeight_audit_sharp` — the calibration point and
  the product-measure audit, through the sharp route.

Everything here is proved from first principles with no `sorry`; in particular no
eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Techniques.ImprovedRandomWalkSharp
import Arlib.MarkovChains.Chains.ProductSpectralIndependence

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The side conditions of the sharp theorem, at `siGamma`

`Techniques.ImprovedRandomWalkSharp` asks for `0 ≤ γ_j` and `γ_j ≤ 2` at *every*
`j : ℕ`, including the levels above the dimension of the complex, where `siGamma`
returns the junk value `1`.  Both conditions hold there with room, so what follows
is entirely about the levels `j + 1 < n`, where `siGamma n η j = (N - η)/(N - 1)`
with `N = n - j ≥ 2` free sites.

`Chains.SpectralIndependenceMixing.siGamma_le_two` already proves the second
condition from `0 ≤ η` and is reused verbatim; the two new facts are that `0 ≤ γ_j`
is `η ≤ 2` rather than `η ≤ 3/2`, and that the *strict* `γ_j < 2` needed by the
comparison is `0 < η`. -/

section Gamma

/-- **The first side condition of the sharp theorem, `0 ≤ γ_j`, is `η ≤ 2`.**

The numerator `(n - j) - η` is smallest at the last level, where `n - j = 2` and it
is `2 - η`.  So `η ≤ 2` is sharp for this family, and it replaces the `η ≤ 3/2` of
`Chains.SpectralIndependenceMixing.two_mul_siGamma_sub_one_nonneg` — which is the
same computation for `2γ_j - 1 = ((n-j) + 1 - 2η)/((n-j) - 1)`, whose numerator at
`n - j = 2` is `3 - 2η`. -/
theorem siGamma_nonneg {n : ℕ} {η : ℝ} (hη : η ≤ 2) (j : ℕ) : 0 ≤ siGamma n η j := by
  by_cases h : j + 1 < n
  · have hN := two_le_cast_natSub h
    rw [siGamma_of_lt h]
    exact div_nonneg (by linarith) (by linarith)
  · rw [siGamma, if_neg h]
    norm_num

/-- **The strict form of the second side condition, `γ_j < 2`, is `0 < η`.**

`Chains.SpectralIndependenceMixing.siGamma_le_two` gets the non-strict `γ_j ≤ 2`
from `0 ≤ η`, and that is all the sharp theorem needs.  The *strict* inequality is
what `Techniques.ImprovedRandomWalkSharp.improvedFactor_div_le_sharpFactor_div`
requires, and it costs the extra `0 < η`: at `η = 0` the last level has
`γ = 2` exactly, where the sharp factor degenerates to `0`. -/
theorem siGamma_lt_two {n : ℕ} {η : ℝ} (hη : 0 < η) (j : ℕ) : siGamma n η j < 2 := by
  by_cases h : j + 1 < n
  · have hN := two_le_cast_natSub h
    have hd : (0 : ℝ) < ((n - j : ℕ) : ℝ) - 1 := by linarith
    rw [siGamma_of_lt h, div_lt_iff₀ hd]
    linarith
  · rw [siGamma, if_neg h]
    norm_num

/-- **The sharp level factor at the gaps spectral independence produces**, in
closed form:

  **`sharpStep (siGamma n η j) = ((n - j) - η)/((n - j) - 2 + η)`,**

that is `(d + 1 - η)/(d - 1 + η)` with `d = n - j - 1` the number of free sites
minus one.  Compare `two_mul_siGamma_sub_one`, which gives `(d + 2 - 2η)/d`.

This is `Techniques.ImprovedRandomWalkSharp.sharpStep_free_sites` with `d` taken to
be the real number `(n - j) - 1`; no hypothesis on the denominator is needed,
because at `(n - j) - 2 + η = 0` both sides are `0` by Lean's division
convention. -/
theorem sharpStep_siGamma {n j : ℕ} (h : j + 1 < n) (η : ℝ) :
    sharpStep (siGamma n η j)
      = (((n - j : ℕ) : ℝ) - η) / (((n - j : ℕ) : ℝ) - 2 + η) := by
  have hN := two_le_cast_natSub h
  have hd : ((n - j : ℕ) : ℝ) - 1 ≠ 0 := by intro hc; linarith
  have key := sharpStep_free_sites (d := ((n - j : ℕ) : ℝ) - 1) (η := η) hd
  have e1 : ((n - j : ℕ) : ℝ) - 1 + 1 - η = ((n - j : ℕ) : ℝ) - η := by ring
  have e2 : ((n - j : ℕ) : ℝ) - 1 - 1 + η = ((n - j : ℕ) : ℝ) - 2 + η := by ring
  rw [e1, e2] at key
  rw [siGamma_of_lt h, key]

/-- **The sharp factor is strictly positive at every real level, for `0 < η < 2`.**
The numerator `(n - j) - η` is at least `2 - η > 0` and the denominator
`(n - j) - 2 + η` is at least `η > 0`.

Both endpoints are needed and neither is an artefact: at `η = 2` the numerator
vanishes at the last level, at `η = 0` the denominator does.  Contrast the old
factor `2γ_j - 1`, which is positive for every `η < 3/2` including `η ≤ 0`. -/
theorem sharpStep_siGamma_pos {n j : ℕ} (h : j + 1 < n) {η : ℝ} (h0 : 0 < η) (h2 : η < 2) :
    0 < sharpStep (siGamma n η j) := by
  have hN := two_le_cast_natSub h
  rw [sharpStep_siGamma h]
  exact div_pos (by linarith) (by linarith)

/-- `sharpStep 1 = 1`, the calibration identity: the sharp factor and the
monograph's `2γ - 1` agree exactly at `γ = 1`, which by
`Techniques.ImprovedRandomWalkSharp.sharpStep_sub_two_mul_sub_one` is the *only*
place below `2` where they agree. -/
@[simp] theorem sharpStep_one : sharpStep 1 = 1 := by
  rw [sharpStep]; norm_num

/-- All the sharp factors are `1` when all the level gaps are — the exact analogue
of `Chains.SpectralIndependenceMixing.improvedFactor_one`, and the reason the
`η = 1` calibration is unchanged by the sharpening. -/
theorem sharpFactor_const_one (i : ℕ) : sharpFactor (fun _ => (1 : ℝ)) i = 1 :=
  Finset.prod_eq_one fun j _ => by rw [sharpStep_one]

/-- **`Γ_m > 0` for `0 < η < 2`.**  Every factor of the product `∏_{j<m}` sits at a
level `j + 1 ≤ m < n` that the complex actually has, so `sharpStep_siGamma_pos`
applies to each. -/
theorem sharpFactor_siGamma_pos (n : ℕ) {η : ℝ} (h0 : 0 < η) (h2 : η < 2) {m : ℕ}
    (hm : m < n) : 0 < sharpFactor (siGamma n η) m :=
  Finset.prod_pos fun j hj =>
    sharpStep_siGamma_pos (by have := Finset.mem_range.mp hj; omega) h0 h2

/-- **The constant of the sharp theorem is strictly positive on `0 < η < 2`.**
The denominator `∑_{i≤m} Γ_i` is at least `1` by `one_le_sum_sharpFactor`, so this
is `sharpFactor_siGamma_pos` divided by a positive number.

This is the whole gain on `3/2 < η < 2`: there the numerator here is positive,
while the old route's hypothesis is not merely unhelpful but false
(`two_mul_siGamma_sub_one_neg`). -/
theorem sharpFactor_siGamma_div_pos {η : ℝ} (h0 : 0 < η) (h2 : η < 2) (m : ℕ) :
    0 < sharpFactor (siGamma (m + 1) η) m
      / ∑ i ∈ Finset.range (m + 1), sharpFactor (siGamma (m + 1) η) i := by
  have hS : (0 : ℝ) < ∑ i ∈ Finset.range (m + 1), sharpFactor (siGamma (m + 1) η) i :=
    lt_of_lt_of_le zero_lt_one
      (one_le_sum_sharpFactor (fun j => siGamma_nonneg h2.le j)
        (fun j => siGamma_le_two h0.le j) m)
  exact div_pos (sharpFactor_siGamma_pos (m + 1) h0 h2 (Nat.lt_succ_self m)) hS

/-- **Above `η = 3/2` the old side condition fails strictly.**

For `2 ≤ n` and `3/2 < η` the level `j = n - 2` — two free sites — has
`2·siGamma n η (n-2) - 1 = 3 - 2η < 0`.  So on `3/2 < η` the hypothesis of
`Techniques.ImprovedRandomWalk` is not merely unavailable: it is refuted, its
`Γ_i` alternate in sign, and `Chains.SpectralIndependenceMixing` has no statement
to make.  That is the precise content of "the old theorem says nothing" on
`3/2 < η < 2`. -/
theorem two_mul_siGamma_sub_one_neg {n : ℕ} (hn : 2 ≤ n) {η : ℝ} (hη : 3 / 2 < η) :
    2 * siGamma n η (n - 2) - 1 < 0 := by
  have h : (n - 2) + 1 < n := by omega
  have hN : (n - (n - 2) : ℕ) = 2 := by omega
  rw [two_mul_siGamma_sub_one h, hN]
  norm_num
  linarith

end Gamma

/-! ## The headline, sharpened

The proof is `Chains.SpectralIndependenceMixing`'s, with
`Techniques.LocalWalkBridge.downUp_top_spectralGapAtLeast_of_localWalk_gap`
replaced by
`Techniques.ImprovedRandomWalkSharp.downUp_top_spectralGapAtLeast_sharp_of_localWalk_gap`
and the side condition `0 ≤ 2γ_j - 1` replaced by `0 ≤ γ_j`.  The hypothesis
shapes are otherwise identical, so every join lemma of that module —
`exists_pinGraph_of_mu_pos`, `gibbsPin_gibbsWeight`,
`spectralGapAtLeast_localWalk_of_spectralIndependence` — is reused unchanged. -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **Spectral independence at every pinning implies a spectral gap for the
Glauber dynamics — with the sharp constant.**

Let `w` be a nonnegative weight on configurations with `Z w > 0`, on `n = m + 1`
sites, and suppose every conditional Gibbs measure `μ_ζ` is `η`-spectrally
independent, with `η ≤ 2`.  Then the Glauber dynamics of `w` satisfies the
Poincaré inequality with constant

  **`Γ_m / ∑_{i ≤ m} Γ_i`,  `Γ_i = ∏_{j < i} siGamma (m+1) η j / (2 - siGamma (m+1) η j)`,**

and `sharpStep (siGamma (m+1) η j) = ((m + 1 - j) - η)/((m + 1 - j) - 2 + η)` by
`sharpStep_siGamma`.  Reindexed by the number `d = m - j` of free sites minus one,
the numerator is `Γ_m = ∏_{d=1}^{m} (d + 1 - η)/(d - 1 + η)`.

*Three remarks on the hypotheses, in the shape of the unsharpened theorem's.*

`0 ≤ η` is **not** assumed: it is derived, by `nonneg_of_spectralIndependence`
applied to the empty pinning, and it is exactly what the side condition `γ_j ≤ 2`
needs.

`η ≤ 2` replaces the `η ≤ 3/2` of
`Chains.SpectralIndependenceMixing.spectralGapAtLeast_glauber_of_spectralIndependence`
and is sharp for this route: at `η > 2` the last level has a negative gap.  At
`η = 2`, and also at `η = 0`, the constant is `0` and the statement is vacuous;
`spectralGapAtLeast_glauber_of_spectralIndependence_sharp_pos` is the version with
the constant certified positive.

Spectral independence is required at **every** pinning, including the empty
one. -/
theorem spectralGapAtLeast_glauber_of_spectralIndependence_sharp
    (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ}
    (hm : Fintype.card V = m + 1) {η : ℝ} (hη : η ≤ 2)
    (hSI : ∀ (Λ : Finset V) (ζ : V → S) (hZΛ : 0 < Z (pinWeight w Λ ζ)),
      SpectralIndependence (gibbsPin w hw Λ ζ hZΛ) η) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw)
      (sharpFactor (siGamma (m + 1) η) m
        / ∑ i ∈ Finset.range (m + 1), sharpFactor (siGamma (m + 1) η) i) := by
  -- `0 ≤ η` comes free, from the hypothesis at the empty pinning.
  have hsum : ∑ σ : V → S, w σ ≠ 0 := by rw [← Z_apply]; exact hZ.ne'
  obtain ⟨σ₀, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hZe : 0 < Z (pinWeight w ∅ σ₀) := by rw [pinWeight_empty]; exact hZ
  have hη0 : 0 ≤ η := nonneg_of_spectralIndependence (hSI ∅ σ₀ hZe)
  -- the encoded complex, built from the normalised weight
  have hWn : ∀ T : Finset (V × S), 0 ≤ graphWeight (gibbsWeight w) T :=
    graphWeight_nonneg (gibbsWeight_nonneg hw hZ)
  have hWs : ∀ T : Finset (V × S), T.card ≠ m + 1 → graphWeight (gibbsWeight w) T = 0 :=
    graphWeight_supp' (gibbsWeight w) hm
  have hWsum : ∑ T : Finset (V × S), graphWeight (gibbsWeight w) T = 1 := by
    rw [graphWeight_sum]
    exact gibbsWeight_sum hZ
  rw [← spectralGapAtLeast_glauber_iff w hw hZ hm]
  refine downUp_top_spectralGapAtLeast_sharp_of_localWalk_gap (graphWeight (gibbsWeight w)) m
    hWn hWs hWsum (siGamma (m + 1) η) (siGamma_nonneg hη) (siGamma_le_two hη0) ?_
  intro j hj τ hcard hpos
  -- the face is the graph of a pinning
  obtain ⟨Λ, ζ, hpg, hcardΛ⟩ := exists_pinGraph_of_mu_pos hpos
  subst hpg
  have hZ1 : 0 < Z (pinWeight (gibbsWeight w) Λ ζ) := by
    rwa [mu_graphWeight_pinGraph] at hpos
  have hZ2 : 0 < Z (pinWeight w Λ ζ) := by
    have h := hZ1
    rw [Z_pinWeight_gibbsWeight] at h
    rcases div_pos_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd h2 (not_lt.mpr hZ.le)
  have hSI' : SpectralIndependence
      (gibbsPin (gibbsWeight w) (gibbsWeight_nonneg hw hZ) Λ ζ hZ1) η := by
    rw [gibbsPin_gibbsWeight w hw hZ Λ ζ hZ1 hZ2]
    exact hSI Λ ζ hZ2
  have hgap := spectralGapAtLeast_localWalk_of_spectralIndependence (gibbsWeight w)
    (gibbsWeight_nonneg hw hZ) (m + 1) hm Λ ζ hZ1 hSI' hWn hWs hpos (by omega) (by omega)
  have hnf : numFree Λ = ((m + 1 - j : ℕ) : ℝ) := by
    simp only [numFree]
    rw [hm, hcardΛ, hcard]
  rw [siGamma_of_lt hj, ← hnf]
  exact hgap

/-- **The sharp theorem with the constant certified positive, on `0 < η < 2`.**

This is the statement to quote.  `0 < η < 2` is the monograph's classical
`|η₀| < 1`, and both endpoints are genuine degeneracies of the *sharp* factor
`(d + 1 - η)/(d - 1 + η)` at the binding level `d = 1`: the numerator vanishes at
`η = 2`, the denominator at `η = 0`.

On `3/2 < η < 2` this is a bound that
`Chains.SpectralIndependenceMixing.spectralGapAtLeast_glauber_of_spectralIndependence`
cannot state at all — see `two_mul_siGamma_sub_one_neg`. -/
theorem spectralGapAtLeast_glauber_of_spectralIndependence_sharp_pos
    (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ}
    (hm : Fintype.card V = m + 1) {η : ℝ} (hη0 : 0 < η) (hη : η < 2)
    (hSI : ∀ (Λ : Finset V) (ζ : V → S) (hZΛ : 0 < Z (pinWeight w Λ ζ)),
      SpectralIndependence (gibbsPin w hw Λ ζ hZΛ) η) :
    0 < sharpFactor (siGamma (m + 1) η) m
        / ∑ i ∈ Finset.range (m + 1), sharpFactor (siGamma (m + 1) η) i
      ∧ SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw)
        (sharpFactor (siGamma (m + 1) η) m
          / ∑ i ∈ Finset.range (m + 1), sharpFactor (siGamma (m + 1) η) i) :=
  ⟨sharpFactor_siGamma_div_pos hη0 hη m,
    spectralGapAtLeast_glauber_of_spectralIndependence_sharp w hw hZ hm hη.le hSI⟩

end Main

/-! ## The comparison, proved rather than asserted

`Techniques.ImprovedRandomWalkSharp.improvedFactor_div_le_sharpFactor_div` compares
the two constants for an abstract family `γ` under `1/2 ≤ γ_j < 2`.  Instantiated
at `siGamma` those two hypotheses become `η ≤ 3/2` and `0 < η`, so the overlap on
which the sharp theorem provably dominates the old one is `0 < η ≤ 3/2`.

The lower endpoint is not slack.  At `η = 0` the old theorem still applies —
`0 ≤ η` is all `siGamma_le_two` needs — and its constant is positive, while the
sharp constant is `0`.  So the sharpening is a strict improvement only on
`0 < η`, and it is a genuine loss at `η = 0`, in exactly the way
`Techniques.ImprovedRandomWalkSharp` warns for `γ = 2`. -/

section Comparison

/-- **The comparison of the two constants, at the level gaps of spectral
independence.**  For `0 < η ≤ 3/2`,

  **`Γ^{old}_m / ∑_{i≤m} Γ^{old}_i  ≤  Γ^{new}_m / ∑_{i≤m} Γ^{new}_i`.**

This is `Techniques.ImprovedRandomWalkSharp.improvedFactor_div_le_sharpFactor_div`
with its two abstract hypotheses discharged: `0 ≤ 2γ_j - 1` by
`two_mul_siGamma_sub_one_nonneg` (that is `η ≤ 3/2`) and the strict `γ_j < 2` by
`siGamma_lt_two` (that is `0 < η`).

It is not a formality — the sharp factors are larger, but they occur in the
denominator too, so the comparison only survives after cross-multiplying. -/
theorem improvedFactor_div_le_sharpFactor_div_siGamma {n : ℕ} {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 3 / 2) (m : ℕ) :
    improvedFactor (siGamma n η) m / ∑ i ∈ Finset.range (m + 1), improvedFactor (siGamma n η) i
      ≤ sharpFactor (siGamma n η) m / ∑ i ∈ Finset.range (m + 1), sharpFactor (siGamma n η) i :=
  improvedFactor_div_le_sharpFactor_div (two_mul_siGamma_sub_one_nonneg hη)
    (siGamma_lt_two hη0) m

end Comparison

section NonDegenerate

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **`0 < η` is free unless the measure is deterministic at every site.**

`Techniques.SpectralIndependence.one_sub_marg_le_of_spectralIndependence` says
`1 - μ(σ_v = s) ≤ η` at every charged pair, so a single site whose marginal is
strictly between `0` and `1` already forces `η > 0`.

This is what rescues the comparison.  The `0 < η` hypothesis of
`improvedFactor_div_le_sharpFactor_div_siGamma` and
`spectralGapAtLeast_glauber_of_spectralIndependence_le_sharp` looks like a new
restriction, and formally it is one — but `η = 0` forces every charged marginal to
be `1`, i.e. forces the measure to be a point mass.  On every measure that is not
a point mass, `0 < η` holds automatically and the sharp constant is at least the
old one.  The `η = 0` loss recorded in the module docstring is therefore confined
to a single degenerate measure, whereas the `3/2 < η < 2` gain is not. -/
theorem pos_of_spectralIndependence_of_marg_lt_one {μ : FinDist (V → S)} {η : ℝ}
    (h : SpectralIndependence μ η) {p : V × S} (hp : 0 < marg μ p) (hlt : marg μ p < 1) :
    0 < η := by
  have := one_sub_marg_le_of_spectralIndependence h hp
  linarith

end NonDegenerate

section CompareMain

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **The sharp theorem implies the old one, on the overlap `0 < η ≤ 3/2`.**

The conclusion here is *literally the statement* of
`Chains.SpectralIndependenceMixing.spectralGapAtLeast_glauber_of_spectralIndependence`,
derived from the sharp theorem by `improvedFactor_div_le_sharpFactor_div_siGamma`
and `SpectralGapAtLeast.mono`.  So on `0 < η ≤ 3/2` nothing is lost by working
with the sharp constant, and by `sharpStep_sub_two_mul_sub_one` the gain is
`2(γ_j - 1)²/(2 - γ_j)` at each level — zero only at `η = 1`, and divergent as the
level gap approaches `2`.

The hypothesis `0 < η` is the only thing this direction adds, it is exactly
the `γ_j < 2` that the abstract comparison cannot drop, and by
`pos_of_spectralIndependence_of_marg_lt_one` it is automatic for every measure
that is not a point mass. -/
theorem spectralGapAtLeast_glauber_of_spectralIndependence_le_sharp
    (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ}
    (hm : Fintype.card V = m + 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 3 / 2)
    (hSI : ∀ (Λ : Finset V) (ζ : V → S) (hZΛ : 0 < Z (pinWeight w Λ ζ)),
      SpectralIndependence (gibbsPin w hw Λ ζ hZΛ) η) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw)
      (improvedFactor (siGamma (m + 1) η) m
        / ∑ i ∈ Finset.range (m + 1), improvedFactor (siGamma (m + 1) η) i) :=
  (spectralGapAtLeast_glauber_of_spectralIndependence_sharp w hw hZ hm
      (by linarith) hSI).mono
    (improvedFactor_div_le_sharpFactor_div_siGamma hη0 hη m)

end CompareMain

/-! ## The calibration, and the product-measure audit

`sharpStep 1 = 1 = 2·1 - 1`, so the two routes agree exactly at `η = 1`: every
level gap is `1`, every `Γ_i` is `1`, the sum is `n`, and the constant is `1/n` on
the nose.  This is the check that mattered — a discrepancy here would have meant
one of the two Improved Random Walk Theorems was wrong — and it passes.

`Chains.ProductSpectralIndependence` discharges the hypothesis at `η = 1` for a
real weight, so the corollary below is unconditional, and
`spectralGapAtLeast_glauber_prodWeight_audit_sharp` now exhibits *three* proofs of
the same proposition: approximate tensorization, the old Improved Random Walk
Theorem, and the sharp one. -/

section Calibration

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **The calibration point survives the sharpening: at `η = 1` the sharp constant
is exactly `1/n`.**

`η = 1` is the monograph's `0`-spectral independence.  Every level gap is `1`,
`sharpStep 1 = 1`, so every `Γ_i` is `1`, the sum is `n`, and the bound is the
optimal relaxation time `1/n` — the identical real expression that
`Chains.SpectralIndependenceMixing.spectralGapAtLeast_glauber_of_spectralIndependence_one`
and `Chains.ProductMeasure.approxTensorization_prodWeight` produce.

Note `1` sits strictly inside `0 < η < 2` and strictly inside `0 < η ≤ 3/2`, so
this point is in the overlap and both routes are non-vacuous there. -/
theorem spectralGapAtLeast_glauber_of_spectralIndependence_sharp_one
    (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ}
    (hm : Fintype.card V = m + 1)
    (hSI : ∀ (Λ : Finset V) (ζ : V → S) (hZΛ : 0 < Z (pinWeight w Λ ζ)),
      SpectralIndependence (gibbsPin w hw Λ ζ hZΛ) 1) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw) (1 / (Fintype.card V : ℝ)) := by
  have h := spectralGapAtLeast_glauber_of_spectralIndependence_sharp w hw hZ hm
    (by norm_num) hSI
  simp only [siGamma_one, sharpFactor_const_one, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at h
  rw [hm]
  exact h

/-- **Pairwise independence at every pinning gives the optimal `1/n` gap**, through
the sharp route.  The user-facing form of the calibration; `PairwiseIndep` implies
`SpectralIndependence … 1` by `spectralIndependence_of_pairwiseIndep`. -/
theorem spectralGapAtLeast_glauber_of_pairwiseIndep_sharp
    (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ}
    (hm : Fintype.card V = m + 1)
    (hPI : ∀ (Λ : Finset V) (ζ : V → S) (hZΛ : 0 < Z (pinWeight w Λ ζ)),
      PairwiseIndep (gibbsPin w hw Λ ζ hZΛ)) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw) (1 / (Fintype.card V : ℝ)) :=
  spectralGapAtLeast_glauber_of_spectralIndependence_sharp_one w hw hZ hm
    fun Λ ζ hZΛ => spectralIndependence_of_pairwiseIndep (hPI Λ ζ hZΛ)

variable {φ : V → S → ℝ}

/-- **The Glauber dynamics of a product measure has spectral gap at least `1/n` —
through spectral independence and the *sharp* Improved Random Walk Theorem.**

`Chains.ProductSpectralIndependence.pairwiseIndep_gibbsPin_prodWeight` discharges
the hypothesis, so this is unconditional.  The route differs from
`Chains.ProductSpectralIndependence.spectralGapAtLeast_glauber_prodWeight_via_spectralIndependence`
only in the level factor used inside the induction — `γ/(2 - γ)` here, `2γ - 1`
there — and the two constants coincide because `sharpStep 1 = 1`. -/
theorem spectralGapAtLeast_glauber_prodWeight_via_spectralIndependence_sharp
    (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s) :
    SpectralGapAtLeast (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
      (glauber (prodWeight φ) (prodWeight_nonneg hφ)) (1 / (Fintype.card V : ℝ)) := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 1 :=
    ⟨Fintype.card V - 1, by have := Fintype.card_pos (α := V); omega⟩
  exact spectralGapAtLeast_glauber_of_pairwiseIndep_sharp (prodWeight φ)
    (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) hm
    fun Λ ζ hZΛ => pairwiseIndep_gibbsPin_prodWeight hφ Λ ζ hZΛ

/-- **The audit, now threefold.**

The same proposition — `γ(P_Glauber) ≥ 1/(Fintype.card V)` for the Gibbs measure of
a product weight — proved three ways: by approximate tensorization of variance
(`Chains.ProductMeasure`), by spectral independence through the monograph's
`2γ - 1` Improved Random Walk Theorem
(`Chains.ProductSpectralIndependence`), and by spectral independence through the
sharp `γ/(2 - γ)` one (this file).

That all three terms typecheck against the *same* statement is the content: the
sharpening changes the constant nowhere at `η = 1`, which is what
`sharpStep_one` predicts and what a bug in either Improved Random Walk Theorem
would have broken. -/
theorem spectralGapAtLeast_glauber_prodWeight_audit_sharp
    (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s) :
    SpectralGapAtLeast (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
        (glauber (prodWeight φ) (prodWeight_nonneg hφ)) (1 / (Fintype.card V : ℝ))
      ∧ SpectralGapAtLeast (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
        (glauber (prodWeight φ) (prodWeight_nonneg hφ)) (1 / (Fintype.card V : ℝ))
      ∧ SpectralGapAtLeast (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
        (glauber (prodWeight φ) (prodWeight_nonneg hφ)) (1 / (Fintype.card V : ℝ)) :=
  ⟨spectralGapAtLeast_glauber_prodWeight hφ hc,
    spectralGapAtLeast_glauber_prodWeight_via_spectralIndependence hφ hc,
    spectralGapAtLeast_glauber_prodWeight_via_spectralIndependence_sharp hφ hc⟩

end Calibration

end Arlib.MarkovChains
