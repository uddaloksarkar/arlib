/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Spin systems as weighted complexes

`Techniques.Levels` builds the up and down walks on the levels of a weighted
complex over an abstract ground set; `Chains.Glauber` builds the Glauber
dynamics on configurations of a spin system.  The monograph observes (§5.1,
Remark at line ~1740) that these are **the same object**: a spin system is the
weighted complex whose ground set is the set of `(vertex, spin)` pairs and whose
top-level faces are the graphs of configurations, and under that identification
the down-up walk at the top level *is* the Glauber dynamics.

This module supplies the identification.

* `graph σ` — the configuration `σ` as a face `{(v, σ v) : v ∈ V}` of the ground
  set `V × S`, with `graph_injective` and `graph_card`.
* `graphWeight w` — the induced top-level weight, and the three hypotheses
  `Techniques.Levels` requires: nonnegativity, support on faces of cardinality
  `|V|`, and total mass `1`.
* `mu_graphWeight` — **the dictionary**: the derived weight of a face `τ` is the
  total weight of the configurations extending it,
  `mu (graphWeight w) τ = ∑ σ, if τ ⊆ graph σ then w σ else 0`.
* `subset_erase_graph_iff` — a face one level below `graph σ` is exactly a
  configuration constraint "agree with `σ` off `v`", and hence
  **`mu_graphWeight_erase : mu (graphWeight w) ((graph σ).erase (v, σ v)) = Zloc w σ v`**:
  the derived weight one level down is the local partition function.  This is
  the heart of the identification — the abstract `mu` and the spin-system `Zloc`
  are the same number.
* `sum_ite_erase` — the reindexing lemma dual to `Levels.sum_ite_insert`: a sum
  over the subfaces of cardinality `k` of a face of cardinality `k + 1` is a sum
  over the elements deleted.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.Levels
import Arlib.MarkovChains.Chains.Glauber
import Mathlib.Data.Fintype.Prod

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The reindexing lemma for the down operator

`Techniques.Levels` states the down operator with the subface condition
`τ'.card = k ∧ τ' ⊆ τ`, which is what makes its row sum easy.  To *compute* with
it one wants the other description — the subfaces of a face of cardinality
`k + 1` are exactly the results of deleting one element — and this lemma
converts between them. -/

section SumIteErase

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Subfaces one level down are deletions.**  For `T` of cardinality `k + 1`,
summing a function over the subfaces of `T` of cardinality `k` is summing over
the elements of `T` that get deleted.

Dual to `Levels.sum_ite_insert`, and stated in the same `ite`-over-`univ` form so
that it can be rewritten directly into a kernel definition without ever naming a
filtered index set. -/
theorem sum_ite_erase {T : Finset α} {k : ℕ} (hT : T.card = k + 1) (g : Finset α → ℝ) :
    ∑ R : Finset α, (if R.card = k ∧ R ⊆ T then g R else 0) = ∑ p ∈ T, g (T.erase p) := by
  -- The subfaces of cardinality `k` are exactly the image of `T` under `erase`.
  have himg : T.image (fun p => T.erase p) = univ.filter (fun R => R.card = k ∧ R ⊆ T) := by
    ext R
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨by rw [Finset.card_erase_of_mem hp, hT]; rfl, Finset.erase_subset _ _⟩
    · rintro ⟨hcard, hsub⟩
      -- `T \ R` is a single element; deleting it from `T` gives `R`.
      have hne : R ≠ T := by
        intro hc; rw [hc, hT] at hcard; omega
      obtain ⟨p, hpT, hpR⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hsub hne)
      refine ⟨p, hpT, ?_⟩
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · exact Finset.subset_erase.mpr ⟨hsub, hpR⟩
      · rw [Finset.card_erase_of_mem hpT, hT, hcard]
        omega
  have hinj : ∀ p ∈ T, ∀ q ∈ T, T.erase p = T.erase q → p = q := by
    intro p hp q hq hpq
    by_contra hne
    have hq' : q ∈ T.erase p := Finset.mem_erase.mpr ⟨fun h => hne h.symm, hq⟩
    rw [hpq] at hq'
    exact (Finset.mem_erase.mp hq').1 rfl
  rw [← Finset.sum_filter, ← himg, Finset.sum_image hinj]

end SumIteErase

/-! ## Configurations as faces -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [DecidableEq S]

/-- The **graph of a configuration**: `σ` viewed as the face
`{(v, σ v) : v ∈ V}` of the ground set `V × S`. -/
def graph (σ : V → S) : Finset (V × S) := univ.image (fun v => (v, σ v))

@[simp] theorem mem_graph_iff (σ : V → S) (v : V) (s : S) :
    (v, s) ∈ graph σ ↔ σ v = s := by
  simp only [graph, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu⟩
    have h1 : u = v := congrArg Prod.fst hu
    subst h1
    exact congrArg Prod.snd hu
  · rintro rfl
    exact ⟨v, rfl⟩

theorem mem_graph_of_apply (σ : V → S) (v : V) : (v, σ v) ∈ graph σ :=
  (mem_graph_iff σ v (σ v)).mpr rfl

theorem fst_eq_of_mem_graph {σ : V → S} {p : V × S} (h : p ∈ graph σ) : σ p.1 = p.2 := by
  obtain ⟨v, s⟩ := p
  exact (mem_graph_iff σ v s).mp h

/-- Distinct configurations have distinct graphs. -/
theorem graph_injective : Function.Injective (graph : (V → S) → Finset (V × S)) := by
  intro σ τ h
  funext v
  have : (v, σ v) ∈ graph τ := h ▸ mem_graph_of_apply σ v
  exact ((mem_graph_iff τ v (σ v)).mp this).symm

/-- Every graph is a face of cardinality `|V|`, so graphs sit at the top level. -/
@[simp] theorem graph_card (σ : V → S) : (graph σ).card = Fintype.card V := by
  rw [graph, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h),
    Finset.card_univ]

/-- Summing over the elements of `graph σ` is summing over vertices. -/
theorem sum_graph {M : Type*} [AddCommMonoid M] (σ : V → S) (g : V × S → M) :
    ∑ p ∈ graph σ, g p = ∑ v, g (v, σ v) := by
  rw [graph, Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h)]

end Graph

/-! ## The induced weighted complex -/

section GraphWeight

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The top-level weight on `Finset (V × S)` induced by a weight on
configurations: mass `w σ` on the face `graph σ`, and `0` on faces that are not
graphs. -/
def graphWeight (w : (V → S) → ℝ) : Finset (V × S) → ℝ :=
  fun T => ∑ σ, if graph σ = T then w σ else 0

theorem graphWeight_apply (w : (V → S) → ℝ) (T : Finset (V × S)) :
    graphWeight w T = ∑ σ, if graph σ = T then w σ else 0 := rfl

/-- On a graph the induced weight is the original weight. -/
@[simp] theorem graphWeight_graph (w : (V → S) → ℝ) (σ : V → S) :
    graphWeight w (graph σ) = w σ := by
  rw [graphWeight_apply]
  rw [Finset.sum_eq_single σ]
  · rw [if_pos rfl]
  · intro τ _ hτ
    exact if_neg fun hc => hτ (graph_injective hc)
  · intro h
    exact absurd (Finset.mem_univ σ) h

theorem graphWeight_nonneg {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (T : Finset (V × S)) :
    0 ≤ graphWeight w T := by
  refine Finset.sum_nonneg fun σ _ => ?_
  split
  · exact hw σ
  · exact le_rfl

/-- The induced weight is supported on faces of cardinality `|V|`, as
`Techniques.Levels` requires of a top-level weight. -/
theorem graphWeight_supp (w : (V → S) → ℝ) {T : Finset (V × S)}
    (hT : T.card ≠ Fintype.card V) : graphWeight w T = 0 := by
  rw [graphWeight_apply]
  refine Finset.sum_eq_zero fun σ _ => if_neg fun hc => hT ?_
  rw [← hc, graph_card]

/-- The induced weight has the same total mass. -/
theorem graphWeight_sum (w : (V → S) → ℝ) :
    ∑ T : Finset (V × S), graphWeight w T = ∑ σ, w σ := by
  simp only [graphWeight_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp

/-- **The dictionary.**  The derived weight of a face is the total weight of the
configurations extending it. -/
theorem mu_graphWeight (w : (V → S) → ℝ) (τ : Finset (V × S)) :
    mu (graphWeight w) τ = ∑ σ, if τ ⊆ graph σ then w σ else 0 := by
  rw [mu_apply]
  have step : ∀ T : Finset (V × S), (if τ ⊆ T then graphWeight w T else 0)
      = ∑ σ, (if τ ⊆ T then (if graph σ = T then w σ else 0) else 0) := by
    intro T
    by_cases h : τ ⊆ T
    · simp only [if_pos h, graphWeight_apply]
    · simp only [if_neg h, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun T _ => step T, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single (graph σ)]
  · by_cases h : τ ⊆ graph σ <;> simp [h]
  · intro T _ hT
    have hz : (if graph σ = T then w σ else 0) = 0 := if_neg fun hc => hT hc.symm
    by_cases h : τ ⊆ T <;> simp [h, hz]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- At the top level the derived weight is the original weight. -/
theorem mu_graphWeight_graph (w : (V → S) → ℝ) (σ : V → S) :
    mu (graphWeight w) (graph σ) = w σ :=
  (mu_top (n := Fintype.card V) (fun _ hT => graphWeight_supp w hT) (graph_card σ)).trans
    (graphWeight_graph w σ)

end GraphWeight

/-! ## One level down: the local partition function

The face `graph σ` with the pair at `v` deleted is the constraint "agree with
`σ` off `v`".  Its derived weight is therefore the local partition function
`Zloc w σ v`, which is precisely the denominator of the single-site heat-bath
update. -/

section Erase

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [DecidableEq S]

/-- **A face one level below `graph σ` is a configuration constraint.**
`(graph σ).erase (v, σ v) ⊆ graph τ` says exactly that `τ` agrees with `σ` off
`v`. -/
theorem subset_erase_graph_iff (v : V) (σ τ : V → S) :
    (graph σ).erase (v, σ v) ⊆ graph τ ↔ AgreeOff v σ τ := by
  constructor
  · intro h u hu
    have hmem : (u, σ u) ∈ (graph σ).erase (v, σ v) := by
      exact Finset.mem_erase.mpr ⟨fun hc => hu (congrArg Prod.fst hc), mem_graph_of_apply σ u⟩
    exact ((mem_graph_iff τ u (σ u)).mp (h hmem)).symm
  · intro h p hp
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
    obtain ⟨u, s⟩ := p
    have hs : σ u = s := (mem_graph_iff σ u s).mp hmem
    have hu : u ≠ v := by
      rintro rfl
      exact hne (by rw [hs])
    exact (mem_graph_iff τ u s).mpr ((h u hu).symm.trans hs)

end Erase

section EraseMu

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The derived weight one level down is the local partition function.**

`mu (graphWeight w) ((graph σ).erase (v, σ v)) = Zloc w σ v`.  This is the
identification on which everything else rests: the abstract level machinery's
`mu` and the spin system's `Zloc` compute the same number. -/
theorem mu_graphWeight_erase (w : (V → S) → ℝ) (v : V) (σ : V → S) :
    mu (graphWeight w) ((graph σ).erase (v, σ v)) = Zloc w σ v := by
  rw [mu_graphWeight]
  have step : ∀ τ : V → S,
      (if (graph σ).erase (v, σ v) ⊆ graph τ then w τ else 0)
        = (if AgreeOff v σ τ then w τ else 0) := by
    intro τ
    by_cases h : AgreeOff v σ τ
    · rw [if_pos ((subset_erase_graph_iff v σ τ).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((subset_erase_graph_iff v σ τ).mp hc)), if_neg h]
  rw [Finset.sum_congr rfl fun τ _ => step τ, sum_ite_agreeOff v σ w, Zloc_apply]

end EraseMu

/-! ## The down-up walk at the top level is the Glauber dynamics

This is the monograph's Remark at line ~1740, made precise.  The two chains
agree on every row of positive weight — that is, `μ`-almost everywhere.  They
must differ on rows of weight zero, where neither the conditional distribution
nor the up operator is determined and each makes its own arbitrary choice; those
rows are invisible to the Gibbs measure. -/

section DownUpGlauber

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The support hypothesis `Techniques.Levels` requires, with the dimension
written as `m + 1` so that the top level is `m + 1` and the level below is `m`. -/
theorem graphWeight_supp' (w : (V → S) → ℝ) {m : ℕ} (hm : Fintype.card V = m + 1)
    (T : Finset (V × S)) (hT : T.card ≠ m + 1) : graphWeight w T = 0 :=
  graphWeight_supp w (by rw [hm]; exact hT)

/-- **The Glauber dynamics as a down-up walk**: the down-up walk at the top level
of the complex induced by a spin system. -/
noncomputable def spinDownUp (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) {m : ℕ}
    (hm : Fintype.card V = m + 1) : FinChain (Finset (V × S)) :=
  downUp (graphWeight w) (m + 1) m (graphWeight_nonneg hw) (graphWeight_supp' w hm)
    (Nat.lt_succ_self m)

/-- The up step out of a face one level below `graph σ` is the single-site
heat-bath update.  This is where the dictionary is cashed in: `mu` one level down
is `Zloc`, the subface condition is `AgreeOff`, and `(m+1) - m = 1` kills the
normalising factor. -/
theorem up_erase_graph (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) {m : ℕ}
    (hm : Fintype.card V = m + 1) {σ : V → S} (hσ : 0 < w σ) (v : V) (τ : V → S) :
    up (graphWeight w) (m + 1) m (graphWeight_nonneg hw) (graphWeight_supp' w hm)
        (Nat.lt_succ_self m) ((graph σ).erase (v, σ v)) (graph τ)
      = siteUpdate w v σ τ := by
  have hZ : 0 < Zloc w σ v := Zloc_pos_of_w_pos hw v hσ
  have hmu : mu (graphWeight w) ((graph σ).erase (v, σ v)) = Zloc w σ v :=
    mu_graphWeight_erase w v σ
  have hcard : ((graph σ).erase (v, σ v)).card = m := by
    rw [Finset.card_erase_of_mem (mem_graph_of_apply σ v), graph_card, hm]
    omega
  have hτcard : (graph τ).card = m + 1 := by rw [graph_card, hm]
  rw [up_apply, if_pos ⟨hcard, by rw [hmu]; exact hZ⟩, hmu,
    siteUpdate_of_Zloc_ne_zero hZ.ne']
  have hsub : ((graph σ).erase (v, σ v) ⊆ graph τ) ↔ AgreeOff v σ τ :=
    subset_erase_graph_iff v σ τ
  have hone : (((m + 1 - m : ℕ) : ℝ)) = 1 := by
    norm_num
  by_cases h : AgreeOff v σ τ
  · rw [if_pos ⟨hτcard, hsub.mpr h⟩, if_pos h, mu_graphWeight_graph, hone, one_mul]
  · rw [if_neg (fun hc => h (hsub.mp hc.2)), if_neg h]

/-- **The down-up walk at the top level is the Glauber dynamics.**

On every configuration of positive weight, the two chains have the same row.
The proof is the dictionary applied twice: `down` from `graph σ` deletes one
pair `(v, σ v)` uniformly, which is choosing a uniform vertex `v`; and `up` from
the resulting face is the single-site heat-bath update at `v`
(`up_erase_graph`). -/
theorem spinDownUp_apply_graph [Nonempty V] (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) {m : ℕ}
    (hm : Fintype.card V = m + 1) {σ : V → S} (hσ : 0 < w σ) (τ : V → S) :
    spinDownUp w hw hm (graph σ) (graph τ) = glauber w hw σ τ := by
  have hgc : (graph σ).card = m + 1 := by rw [graph_card, hm]
  rw [spinDownUp, downUp, FinKernel.comp_apply]
  have step : ∀ R : Finset (V × S),
      down m (graph σ) R
          * up (graphWeight w) (m + 1) m (graphWeight_nonneg hw) (graphWeight_supp' w hm)
              (Nat.lt_succ_self m) R (graph τ)
        = if R.card = m ∧ R ⊆ graph σ then
            (1 / ((m : ℝ) + 1))
              * up (graphWeight w) (m + 1) m (graphWeight_nonneg hw) (graphWeight_supp' w hm)
                  (Nat.lt_succ_self m) R (graph τ)
          else 0 := by
    intro R
    rw [down_apply, if_pos hgc]
    split
    · rfl
    · rw [zero_mul]
  rw [Finset.sum_congr rfl fun R _ => step R, sum_ite_erase hgc, sum_graph]
  have step2 : ∀ v : V,
      (1 / ((m : ℝ) + 1))
          * up (graphWeight w) (m + 1) m (graphWeight_nonneg hw) (graphWeight_supp' w hm)
              (Nat.lt_succ_self m) ((graph σ).erase (v, σ v)) (graph τ)
        = (1 / ((m : ℝ) + 1)) * siteUpdate w v σ τ := by
    intro v
    rw [up_erase_graph w hw hm hσ v τ]
  rw [Finset.sum_congr rfl fun v _ => step2 v, ← Finset.mul_sum, glauber_apply]
  have hcast : ((Fintype.card V : ℕ) : ℝ) = (m : ℝ) + 1 := by
    rw [hm]; push_cast; ring
  rw [hcast]
  rfl

end DownUpGlauber

end Arlib.MarkovChains
