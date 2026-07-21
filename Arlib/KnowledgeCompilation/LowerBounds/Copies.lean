/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Step 1 of the lifting: making copies of variables

The first half of the copy-and-permute construction (paper §4.4.1,
`source/kc/arXiv.tex:377`).  Every variable `xᵢ` of the original formula is
replaced by a disjunction `⋁_{j ∈ [m]} y_{i,j}` of `m` fresh copies, the result
is expanded by distributivity into a DNF, and then — a step Knop does not need,
but this paper does — each term is *re-disambiguated* by adding `¬y_{i,j'}` for
every copy `j'` other than the one it selected.

Copies are indexed by `ι × Fin m`: the copy `y_{i,j}` is the variable `(i, j)`.

## The shape of a derived term

The paper computes (line 413) that every term of `ψ^∨` derived from a term with
positive part `I_p` and negative part `I_n` has the form

  `⋀_{i ∈ I_p} y_{i,jᵢ} ∧ ⋀_{i ∈ I_p, j ≠ jᵢ} ¬y_{i,j} ∧ ⋀_{i ∈ I_n} ⋀_j ¬y_{i,j}`

so such a term is determined by the original term together with a *choice
function* `c : ι → Fin m` picking, for each positive variable, which copy is
switched on.  `copyTerm` below is exactly this, and the two `biUnion`s are the
positive and negative parts of the display.

## The trap: this is not a semantics-preserving construction

It is very natural to expect `ψ^∨ ≡ ψ[xᵢ := ⋁ⱼ y_{i,j}]`, and **that is false**.
The intermediate DNF `φ`, before re-disambiguation, does satisfy it; adding the
`¬y_{i,j'}` conjuncts at line 385 strictly shrinks the satisfying set.  An
assignment switching on *two* copies of some `xᵢ` satisfies `φ` — it satisfies
whichever term chose either copy — but satisfies no term of `ψ^∨` at all, since
every one of them forces the other copies off.

The paper never claims the equivalence: its lemma at line 391 asserts only
unambiguity, the width, and the term count.  But a formalization that stated the
equivalence unconditionally would be wrong.

What is true, and what the lifting actually consumes, is the pair below:

* `sat_of_sat_copyTerm` — **soundness**, unconditional.  If `α` satisfies a
  derived term, then the collapsed assignment satisfies the original.
* `exists_copyTerm_sat` — **completeness**, conditional on `α` being *one-hot*:
  at most one copy of each variable is on.

And this is precisely why the protocol in the proof of `thm: fixed_to_best`
(lines 452–457) sets *every other variable of `V` to zero*.  That clause is not
padding; it is what places the simulated input in the region where `ψ^∨` and `ψ`
agree, and without it the reduction would not be sound.
-/
import Arlib.KnowledgeCompilation.Circuits.DNF

namespace Arlib.KnowledgeCompilation
namespace Copies

variable {ι : Type*} [DecidableEq ι] {m : ℕ}

/-! ## Collapsing an assignment on copies -/

/-- The original variable `xᵢ` is read off from an assignment to the copies as
the disjunction `⋁ⱼ y_{i,j}` — the paper's `β(xᵢ) = 1 ⟺ α(⋁ⱼ y_{i,j}) = 1`
(line 398). -/
def collapse (α : ι × Fin m → Bool) : ι → Bool :=
  fun i => decide (∃ j : Fin m, α (i, j) = true)

lemma collapse_eq_true {α : ι × Fin m → Bool} {i : ι} :
    collapse α i = true ↔ ∃ j, α (i, j) = true := by simp [collapse]

lemma collapse_eq_false {α : ι × Fin m → Bool} {i : ι} :
    collapse α i = false ↔ ∀ j, α (i, j) = false := by
  simp [collapse]

/-- An assignment to the copies is *one-hot* if it switches on at most one copy
of each original variable.

This is the region on which the construction is faithful; see the module
docstring, and the protocol at `source/kc/arXiv.tex:452`. -/
def OneHot (α : ι × Fin m → Bool) : Prop :=
  ∀ i : ι, ∀ j j' : Fin m, α (i, j) = true → α (i, j') = true → j = j'

/-! ## The derived terms -/

/-- The variables occurring positively in a term. -/
def posPart (t : Finset (Lit ι)) : Finset ι :=
  (t.filter (fun p => p.2 = true)).image Prod.fst

/-- The variables occurring negatively in a term. -/
def negPart (t : Finset (Lit ι)) : Finset ι :=
  (t.filter (fun p => p.2 = false)).image Prod.fst

lemma mem_posPart {t : Finset (Lit ι)} {i : ι} : i ∈ posPart t ↔ (i, true) ∈ t := by
  simp only [posPart, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hp, hb⟩, rfl⟩
    simp only at hb; subst hb; exact hp
  · intro h; exact ⟨(i, true), ⟨h, rfl⟩, rfl⟩

lemma mem_negPart {t : Finset (Lit ι)} {i : ι} : i ∈ negPart t ↔ (i, false) ∈ t := by
  simp only [negPart, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hp, hb⟩, rfl⟩
    simp only at hb; subst hb; exact hp
  · intro h; exact ⟨(i, false), ⟨h, rfl⟩, rfl⟩

/-- **The term derived from `t` by the choice function `c`** (paper line 413).

For each positively-occurring `i`, the copy `c i` is required on and every other
copy off; for each negatively-occurring `i`, all copies are required off.

Note that the positive block is emitted for *every* `j`, with required value
`decide (j = c i)` — that single expression is the paper's
`y_{i,jᵢ} ∧ ⋀_{j ≠ jᵢ} ¬y_{i,j}`. -/
def copyTerm (t : Finset (Lit ι)) (c : ι → Fin m) : Finset (Lit (ι × Fin m)) :=
  (posPart t).biUnion
      (fun i => (Finset.univ : Finset (Fin m)).image (fun j => ((i, j), decide (j = c i))))
    ∪ (negPart t).biUnion
      (fun i => (Finset.univ : Finset (Fin m)).image (fun j => ((i, j), false)))

lemma mem_copyTerm {t : Finset (Lit ι)} {c : ι → Fin m} {i : ι} {j : Fin m} {b : Bool} :
    (((i, j), b) : Lit (ι × Fin m)) ∈ copyTerm t c ↔
      (i ∈ posPart t ∧ b = decide (j = c i)) ∨ (i ∈ negPart t ∧ b = false) := by
  simp only [copyTerm, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro (⟨i', hi', j', ⟨⟨rfl, rfl⟩, rfl⟩⟩ | ⟨i', hi', j', ⟨⟨rfl, rfl⟩, rfl⟩⟩)
    · exact Or.inl ⟨hi', rfl⟩
    · exact Or.inr ⟨hi', rfl⟩
  · rintro (⟨hi, rfl⟩ | ⟨hi, rfl⟩)
    · exact Or.inl ⟨i, hi, j, ⟨rfl, rfl⟩, rfl⟩
    · exact Or.inr ⟨i, hi, j, ⟨rfl, rfl⟩, rfl⟩

/-! ## Soundness: unconditional -/

/-- **Soundness of the construction.**  If `α` satisfies a term derived from `t`,
then the collapsed assignment satisfies `t`.

This direction needs no hypothesis on `α`; it is the converse that does. -/
theorem sat_of_sat_copyTerm {t : Finset (Lit ι)} {c : ι → Fin m}
    {α : ι × Fin m → Bool} (h : Term.Sat (copyTerm t c) α) :
    Term.Sat t (collapse α) := by
  rintro ⟨i, b⟩ hp
  cases b with
  | true =>
    -- the copy `c i` is switched on, so the disjunction of copies is on
    have hi : i ∈ posPart t := mem_posPart.mpr hp
    have : α (i, c i) = true := by
      have := h ((i, c i), decide (c i = c i)) (mem_copyTerm.mpr (Or.inl ⟨hi, rfl⟩))
      simpa using this
    simp only [collapse_eq_true]
    exact ⟨c i, this⟩
  | false =>
    -- every copy is switched off, so the disjunction of copies is off
    have hi : i ∈ negPart t := mem_negPart.mpr hp
    have hall : ∀ j : Fin m, α (i, j) = false := by
      intro j
      have := h ((i, j), false) (mem_copyTerm.mpr (Or.inr ⟨hi, rfl⟩))
      simpa using this
    simpa [collapse_eq_false] using hall

/-! ## Completeness: only for one-hot assignments -/

/-- **Completeness, on the one-hot region.**  If `α` is one-hot and the collapsed
assignment satisfies `t`, then `α` satisfies the term derived from `t` by the
choice function that selects, for each variable, the copy that `α` switches on.

The one-hot hypothesis is not removable: an `α` switching on two copies of some
positively-occurring `xᵢ` collapses to a satisfying assignment of `t`, yet
satisfies no derived term whatsoever, because each of them switches the other
copies off.  See the module docstring. -/
theorem exists_copyTerm_sat [NeZero m] {t : Finset (Lit ι)} {α : ι × Fin m → Bool}
    (hone : OneHot α) (h : Term.Sat t (collapse α)) :
    ∃ c : ι → Fin m, Term.Sat (copyTerm t c) α := by
  classical
  -- pick, for each variable, a copy that `α` switches on, when there is one
  have hchoice : ∀ i : ι, ∃ j : Fin m, (collapse α i = true → α (i, j) = true) := by
    intro i
    by_cases hi : collapse α i = true
    · obtain ⟨j, hj⟩ := collapse_eq_true.mp hi
      exact ⟨j, fun _ => hj⟩
    · exact ⟨Classical.arbitrary _, fun hc => absurd hc hi⟩
  choose c hc using hchoice
  refine ⟨c, ?_⟩
  rintro ⟨⟨i, j⟩, b⟩ hp
  rcases mem_copyTerm.mp hp with ⟨hi, rfl⟩ | ⟨hi, rfl⟩
  · -- `i` occurs positively: `α` switches on exactly the copy `c i`
    have hci : collapse α i = true := h (i, true) (mem_posPart.mp hi)
    have hon : α (i, c i) = true := hc i hci
    by_cases hj : j = c i
    · subst hj; simpa using hon
    · -- any other copy must be off, by one-hotness
      rw [decide_eq_false hj]
      cases hval : α (i, j) with
      | false => rfl
      | true => exact absurd (hone i j (c i) hval hon) hj
  · -- `i` occurs negatively: every copy is off
    have hci : collapse α i = false := h (i, false) (mem_negPart.mp hi)
    simpa using collapse_eq_false.mp hci j

/-! ## Towards unambiguity -/

/-- **A satisfied derived term determines its choice function.**

If `α` satisfies the terms derived from `t` by two choice functions, those
functions agree wherever it matters — on the positive part of `t`, which is the
only place `copyTerm` reads them.

This is the crux of the paper's unambiguity argument (line 415, "it is therefore
easy to see that `C = C'`"): a term of `ψ^∨` derived from `t` is *determined* by
its choice function, so two satisfied ones must coincide.  Note that no one-hot
hypothesis is needed — the derived term supplies its own, since it explicitly
switches every unselected copy off. -/
theorem choice_eq_on_posPart {t : Finset (Lit ι)} {c c' : ι → Fin m}
    {α : ι × Fin m → Bool} (h : Term.Sat (copyTerm t c) α)
    (h' : Term.Sat (copyTerm t c') α) {i : ι} (hi : i ∈ posPart t) :
    c i = c' i := by
  -- `α` switches on the copy `c i`, since that is what the first term demands
  have hon : α (i, c i) = true := by
    have := h ((i, c i), decide (c i = c i)) (mem_copyTerm.mpr (Or.inl ⟨hi, rfl⟩))
    simpa using this
  -- but the second term demands that copy be on only if `c'` also selects it
  have := h' ((i, c i), decide (c i = c' i)) (mem_copyTerm.mpr (Or.inl ⟨hi, rfl⟩))
  rw [hon] at this
  exact of_decide_eq_true this.symm

/-- Two choice functions agreeing on the positive part of `t` derive the *same*
term, so `choice_eq_on_posPart` really does identify derived terms. -/
theorem copyTerm_congr {t : Finset (Lit ι)} {c c' : ι → Fin m}
    (h : ∀ i ∈ posPart t, c i = c' i) : copyTerm t c = copyTerm t c' := by
  ext ⟨⟨i, j⟩, b⟩
  rw [mem_copyTerm, mem_copyTerm]
  constructor
  · rintro (⟨hi, rfl⟩ | ⟨hi, rfl⟩)
    · exact Or.inl ⟨hi, by rw [h i hi]⟩
    · exact Or.inr ⟨hi, rfl⟩
  · rintro (⟨hi, rfl⟩ | ⟨hi, rfl⟩)
    · exact Or.inl ⟨hi, by rw [h i hi]⟩
    · exact Or.inr ⟨hi, rfl⟩

/-- **Derived terms are unambiguous among themselves.**  Two choice functions
whose derived terms are both satisfied by `α` derive the same term — the paper's
`C = C'`. -/
theorem copyTerm_eq_of_sat {t : Finset (Lit ι)} {c c' : ι → Fin m}
    {α : ι × Fin m → Bool} (h : Term.Sat (copyTerm t c) α)
    (h' : Term.Sat (copyTerm t c') α) : copyTerm t c = copyTerm t c' :=
  copyTerm_congr (fun _ hi => choice_eq_on_posPart h h' hi)

/-- The two directions together, on the one-hot region: the derived terms
capture exactly the original term. -/
theorem sat_copyTerm_iff [NeZero m] {t : Finset (Lit ι)} {α : ι × Fin m → Bool}
    (hone : OneHot α) :
    (∃ c : ι → Fin m, Term.Sat (copyTerm t c) α) ↔ Term.Sat t (collapse α) :=
  ⟨fun ⟨_, hc⟩ => sat_of_sat_copyTerm hc, exists_copyTerm_sat hone⟩

end Copies
end Arlib.KnowledgeCompilation
