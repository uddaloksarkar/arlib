/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Automata.SuccinctNFAMembership

/-!
# Witnesses for `SuccinctNFA.Encoding` and `Definition def:prop`

`SuccinctNFA.Encoding` and `SuccinctNFA.LabelProps` are hypothesis bundles: they
occur to the *left* of the turnstile in `Encoding.memberTest`, in the source's
`thm:progmain`, and in everything the `CQCount` development builds on top of
them.  A hypothesis bundle that nothing satisfies makes every theorem about it
true and worthless, and the failure is invisible — no proof breaks, no `sorry`
appears.  This file removes that possibility by exhibiting instances.

## The instance

`witnessNFA` is the two-state automaton `0 --A--> 1` over `Γ = Fin 3` with
`L = Bool`:

* `decode true = {0, 1}` — the used label, decoding to **two** symbols;
* `decode false = ∅` — an *unused* label, present in `L` but on no transition.

`witnessOracle` answers for it, and `labelProps_witness` proves
`LabelProps witnessNFA witnessOracle (1/2) 1 2`.  `witnessEncoding` is the
matching `Encoding`, of size `4`, and `witness_memberTest` instantiates
`Encoding.memberTest` — the source's `prop:membertest` — at the pair, so that
proposition too is known to have a model.

## What the witness exercises, clause by clause

The point of a witness is defeated if every clause holds for a degenerate
reason, so each is accounted for here.

**Genuinely exercised, and tight — the parameters `(ε₀, g, T) = (1/2, 1, 2)`
cannot be improved in any coordinate:**

* `sampler_uniform`.  `decode true` has **two distinct** elements, `0` and `1`,
  and the sampler is deliberately **non-uniform**: it returns `0` with
  probability `1/4` and `1` with probability `3/4`, against a target of
  `1/|A| = 1/2`.  Both endpoints of the window `[(1−ε₀)/2, (1+ε₀)/2] = [1/4, 3/4]`
  are attained (`witness_sampler_uniform_tight`), so the clause is an equality
  constraint at both ends rather than a `p = p`.  `labelProps_witness_le_eps`
  turns this around: no `ε₀ < 1/2` works, whatever `g` and `T`.
* `sizeBound`.  `|decode true| = 2 = 2 ^ 1`, so the bound holds with equality;
  `labelProps_witness_le_g` shows `g = 0` fails.
* `memCost_le` and `sampler_cost`.  Membership costs exactly `2 = T`, and the
  sampler's two support points cost `1` and `2`; `labelProps_witness_le_T`
  shows `T = 1` fails.
* `memTest_correct`.  `memTest true` is `a ≠ 2`, which is `true` on `0, 1` and
  `false` on `2`, so both directions of the `↔` have content: `decode true` is a
  **proper** subset of `Γ`, and a test that always said `true` would fail.
* `sampler_mem`.  `2 ∉ decode true`, and the sampler must and does avoid it.
  The guard `(decode true).Nonempty` is discharged, not exploited, so the clause
  is checked and not skipped: `witness_sampler_mem_unguarded` states the
  unguarded form separately.
* `UsedLabel` is not vacuous: `witnessNFA_usedLabel_true` holds, so every clause
  above is actually reached.  And it is not trivial either —
  `witnessNFA_not_usedLabel_false` shows `false` is *not* used, which is what
  lets `witnessOracle` answer nonsense there (`est false = 17`, a sampler
  returning `2` at cost `7`) without breaking anything.  That is the `UsedLabel`
  guard doing its job.

**Holds degenerately, and could not do otherwise:**

* `finite`.  `Γ = Fin 3` is a finite type, so every subset is finite.  No choice
  of witness over a finite alphabet can exercise this clause; it exists for
  alphabets that are not finite types.
* `est_relErr`.  `est true = 5/2` sits strictly inside `[1, 3]`, so the clause is
  satisfied with slack.  This is deliberate: making it tight would make `ε₀`
  overdetermined and hide which clause is really pinning `ε₀ = 1/2`.

## The empty-label case, and why `sampler_mem` is guarded

`deadNFA` is the same shape with a single label decoding to `∅` — a dead
transition, which nothing in the model forbids.  `labelProps_dead` proves
`LabelProps deadNFA deadOracle 0 0 0`, and
`not_unguarded_sampler_mem_dead` proves that **no** oracle whatsoever satisfies
the *unguarded* form of `sampler_mem` on it, because a `PMF` has nonempty
support.  The pair is the proof that the `(N.decode A).Nonempty` guard on
`LabelProps.sampler_mem` is load-bearing and not decoration: without it the
bundle is not merely awkward on `deadNFA`, it is empty, and every theorem taking
it as a hypothesis would say nothing there.
-/

namespace Arlib.Automata

open Arlib.Approximation

namespace SuccinctNFA

/-! ### The automaton

`0 --true--> 1` over `Γ = Fin 3`, with the label `true` decoding to `{0, 1}` and
the label `false` — which labels no transition — decoding to `∅`. -/

/-- The witness automaton: two states, one transition, carrying the label `true`
whose decoding `{0, 1}` has two elements.  The label `false` occurs on no
transition, so `def:prop` says nothing about it. -/
def witnessNFA : SuccinctNFA (Fin 2) (Fin 3) Bool where
  decode A := cond A {0, 1} ∅
  step s A s' := A = true ∧ s = 0 ∧ s' = 1
  init := 0
  final := 1

@[simp] theorem witnessNFA_decode_true : witnessNFA.decode true = {0, 1} := rfl

@[simp] theorem witnessNFA_decode_false : witnessNFA.decode false = (∅ : Set (Fin 3)) := rfl

@[simp] theorem witnessNFA_step_iff (s s' : Fin 2) (A : Bool) :
    witnessNFA.step s A s' ↔ (A = true ∧ s = 0 ∧ s' = 1) := Iff.rfl

theorem witnessNFA_usedLabel_iff (A : Bool) : witnessNFA.UsedLabel A ↔ A = true := by
  constructor
  · rintro ⟨s, s', h, -, -⟩; exact h
  · rintro rfl; exact ⟨0, 1, rfl, rfl, rfl⟩

/-- The label `true` **is** used, so no clause of `def:prop` is vacuous on it. -/
theorem witnessNFA_usedLabel_true : witnessNFA.UsedLabel true :=
  (witnessNFA_usedLabel_iff true).2 rfl

/-- The label `false` is **not** used, which is why the oracle may answer
nonsense there. -/
theorem witnessNFA_not_usedLabel_false : ¬ witnessNFA.UsedLabel false := by
  simp [witnessNFA_usedLabel_iff]

/-- `|A| = 2`: the used label decodes to **two distinct** symbols, which is what
makes `sampler_uniform` a constraint relating two different probabilities rather
than a tautology. -/
@[simp] theorem witnessNFA_ncard_decode_true : (witnessNFA.decode true).ncard = 2 := by
  rw [witnessNFA_decode_true]
  exact Set.ncard_pair (by decide)

/-- The witness automaton is unrolled, at the level function `1, 0`. -/
theorem witnessNFA_isUnrolled : witnessNFA.IsUnrolled (fun s => if s = 0 then 1 else 0) where
  step_lvl := by rintro s A s' ⟨-, rfl, rfl⟩; rfl

/-! ### The sampler

A deliberately **non-uniform** law on `decode true = {0, 1}`: `1/4` on `0` at
cost `1`, `3/4` on `1` at cost `2`.  Against the target `1/|A| = 1/2` these sit
exactly on the two endpoints of the `(1 ± 1/2)` window. -/

/-- The output law of the witness sampler: `1/4` on `0`, `3/4` on `1`, nothing
on `2`. -/
noncomputable def witnessBase : PMF (Fin 3) :=
  PMF.ofFintype ![1 / 4, 3 / 4, 0] (by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, add_zero]
    rw [ENNReal.div_add_div_same]
    norm_num
    exact ENNReal.div_self (by norm_num) (by norm_num))

theorem witnessBase_apply (a : Fin 3) : witnessBase a = ![1 / 4, 3 / 4, 0] a :=
  PMF.ofFintype_apply _ a

theorem witnessBase_support : witnessBase.support = {0, 1} := by
  rw [witnessBase, PMF.support_ofFintype]
  ext a
  fin_cases a <;> simp [Function.support]

/-- The witness sampler: the law `witnessBase`, paired with a cost of `1` on `0`
and `2` on `1`.  The cost `2` meets the bound `T = 2` exactly. -/
noncomputable def witnessSampler : PMF (Fin 3 × ℕ) :=
  witnessBase.map (fun a => (a, if a = 0 then 1 else 2))

theorem witnessSampler_support :
    witnessSampler.support = {((0 : Fin 3), 1), ((1 : Fin 3), 2)} := by
  rw [witnessSampler, PMF.support_map, witnessBase_support]
  ext p
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with rfl | rfl
    · exact Or.inl (by norm_num)
    · exact Or.inr (by norm_num)
  · rintro (rfl | rfl)
    · exact ⟨0, Or.inl rfl, by norm_num⟩
    · exact ⟨1, Or.inr rfl, by norm_num⟩

theorem witnessSampler_outProb (a : Fin 3) :
    outProb witnessSampler ({a} : Set (Fin 3)) = witnessBase a := by
  rw [outProb, witnessSampler, PMF.toOuterMeasure_map_apply]
  have h : ((fun b : Fin 3 => (b, if b = 0 then 1 else 2)) ⁻¹'
      {p : Fin 3 × ℕ | p.1 ∈ ({a} : Set (Fin 3))}) = {a} := by
    ext b; simp
  rw [h, PMF.toOuterMeasure_apply_singleton]

@[simp] theorem witnessSampler_outProbR_zero :
    outProbR witnessSampler ({0} : Set (Fin 3)) = 1 / 4 := by
  rw [outProbR, witnessSampler_outProb, witnessBase_apply]
  norm_num [ENNReal.toReal_div]

@[simp] theorem witnessSampler_outProbR_one :
    outProbR witnessSampler ({1} : Set (Fin 3)) = 3 / 4 := by
  rw [outProbR, witnessSampler_outProb, witnessBase_apply]
  norm_num [ENNReal.toReal_div]

/-- **The sampler is genuinely non-uniform.**  Were it uniform, `sampler_uniform`
would hold for the trivial reason that both sides equal `1/|A|`; it does not. -/
theorem witnessSampler_not_uniform :
    outProbR witnessSampler ({0} : Set (Fin 3)) ≠ outProbR witnessSampler ({1} : Set (Fin 3)) := by
  norm_num

/-! ### The oracle -/

/-- The oracle for `witnessNFA`.  On the used label `true` it is honest; on the
unused label `false` it is deliberately wrong in every clause — the estimate is
`17` for a set of size `0`, and the sampler returns the symbol `2 ∉ ∅` at a cost
of `7 > T` — to show that the `UsedLabel` guard is what confines `def:prop` to
the labels of `Δ`. -/
noncomputable def witnessOracle : LabelOracle (Fin 3) Bool where
  est A := cond A (5 / 2) 17
  memTest A a := A && decide (a ≠ 2)
  memCost _ _ := 2
  sampler A := cond A witnessSampler (PMF.pure (2, 7))

@[simp] theorem witnessOracle_est_true : witnessOracle.est true = 5 / 2 := rfl

@[simp] theorem witnessOracle_memTest_true (a : Fin 3) :
    witnessOracle.memTest true a = decide (a ≠ 2) := by
  simp [witnessOracle]

@[simp] theorem witnessOracle_sampler_true : witnessOracle.sampler true = witnessSampler := rfl

/-! ### `Definition def:prop` is satisfiable -/

/-- **`LabelProps` has a model.**  Every clause of `def:prop` holds for
`witnessNFA` and `witnessOracle` at `ε₀ = 1/2`, `g = 1`, `T = 2`.  See the module
docstring for which clauses this exercises and which hold degenerately. -/
theorem labelProps_witness : LabelProps witnessNFA witnessOracle (1 / 2) 1 2 where
  finite := fun _ _ => Set.toFinite _
  sizeBound := by
    rintro A hA
    rw [(witnessNFA_usedLabel_iff A).1 hA, witnessNFA_ncard_decode_true]
    norm_num
  memTest_correct := by
    rintro A hA a
    obtain rfl := (witnessNFA_usedLabel_iff A).1 hA
    rw [witnessOracle_memTest_true, witnessNFA_decode_true]
    simp only [decide_eq_true_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert a
    decide
  memCost_le := fun _ _ _ => le_refl _
  est_relErr := by
    rintro A hA
    obtain rfl := (witnessNFA_usedLabel_iff A).1 hA
    rw [witnessNFA_ncard_decode_true, witnessOracle_est_true]
    simp only [relErr, Set.mem_Icc]
    norm_num
  sampler_mem := by
    rintro A hA - p hp
    obtain rfl := (witnessNFA_usedLabel_iff A).1 hA
    rw [witnessOracle_sampler_true, witnessSampler_support] at hp
    rcases hp with rfl | rfl <;> simp
  sampler_cost := by
    rintro A hA p hp
    obtain rfl := (witnessNFA_usedLabel_iff A).1 hA
    rw [witnessOracle_sampler_true, witnessSampler_support] at hp
    rcases hp with rfl | rfl <;> norm_num
  sampler_uniform := by
    rintro A hA a ha
    obtain rfl := (witnessNFA_usedLabel_iff A).1 hA
    rw [witnessNFA_ncard_decode_true, witnessOracle_sampler_true]
    rw [witnessNFA_decode_true] at ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    simp only [relErr, Set.mem_Icc]
    rcases ha with rfl | rfl
    · rw [witnessSampler_outProbR_zero]; norm_num
    · rw [witnessSampler_outProbR_one]; norm_num

/-- `def:prop` is satisfiable. -/
theorem exists_labelProps :
    ∃ (S Γ L : Type) (N : SuccinctNFA S Γ L) (O : LabelOracle Γ L) (ε₀ : ℝ) (g T : ℕ),
      (∃ A : L, N.UsedLabel A ∧ 1 < (N.decode A).ncard) ∧ LabelProps N O ε₀ g T :=
  ⟨Fin 2, Fin 3, Bool, witnessNFA, witnessOracle, 1 / 2, 1, 2,
    ⟨true, witnessNFA_usedLabel_true, by rw [witnessNFA_ncard_decode_true]; norm_num⟩,
    labelProps_witness⟩

/-- The witness satisfies `sampler_mem` in its **unguarded** form as well, so it
certifies `LabelProps` as it stood before the `(N.decode A).Nonempty` guard was
added: the guard is not what makes this witness work. -/
theorem witness_sampler_mem_unguarded (A : Bool) (hA : witnessNFA.UsedLabel A) :
    ∀ p ∈ (witnessOracle.sampler A).support, p.1 ∈ witnessNFA.decode A :=
  fun p hp => labelProps_witness.sampler_mem A hA
    (by rw [(witnessNFA_usedLabel_iff A).1 hA, witnessNFA_decode_true]; exact ⟨0, by simp⟩) p hp

/-! ### The parameters are tight

Three lemmas showing that `(ε₀, g, T) = (1/2, 1, 2)` cannot be improved in any
coordinate.  Together they are the certificate that the clauses of `def:prop`
are doing work here rather than being satisfied by accident. -/

/-- **Both endpoints of the uniformity window are attained.**  `sampler_uniform`
is an equality constraint at both ends for this witness. -/
theorem witness_sampler_uniform_tight :
    outProbR witnessSampler ({0} : Set (Fin 3))
        = (1 - 1 / 2) * (1 / ((witnessNFA.decode true).ncard : ℝ)) ∧
      outProbR witnessSampler ({1} : Set (Fin 3))
        = (1 + 1 / 2) * (1 / ((witnessNFA.decode true).ncard : ℝ)) := by
  rw [witnessNFA_ncard_decode_true, witnessSampler_outProbR_zero, witnessSampler_outProbR_one]
  norm_num

/-- `ε₀ = 1/2` is forced: the witness satisfies `def:prop` at **no** smaller
precision, whatever `g` and `T`.  This is `sampler_uniform` biting. -/
theorem labelProps_witness_le_eps {ε₀ : ℝ} {g T : ℕ}
    (h : LabelProps witnessNFA witnessOracle ε₀ g T) : 1 / 2 ≤ ε₀ := by
  have h₁ := (h.sampler_uniform true witnessNFA_usedLabel_true 1 (by simp)).2
  rw [witnessNFA_ncard_decode_true, witnessOracle_sampler_true,
    witnessSampler_outProbR_one] at h₁
  norm_num at h₁
  linarith

/-- `g = 1` is forced: `|A| = 2` does not fit in `2 ^ 0`.  This is `sizeBound`
biting. -/
theorem labelProps_witness_le_g {ε₀ : ℝ} {g T : ℕ}
    (h : LabelProps witnessNFA witnessOracle ε₀ g T) : 1 ≤ g := by
  have h₁ := h.sizeBound true witnessNFA_usedLabel_true
  rw [witnessNFA_ncard_decode_true] at h₁
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp at h₁
  · exact hg

/-- `T = 2` is forced: a membership test costs `2`, and so does one of the
sampler's two outcomes.  This is `memCost_le` and `sampler_cost` biting. -/
theorem labelProps_witness_le_T {ε₀ : ℝ} {g T : ℕ}
    (h : LabelProps witnessNFA witnessOracle ε₀ g T) : 2 ≤ T := by
  have h₁ := h.sampler_cost true witnessNFA_usedLabel_true (1, 2) (by
    rw [witnessOracle_sampler_true, witnessSampler_support]; right; rfl)
  exact h₁

/-! ### `Encoding` is satisfiable -/

/-- The `Encoding` of `witnessNFA`: two states, one transition, every label of
representation size `1`.  Its `size` is `2 + 1 + 1 = 4`. -/
def witnessEncoding : witnessNFA.Encoding where
  states := Finset.univ
  transitions := {(0, true, 1)}
  rsize _ := 1
  init_mem := Finset.mem_univ _
  final_mem := Finset.mem_univ _
  mem_transitions := by
    intro s A s'
    simp only [Finset.mem_singleton, Prod.mk.injEq, witnessNFA_step_iff]
    tauto
  transitions_subset := fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩

@[simp] theorem witnessEncoding_size : witnessEncoding.size = 4 := by
  simp [Encoding.size, witnessEncoding]

/-- `Encoding` is satisfiable. -/
theorem exists_encoding :
    ∃ (S Γ L : Type) (N : SuccinctNFA S Γ L), Nonempty N.Encoding :=
  ⟨Fin 2, Fin 3, Bool, witnessNFA, ⟨witnessEncoding⟩⟩

/-- **`Proposition prop:membertest` has a model.**  Its three hypotheses —
an `Encoding`, `def:prop`, and being unrolled — are simultaneously satisfiable,
so the proposition is not conditionally vacuous. -/
theorem witness_memberTest (w : List (Fin 3)) (s : Fin 2) :
    (w ∈ witnessNFA.W s ↔ s ∈ witnessEncoding.reachSet witnessOracle w) ∧
      witnessEncoding.reachCost witnessOracle w ≤ witnessEncoding.transitions.card * 2 :=
  witnessEncoding.memberTest witnessOracle labelProps_witness witnessNFA_isUnrolled w s

/-! ### The empty label, and why `sampler_mem` is guarded -/

/-- An automaton whose only label decodes to `∅`: the transition `0 → 1` is dead.
Nothing in `SuccinctNFA` forbids this, and nothing in the source does either. -/
def deadNFA : SuccinctNFA (Fin 2) (Fin 3) Unit where
  decode _ := ∅
  step s _ s' := s = 0 ∧ s' = 1
  init := 0
  final := 1

@[simp] theorem deadNFA_decode (A : Unit) : deadNFA.decode A = (∅ : Set (Fin 3)) := rfl

theorem deadNFA_usedLabel (A : Unit) : deadNFA.UsedLabel A := ⟨0, 1, rfl, rfl⟩

/-- An oracle for `deadNFA`.  Its sampler must return *something* — that is what
a `PMF` is — and whatever it returns lies outside `decode A = ∅`. -/
noncomputable def deadOracle : LabelOracle (Fin 3) Unit where
  est _ := 0
  memTest _ _ := false
  memCost _ _ := 0
  sampler _ := PMF.pure (0, 0)

/-- **`def:prop` holds on an automaton with an empty used label.**  This is what
the `(N.decode A).Nonempty` guard on `sampler_mem` buys: without it the bundle is
`IsEmpty` here, by `not_unguarded_sampler_mem_dead`. -/
theorem labelProps_dead : LabelProps deadNFA deadOracle 0 0 0 where
  finite := fun _ _ => Set.finite_empty
  sizeBound := by intro A _; simp
  memTest_correct := by intro A _ a; simp [deadOracle]
  memCost_le := fun _ _ _ => le_refl _
  est_relErr := by intro A _; simp [deadOracle, relErr]
  sampler_mem := by intro A _ hne; simp at hne
  sampler_cost := by
    intro A _ p hp
    simp only [deadOracle, PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact le_refl _
  sampler_uniform := by intro A _ a ha; simp at ha

/-- **The unguarded clause is unsatisfiable on `deadNFA`.**  No oracle at all —
not merely no *natural* one — makes the sampler's support land inside `∅`, since
a `PMF` has total mass `1` and hence nonempty support.  So the unguarded
`sampler_mem` is a covert `(N.decode A).Nonempty` assumption on every used
label. -/
theorem not_unguarded_sampler_mem_dead (O : LabelOracle (Fin 3) Unit) :
    ¬ ∀ A : Unit, deadNFA.UsedLabel A → ∀ p ∈ (O.sampler A).support, p.1 ∈ deadNFA.decode A := by
  intro h
  have hne : (deadNFA.decode ()).Nonempty :=
    nonempty_of_sampler_support_subset (h () (deadNFA_usedLabel ()))
  simp at hne

end SuccinctNFA

end Arlib.Automata
