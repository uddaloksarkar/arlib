/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Computational-DAG error propagation

A computational DAG models a floating-point evaluation of a numerical expression
as a tree of the six basic operations `+ - × ÷ √ log`, each rounded on top of
whatever error already arrived from its children, with errors tracked
*multiplicatively* (as relative errors) rather than additively.  This file
develops that machinery in full generality: the expression language `Expr`, its
ideal (`eval`) and rounded (`evalRnd`) evaluators for an *abstract* rounding oracle
satisfying the standard relative-error contract, the symbolic bottom-up error bound
`errBound`, and the master theorem bounding the true relative error of the rounded
evaluation by `errBound` plus an explicit, honestly-tracked `O(ε²)` correction.

## Design choices (documented, not hidden)

* **Exact constants are not rounded at all** (`θ = 0`, and `evalRnd` leaves a
  `const` leaf untouched). For a constant that is exactly representable this is
  one of two equally defensible modeling choices; we take it here because it makes
  the `const` case of the master theorem trivial and honest (zero error in, zero
  error out), rather than because it is somehow more "correct."
* **The `log` node carries its own lower bound.** `Expr.log (g : Expr ι) (lb : ℝ)`
  carries the promised bound `lb ≤ |log (eval env g)|` alongside the node, avoiding
  a separate side-map from nodes to bounds.
* **`errBound` needs the environment, not just the syntax tree.** The subtraction
  rule `θ_v = (θ_g·g + θ_h·h)/(g-h) + ε` mentions the *values* `g`, `h`, not just
  their symbolic error bounds — so `errBound` is parameterized by `env` as well as
  `ε`, `εlog`. This is the same information the master theorem's
  `Positive`/`ValidLb` hypotheses already need to see.
* **The `O(ε²)` slack constant `C` is shape *and* value dependent** (it uses the
  concrete magnitudes at each node, exactly as `errBound` does for `sub`), and is
  defined by the same structural recursion `errBound` uses.
* **A "small error" side condition is unavoidable for `√` and `÷`.** Both need
  their *argument's* rounded value to stay clear of zero (respectively: to stay
  nonnegative so `Real.sqrt` behaves, and to stay away from zero so division
  doesn't blow up) — a real fact about the specific `ε`, `εlog`, and the node's
  shape, not a free lunch. We state it as a single explicit hypothesis on the
  root node's own combined shape constant `W + C`, and push it down to every
  subterm via one-line monotonicity facts baked into the induction itself
  (`W`, `C` are monotone from a child to its parent by construction).
-/

set_option linter.unusedVariables false

namespace Arlib.Numerics

/-- An operation DAG (formalized here, for the purposes of the structural
induction, as a tree — shared subexpressions can be handled by unfolding, which
only weakens the constants below, not the shape of the argument) for a scalar
function built from the six basic floating-point operations. The `log` node
carries the promised lower bound `lb` on `|log (eval env g)|` alongside its
argument, per the master theorem's own hypothesis. -/
inductive Expr (ι : Type*) where
  /-- An input leaf: a floating-point number read in directly. -/
  | var : ι → Expr ι
  /-- An exact mathematical constant, not subject to rounding (`θ = 0`). -/
  | const : ℝ → Expr ι
  | add : Expr ι → Expr ι → Expr ι
  | sub : Expr ι → Expr ι → Expr ι
  | mul : Expr ι → Expr ι → Expr ι
  | div : Expr ι → Expr ι → Expr ι
  | sqrt : Expr ι → Expr ι
  /-- `log g lb`: the node `log g`, together with the promised lower bound
  `lb ≤ |log (eval env g)|` that makes its *relative* error controllable. -/
  | log : Expr ι → ℝ → Expr ι
  deriving Inhabited

namespace Expr

variable {ι : Type*}

/-- The ideal (exact real-arithmetic) evaluator. -/
noncomputable def eval (env : ι → ℝ) : Expr ι → ℝ
  | var i => env i
  | const c => c
  | add a b => eval env a + eval env b
  | sub a b => eval env a - eval env b
  | mul a b => eval env a * eval env b
  | div a b => eval env a / eval env b
  | sqrt a => Real.sqrt (eval env a)
  | log a _ => Real.log (eval env a)

/-- The rounded (floating-point) evaluator: applies the ambient rounding oracle
`rnd` at every arithmetic node and the (possibly different) oracle `rndLog` at
every `log` node, on top of the already-rounded values of the children — so a
`var` leaf itself is rounded (representing it in floating point already
introduces `ε`), while `const` is left exactly alone (it needs no rounding, by
our stated design choice `θ = 0` for exact constants). -/
noncomputable def evalRnd (rnd rndLog : ℝ → ℝ) (env : ι → ℝ) : Expr ι → ℝ
  | var i => rnd (env i)
  | const c => c
  | add a b => rnd (evalRnd rnd rndLog env a + evalRnd rnd rndLog env b)
  | sub a b => rnd (evalRnd rnd rndLog env a - evalRnd rnd rndLog env b)
  | mul a b => rnd (evalRnd rnd rndLog env a * evalRnd rnd rndLog env b)
  | div a b => rnd (evalRnd rnd rndLog env a / evalRnd rnd rndLog env b)
  | sqrt a => rnd (Real.sqrt (evalRnd rnd rndLog env a))
  | log a lb => rndLog (Real.log (evalRnd rnd rndLog env a))

/-- The symbolic, bottom-up error-propagation rule (`SymbolicErrorProp`): a
bound `θ_v` on the relative error `|rnd(v) - v| / |v|` at every node, computed
from the already-computed bounds at its children. As noted above, this needs
`env` (not just the syntax tree) because the subtraction rule refers to the
actual values `g`, `h` at that node. -/
noncomputable def errBound (ε εlog : ℝ) (env : ι → ℝ) : Expr ι → ℝ
  | var _ => ε
  | const _ => 0
  | add a b => max (errBound ε εlog env a) (errBound ε εlog env b) + ε
  | sub a b =>
      let g := eval env a
      let h := eval env b
      (errBound ε εlog env a * g + errBound ε εlog env b * h) / (g - h) + ε
  | mul a b => errBound ε εlog env a + errBound ε εlog env b + ε
  | div a b => errBound ε εlog env a + errBound ε εlog env b + ε
  | sqrt a => errBound ε εlog env a / 2 + ε
  | log a lb => errBound ε εlog env a / lb + εlog

/-- The "unit-parameter" instantiation `errBound 1 1`, used purely as a
shape/value-dependent bookkeeping constant to control the cross terms in the
master theorem's `O(ε²)` slack (see `errBound_le_W_mul`, the key lemma making
this precise). -/
noncomputable def W (env : ι → ℝ) (e : Expr ι) : ℝ := errBound 1 1 env e

/-- The explicit `O(ε²)` slack constant, defined by the same structural
recursion `errBound` uses (and, like `errBound`'s `sub` case, depending on the
concrete values at each node, not just the syntax tree) — but, importantly,
*not* on `ε` or `εlog` themselves: the recursion below already isolates the
`ε`-dependence into `errBound`/`W`. -/
noncomputable def C (env : ι → ℝ) : Expr ι → ℝ
  | var _ => 0
  | const _ => 0
  | add a b => max (W env a) (W env b) + 2 * max (C env a) (C env b)
  | mul a b =>
      let Wa := W env a; let Wb := W env b
      let Ca := C env a; let Cb := C env b
      (Wa + Wb) + 2 * (Ca + Cb) + 2 * (Wa + Ca) * (Wb + Cb)
  | div a b =>
      let Wa := W env a; let Wb := W env b
      let Ca := C env a; let Cb := C env b
      (Ca + Cb) + (Wa + Wb + Ca + Cb) + 4 * (Wa + Ca + Wb + Cb) * (Wb + Cb)
  | sqrt a =>
      let Wa := W env a; let Ca := C env a
      2 * (Wa + Ca) ^ 2 + (Wa + Ca) + 1
  | sub a b =>
      -- The cancellation case: the `O(ε²)` slack, like `errBound`'s own `sub`
      -- rule, is *amplified* by `1/(g-h)`, since the second-order terms it has
      -- to absorb are proportional to `g` and `h` separately, not to `g-h`.
      let Wa := W env a; let Wb := W env b
      let Ca := C env a; let Cb := C env b
      let g := eval env a; let h := eval env b
      ((2 * Ca + Wa) * g + (2 * Cb + Wb) * h) / (g - h)
  | log a lb =>
      -- Divided by the node's own promised lower bound `lb ≤ |log g|`, exactly
      -- as `errBound`'s `log` rule is: the second-order terms are absolute
      -- errors on `log g`, and turning them into *relative* errors costs `1/lb`.
      let Wa := W env a; let Ca := C env a
      (2 * Ca + Wa + 4 * (Wa + Ca) ^ 2) / lb

/-- Every node's ideal value is strictly positive throughout the DAG — the
hypothesis the master theorem needs threaded through the whole induction, since
the propagation rules above only make sense as *relative*-error bounds for
positive intermediate quantities. For `sub a b` we require the uniform strict
inequality `eval env b < eval env a`; the boundary case `h = 0` is the *exact*
subtraction `v = g`, with no cancellation and hence no interesting content for
this rule. For `log a lb` we require the node's *own* value `log (eval env a)`
to be positive too — a real restriction, since it excludes `log` nodes whose
argument sits in `(0,1)`. -/
def Positive (env : ι → ℝ) : Expr ι → Prop
  | var i => 0 < env i
  | const c => 0 < c
  | add a b => Positive env a ∧ Positive env b
  | sub a b => Positive env a ∧ Positive env b ∧ eval env b < eval env a
  | mul a b => Positive env a ∧ Positive env b
  | div a b => Positive env a ∧ Positive env b
  | sqrt a => Positive env a
  | log a lb => Positive env a ∧ 0 < Real.log (eval env a)

/-- Every `log` node's stated lower bound is valid, and strictly positive
(needed to divide by it in `errBound`). -/
def ValidLb (env : ι → ℝ) : Expr ι → Prop
  | var _ => True
  | const _ => True
  | add a b => ValidLb env a ∧ ValidLb env b
  | sub a b => ValidLb env a ∧ ValidLb env b
  | mul a b => ValidLb env a ∧ ValidLb env b
  | div a b => ValidLb env a ∧ ValidLb env b
  | sqrt a => ValidLb env a
  | log a lb => 0 < lb ∧ lb ≤ |Real.log (eval env a)| ∧ ValidLb env a

/-- The "not already too erroneous" side condition needed for `√`, `÷` and
`log`: at every `sqrt` node, the *argument*'s already-accumulated error bound
must stay below `1/2` (so the rounded argument stays positive, comfortably
clear of `0`, and `Real.sqrt` keeps behaving); likewise at every `div` node,
the *divisor*'s error bound must stay below `1/2` (so the rounded divisor stays
comfortably clear of `0`); and likewise at every `log` node, the *argument*'s
error bound must stay below `1/2` (so the rounded argument stays positive —
`Real.log` is junk-valued at `0` and below — and so that `log (1+δ)` admits its
first-order expansion with a *quadratic* remainder). This is a genuine,
unavoidable hypothesis — not an artifact of this formalization — since a large
enough `ε` really can round a positive quantity's floating-point image across
`0`. It is phrased once, at exactly the nodes that need it, and is *not* needed
at `add`, `mul`, or `sub` (whose own case proofs never divide by, take the
square root of, or take the logarithm of, a possibly-small rounded
quantity). -/
def ErrSmall (ε εlog : ℝ) (env : ι → ℝ) : Expr ι → Prop
  | var _ => True
  | const _ => True
  | add a b => ErrSmall ε εlog env a ∧ ErrSmall ε εlog env b
  | sub a b => ErrSmall ε εlog env a ∧ ErrSmall ε εlog env b
  | mul a b => ErrSmall ε εlog env a ∧ ErrSmall ε εlog env b
  | div a b => ErrSmall ε εlog env a ∧ ErrSmall ε εlog env b ∧
      errBound ε εlog env b + C env b * (ε + εlog) ^ 2 ≤ 1 / 2
  | sqrt a => ErrSmall ε εlog env a ∧
      errBound ε εlog env a + C env a * (ε + εlog) ^ 2 ≤ 1 / 2
  | log a _ => ErrSmall ε εlog env a ∧
      errBound ε εlog env a + C env a * (ε + εlog) ^ 2 ≤ 1 / 2

/-- Every node's ideal value is positive, given `Positive`. -/
theorem Positive.eval_pos {env : ι → ℝ} : ∀ {e : Expr ι}, Positive env e → 0 < eval env e
  | var _, h => h
  | const _, h => h
  | add a b, ⟨ha, hb⟩ => add_pos (Positive.eval_pos ha) (Positive.eval_pos hb)
  | sub a b, ⟨_, _, hlt⟩ => sub_pos.mpr hlt
  | mul a b, ⟨ha, hb⟩ => mul_pos (Positive.eval_pos ha) (Positive.eval_pos hb)
  | div a b, ⟨ha, hb⟩ => div_pos (Positive.eval_pos ha) (Positive.eval_pos hb)
  | sqrt a, ha => Real.sqrt_pos.mpr (Positive.eval_pos ha)
  | log a _, ⟨_, hlog⟩ => hlog

/-- `errBound` is nonnegative at every node, given the standard side hypotheses. -/
theorem errBound_nonneg {ε εlog : ℝ} (hε : 0 ≤ ε) (hεlog : 0 ≤ εlog) (env : ι → ℝ) :
    ∀ e : Expr ι, Positive env e → ValidLb env e → 0 ≤ errBound ε εlog env e := by
  intro e
  induction e with
  | var i => intro _ _; exact hε
  | const c => intro _ _; exact le_refl 0
  | add a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩
      have := iha hpa hla
      simp only [errBound]
      have : errBound ε εlog env a ≤ max (errBound ε εlog env a) (errBound ε εlog env b) :=
        le_max_left _ _
      linarith [iha hpa hla]
  | sub a b iha ihb =>
      intro ⟨hpa, hpb, hlt⟩ ⟨hla, hlb⟩
      have hga : 0 ≤ eval env a := (Positive.eval_pos hpa).le
      have hgb : 0 ≤ eval env b := (Positive.eval_pos hpb).le
      have hgh : 0 < eval env a - eval env b := sub_pos.mpr hlt
      have hθa := iha hpa hla
      have hθb := ihb hpb hlb
      have hnum : 0 ≤ errBound ε εlog env a * eval env a + errBound ε εlog env b * eval env b :=
        add_nonneg (mul_nonneg hθa hga) (mul_nonneg hθb hgb)
      have hq := div_nonneg hnum hgh.le
      simp only [errBound]
      linarith
  | mul a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩
      simp only [errBound]
      linarith [iha hpa hla, ihb hpb hlb]
  | div a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩
      simp only [errBound]
      linarith [iha hpa hla, ihb hpb hlb]
  | sqrt a iha =>
      intro hpa hla
      simp only [errBound]
      linarith [iha hpa hla]
  | log a lb iha =>
      intro ⟨hpa, hlog⟩ ⟨hlb0, hlbval, hla⟩
      have hθa := iha hpa hla
      have hq : 0 ≤ errBound ε εlog env a / lb := div_nonneg hθa hlb0.le
      simp only [errBound]
      linarith

/-- `W := errBound 1 1` is nonnegative — an instance of `errBound_nonneg`. -/
theorem W_nonneg (env : ι → ℝ) {e : Expr ι} (hpos : Positive env e) (hlb : ValidLb env e) :
    0 ≤ W env e :=
  errBound_nonneg zero_le_one zero_le_one env e hpos hlb

/-- The `O(ε²)` slack constant `C` is nonnegative. -/
theorem C_nonneg (env : ι → ℝ) :
    ∀ e : Expr ι, Positive env e → ValidLb env e → 0 ≤ C env e := by
  intro e
  induction e with
  | var i => intro _ _; exact le_refl 0
  | const c => intro _ _; exact le_refl 0
  | add a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩
      have hWa := W_nonneg env hpa hla
      have hCa := iha hpa hla
      have hCb := ihb hpb hlb
      simp only [C]
      have hw : Expr.W env a ≤ max (Expr.W env a) (Expr.W env b) := le_max_left _ _
      have hc : Expr.C env a ≤ max (Expr.C env a) (Expr.C env b) := le_max_left _ _
      linarith
  | mul a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩
      have hWa := W_nonneg env hpa hla; have hWb := W_nonneg env hpb hlb
      have hCa := iha hpa hla; have hCb := ihb hpb hlb
      simp only [C]
      have h1 : 0 ≤ Expr.W env a + Expr.C env a := by linarith
      have h2 : 0 ≤ Expr.W env b + Expr.C env b := by linarith
      have := mul_nonneg h1 h2
      linarith
  | div a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩
      have hWa := W_nonneg env hpa hla; have hWb := W_nonneg env hpb hlb
      have hCa := iha hpa hla; have hCb := ihb hpb hlb
      simp only [C]
      have hp3 : 0 ≤ (Expr.W env a + Expr.C env a + Expr.W env b + Expr.C env b) *
          (Expr.W env b + Expr.C env b) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
  | sqrt a iha =>
      intro hpa hla
      replace hpa : Positive env a := hpa
      replace hla : ValidLb env a := hla
      have hWa := W_nonneg env hpa hla; have hCa := iha hpa hla
      simp only [C]
      have : 0 ≤ (Expr.W env a + Expr.C env a) ^ 2 := sq_nonneg _
      linarith
  | sub a b iha ihb =>
      intro ⟨hpa, hpb, hlt⟩ ⟨hla, hlb⟩
      have hCa := iha hpa hla; have hCb := ihb hpb hlb
      have hWa := W_nonneg env hpa hla; have hWb := W_nonneg env hpb hlb
      have hga : 0 ≤ eval env a := (Positive.eval_pos hpa).le
      have hgb : 0 ≤ eval env b := (Positive.eval_pos hpb).le
      have hgh : 0 < eval env a - eval env b := sub_pos.mpr hlt
      simp only [C]
      refine div_nonneg ?_ hgh.le
      have h1 : 0 ≤ (2 * Expr.C env a + Expr.W env a) * eval env a :=
        mul_nonneg (by linarith) hga
      have h2 : 0 ≤ (2 * Expr.C env b + Expr.W env b) * eval env b :=
        mul_nonneg (by linarith) hgb
      linarith
  | log a lb iha =>
      intro ⟨hpa, _⟩ ⟨hlb0, _, hla⟩
      have hCa := iha hpa hla
      have hWa := W_nonneg env hpa hla
      simp only [C]
      refine div_nonneg ?_ hlb0.le
      nlinarith [sq_nonneg (Expr.W env a + Expr.C env a)]

/-- The key auxiliary lemma: for `ε, εlog ≥ 0`, the symbolic error bound `θ(e)`
is dominated by the "unit-parameter" shape constant `W(e)` times `ε + εlog`.
This is what lets the master theorem's proof turn the genuinely-linear-in-`ε`
cross terms produced by the first-order expansion at each node (e.g. the
`ε · θ_g` term in the multiplication step) into the theorem's `O(ε²)` slack:
`ε · θ(g) ≤ ε · W(g) · (ε+εlog) ≤ W(g) · (ε+εlog)²`. -/
theorem errBound_le_W_mul {ε εlog : ℝ} (hε : 0 ≤ ε) (hεlog : 0 ≤ εlog) (env : ι → ℝ) :
    ∀ e : Expr ι, Positive env e → ValidLb env e →
      errBound ε εlog env e ≤ W env e * (ε + εlog) := by
  intro e
  induction e with
  | var i => intro _ _; simp only [W, errBound]; linarith
  | const c => intro _ _; simp only [W, errBound]; linarith
  | add a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩
      have hi := iha hpa hla
      have hj := ihb hpb hlb
      have hWa := W_nonneg env hpa hla; have hWb := W_nonneg env hpb hlb
      simp only [W, errBound] at *
      have key : max (errBound ε εlog env a) (errBound ε εlog env b) ≤
          max (errBound 1 1 env a) (errBound 1 1 env b) * (ε + εlog) := by
        rcases le_total (errBound ε εlog env a) (errBound ε εlog env b) with h | h
        · rw [max_eq_right h]
          calc errBound ε εlog env b ≤ errBound 1 1 env b * (ε + εlog) := hj
            _ ≤ max (errBound 1 1 env a) (errBound 1 1 env b) * (ε + εlog) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
        · rw [max_eq_left h]
          calc errBound ε εlog env a ≤ errBound 1 1 env a * (ε + εlog) := hi
            _ ≤ max (errBound 1 1 env a) (errBound 1 1 env b) * (ε + εlog) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      linarith
  | mul a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩
      simp only [W, errBound] at *
      linarith [iha hpa hla, ihb hpb hlb]
  | div a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩
      simp only [W, errBound] at *
      linarith [iha hpa hla, ihb hpb hlb]
  | sqrt a iha =>
      intro hpa hla
      simp only [W, errBound] at *
      linarith [iha hpa hla]
  | log a lb iha =>
      intro ⟨hpa, _⟩ ⟨hlb0, _, hla⟩
      have hi := iha hpa hla
      simp only [W, errBound] at *
      have hstep : errBound ε εlog env a / lb ≤ (errBound 1 1 env a * (ε + εlog)) / lb :=
        (div_le_div_iff_of_pos_right hlb0).mpr hi
      rw [mul_div_right_comm] at hstep
      linarith
  | sub a b iha ihb =>
      intro ⟨hpa, hpb, hlt⟩ ⟨hla, hlb⟩
      have hi := iha hpa hla
      have hj := ihb hpb hlb
      have hga : 0 ≤ eval env a := (Positive.eval_pos hpa).le
      have hgb : 0 ≤ eval env b := (Positive.eval_pos hpb).le
      have hgh : 0 < eval env a - eval env b := sub_pos.mpr hlt
      simp only [W, errBound] at *
      have hnum : errBound ε εlog env a * eval env a + errBound ε εlog env b * eval env b ≤
          (errBound 1 1 env a * eval env a + errBound 1 1 env b * eval env b) * (ε + εlog) := by
        nlinarith [mul_le_mul_of_nonneg_right hi hga, mul_le_mul_of_nonneg_right hj hgb]
      have hstep := (div_le_div_iff_of_pos_right hgh).mpr hnum
      rw [mul_div_right_comm] at hstep
      linarith

/-- A weighted average of `x`, `y` (with nonnegative weights `p`, `q`) is
bounded by `max x y` times the total weight — the elementary fact behind the
`add` case of the master theorem (it is what lets `θ_v = max(θ_g,θ_h) + ε`
dominate the true weighted contribution `θ_g·g + θ_h·h` of the two summands). -/
theorem weighted_avg_le_max (x y p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    x * p + y * q ≤ max x y * (p + q) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

/-- The quadratic remainder of the first-order Taylor expansion of `√(1+δ)`
around `δ = 0` is *exactly* `-δ²/(2(√(1+δ)+1)²)`, hence bounded by `δ²/2` —
the fact behind the `√` case of the master theorem. -/
theorem abs_sqrt_one_add_sub_one_sub_half_le {δ : ℝ} (hδ : -1 ≤ δ) :
    |Real.sqrt (1 + δ) - 1 - δ / 2| ≤ δ ^ 2 / 2 := by
  have hu : (0:ℝ) ≤ 1 + δ := by linarith
  set s := Real.sqrt (1 + δ) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 + δ := Real.sq_sqrt hu
  have hδeq : δ = s ^ 2 - 1 := by linarith
  have hkey : (s - 1 - δ / 2) * (2 * (s + 1) ^ 2) = -δ ^ 2 := by
    rw [hδeq]; ring
  have hD1 : (1:ℝ) ≤ (s + 1) ^ 2 := by nlinarith [hs_nonneg]
  rw [abs_le]
  constructor
  · nlinarith [hkey, hD1, sq_nonneg δ, mul_nonneg (sub_nonneg.mpr hD1) (sq_nonneg δ)]
  · nlinarith [hkey, hD1, sq_nonneg δ, mul_nonneg (sub_nonneg.mpr hD1) (sq_nonneg δ)]

/-- The first-order expansion of `log (1+δ)` around `δ = 0` has a genuinely
quadratic remainder on `|δ| ≤ 1/2`: `|log (1+δ)| ≤ |δ| + 2δ²`. Both directions
come from the single Mathlib inequality `Real.log_le_sub_one_of_pos`
(`log x ≤ x - 1`): applied to `1+δ` it gives `log (1+δ) ≤ δ`, and applied to
`1/(1+δ)` it gives `-log (1+δ) ≤ 1/(1+δ) - 1 = -δ/(1+δ)`, whose gap over `|δ|`
is `≤ 2δ²` precisely because `|δ| ≤ 1/2` keeps `1+δ` away from `0`. This is the
fact behind the `log` case of the master theorem — the constant `2` (rather
than the sharp `1/(2(1-|δ|))`) is all that case needs. -/
theorem abs_log_one_add_le {δ : ℝ} (hδ : |δ| ≤ 1 / 2) :
    |Real.log (1 + δ)| ≤ |δ| + 2 * δ ^ 2 := by
  have hδ' := abs_le.mp hδ
  have hpos : (0:ℝ) < 1 + δ := by linarith [hδ'.1]
  have hupper : Real.log (1 + δ) ≤ δ := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hinv : Real.log (1 / (1 + δ)) ≤ 1 / (1 + δ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hloginv : Real.log (1 / (1 + δ)) = -Real.log (1 + δ) := by
    rw [one_div, Real.log_inv]
  have hlower : -Real.log (1 + δ) ≤ 1 / (1 + δ) - 1 := by rw [← hloginv]; exact hinv
  have hkey : 1 / (1 + δ) - 1 ≤ |δ| + 2 * δ ^ 2 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hpos]
    rcases abs_cases δ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [hδ'.1, hδ'.2, sq_nonneg δ]
  rw [abs_le]
  exact ⟨by linarith, by linarith [le_abs_self δ, sq_nonneg δ]⟩

set_option maxHeartbeats 16000000

/-- **The master theorem.** Given the
standard rounding contracts for `rnd` (unit round-off `ε`) and `rndLog` (unit
round-off `εlog`), `ε + εlog ≤ 1` (unit round-offs are always tiny — far below
`1` — this just makes that precise), positivity of every node's ideal value,
validity of every `log` node's stated lower bound, and the "not already too
erroneous" side condition `ErrSmall` at the `√`/`÷` nodes that need it, the
bottom-up `errBound` bounds the relative error of the fully rounded evaluation,
up to an explicit, honestly-computed `O(ε²)` correction `C e * (ε+εlog)^2`.

Proved by structural induction on `e` (a tree, for the purposes of this
induction — shared subexpressions can be handled by unfolding, which only
weakens the constants, not the shape of the argument), with each node type's
step a first-order expansion in `θ`
(e.g. multiplication: `rnd(v) = rnd(rnd(g)·rnd(h)) ≤ rnd(g)·rnd(h)·(1+ε) ≤
g(1+θg)·h(1+θh)·(1+ε) = gh·(1+θg+θh+ε+O(ε²))`), with the genuinely-`O(ε²)`
cross terms bounded via `errBound_le_W_mul` and discharged into `C`.

**Status**: all eight node shapes (`var`, `const`, `add`, `sub`, `mul`, `div`,
`sqrt`, `log`) are fully proved; the statement uses no `sorry`. -/
theorem abs_evalRnd_sub_eval_le {ε εlog : ℝ} (rnd rndLog : ℝ → ℝ)
    (hrnd : ∀ x : ℝ, |rnd x - x| ≤ ε * |x|) (hrndLog : ∀ x : ℝ, |rndLog x - x| ≤ εlog * |x|)
    (hε : 0 ≤ ε) (hεlog : 0 ≤ εlog) (hm : ε + εlog ≤ 1) (env : ι → ℝ) :
    ∀ e : Expr ι, Positive env e → ValidLb env e → ErrSmall ε εlog env e →
      |evalRnd rnd rndLog env e - eval env e| ≤
        (errBound ε εlog env e + C env e * (ε + εlog) ^ 2) * |eval env e| := by
  intro e
  induction e with
  | var i =>
      intro _ _ _
      simp only [eval, evalRnd, errBound, C, zero_mul, add_zero]
      exact hrnd (env i)
  | const c =>
      intro _ _ _
      simp [eval, evalRnd, errBound, C]
  | add a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩ ⟨hsa, hsb⟩
      have hVa := Positive.eval_pos hpa
      have hVb := Positive.eval_pos hpb
      have hm0 : (0:ℝ) ≤ ε + εlog := by linarith
      have hea := iha hpa hla hsa
      have heb := ihb hpb hlb hsb
      rw [abs_of_pos hVa] at hea
      rw [abs_of_pos hVb] at heb
      rw [abs_le] at hea heb
      have hVab_pos : (0:ℝ) < eval env a + eval env b := by linarith
      show |evalRnd rnd rndLog env (Expr.add a b) - eval env (Expr.add a b)| ≤
          (errBound ε εlog env (Expr.add a b) + C env (Expr.add a b) * (ε + εlog) ^ 2) *
            |eval env (Expr.add a b)|
      have heval : eval env (Expr.add a b) = eval env a + eval env b := rfl
      have hrndeval : evalRnd rnd rndLog env (Expr.add a b) =
          rnd (evalRnd rnd rndLog env a + evalRnd rnd rndLog env b) := rfl
      rw [heval, hrndeval, abs_of_pos hVab_pos]
      simp only [errBound, C]
      set Ra := evalRnd rnd rndLog env a
      set Rb := evalRnd rnd rndLog env b
      set Va := eval env a
      set Vb := eval env b
      set θa := errBound ε εlog env a
      set θb := errBound ε εlog env b
      set Ca := C env a
      set Cb := C env b
      -- Step A: the additive triangle bound on the *unrounded* sum.
      have hΔ : |Ra + Rb - (Va + Vb)| ≤ (θa + Ca * (ε + εlog) ^ 2) * Va +
          (θb + Cb * (ε + εlog) ^ 2) * Vb := by
        rw [abs_le]; constructor <;> linarith [hea.1, hea.2, heb.1, heb.2]
      have hΔ' := abs_le.mp hΔ
      -- Step B: bound on |Ra+Rb| itself, feeding the rounding-oracle bound.
      have hSabs : |Ra + Rb| ≤ (Va + Vb) + ((θa + Ca * (ε + εlog) ^ 2) * Va +
          (θb + Cb * (ε + εlog) ^ 2) * Vb) := by
        rw [abs_le]; constructor <;> linarith [hΔ'.1, hΔ'.2]
      have hSabs' := abs_le.mp hSabs
      have hrnd' := abs_le.mp (hrnd (Ra + Rb))
      -- Step C: the full rounded-sum bound, unsimplified.
      have hΔ2 : |rnd (Ra + Rb) - (Va + Vb)| ≤
          ε * ((Va + Vb) + ((θa + Ca * (ε + εlog) ^ 2) * Va + (θb + Cb * (ε + εlog) ^ 2) * Vb)) +
          ((θa + Ca * (ε + εlog) ^ 2) * Va + (θb + Cb * (ε + εlog) ^ 2) * Vb) := by
        rw [abs_le]; constructor <;> nlinarith [hrnd'.1, hrnd'.2, hΔ'.1, hΔ'.2]
      -- Step D: dominate the cross terms into the `max`-shaped target.
      have hi : θa * Va + θb * Vb ≤ max θa θb * (Va + Vb) :=
        weighted_avg_le_max θa θb Va Vb hVa.le hVb.le
      have hWa_nonneg := W_nonneg env hpa hla
      have hWb_nonneg := W_nonneg env hpb hlb
      have hθWa := errBound_le_W_mul hε hεlog env a hpa hla
      have hθWb := errBound_le_W_mul hε hεlog env b hpb hlb
      have hmaxθW : max θa θb ≤ max (W env a) (W env b) * (ε + εlog) := by
        apply max_le
        · exact hθWa.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hm0)
        · exact hθWb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hm0)
      have hVab_nonneg : (0:ℝ) ≤ Va + Vb := by linarith
      have hWmax_nonneg : (0:ℝ) ≤ max (W env a) (W env b) := le_trans hWa_nonneg (le_max_left _ _)
      have h1 : θa * Va + θb * Vb ≤ max (W env a) (W env b) * (ε + εlog) * (Va + Vb) :=
        hi.trans (mul_le_mul_of_nonneg_right hmaxθW hVab_nonneg)
      have h1_nonneg : (0:ℝ) ≤ max (W env a) (W env b) * (ε + εlog) * (Va + Vb) :=
        mul_nonneg (mul_nonneg hWmax_nonneg hm0) hVab_nonneg
      have hii : ε * (θa * Va + θb * Vb) ≤ max (W env a) (W env b) * (ε + εlog) ^ 2 * (Va + Vb) :=
        calc ε * (θa * Va + θb * Vb)
            ≤ ε * (max (W env a) (W env b) * (ε + εlog) * (Va + Vb)) :=
              mul_le_mul_of_nonneg_left h1 hε
          _ ≤ (ε + εlog) * (max (W env a) (W env b) * (ε + εlog) * (Va + Vb)) :=
              mul_le_mul_of_nonneg_right (by linarith) h1_nonneg
          _ = max (W env a) (W env b) * (ε + εlog) ^ 2 * (Va + Vb) := by ring
      have hCa_nonneg : (0:ℝ) ≤ Ca := C_nonneg env a hpa hla
      have hCb_nonneg : (0:ℝ) ≤ Cb := C_nonneg env b hpb hlb
      have hCmax_nonneg : (0:ℝ) ≤ max Ca Cb := le_trans hCa_nonneg (le_max_left _ _)
      have hsqnonneg : (0:ℝ) ≤ (ε + εlog) ^ 2 := sq_nonneg _
      have hiii : Ca * (ε + εlog) ^ 2 * Va + Cb * (ε + εlog) ^ 2 * Vb ≤
          max Ca Cb * (ε + εlog) ^ 2 * (Va + Vb) := by
        have hw := weighted_avg_le_max Ca Cb ((ε + εlog) ^ 2 * Va) ((ε + εlog) ^ 2 * Vb)
          (mul_nonneg hsqnonneg hVa.le) (mul_nonneg hsqnonneg hVb.le)
        calc Ca * (ε + εlog) ^ 2 * Va + Cb * (ε + εlog) ^ 2 * Vb
            = Ca * ((ε + εlog) ^ 2 * Va) + Cb * ((ε + εlog) ^ 2 * Vb) := by ring
          _ ≤ max Ca Cb * ((ε + εlog) ^ 2 * Va + (ε + εlog) ^ 2 * Vb) := hw
          _ = max Ca Cb * (ε + εlog) ^ 2 * (Va + Vb) := by ring
      have hiii_nonneg : (0:ℝ) ≤ max Ca Cb * (ε + εlog) ^ 2 * (Va + Vb) :=
        mul_nonneg (mul_nonneg hCmax_nonneg hsqnonneg) hVab_nonneg
      have hLHSnonneg : (0:ℝ) ≤ Ca * (ε + εlog) ^ 2 * Va + Cb * (ε + εlog) ^ 2 * Vb :=
        add_nonneg (mul_nonneg (mul_nonneg hCa_nonneg hsqnonneg) hVa.le)
          (mul_nonneg (mul_nonneg hCb_nonneg hsqnonneg) hVb.le)
      have hε_le_one : ε ≤ 1 := by linarith
      have hiv : ε * (Ca * (ε + εlog) ^ 2 * Va + Cb * (ε + εlog) ^ 2 * Vb) ≤
          max Ca Cb * (ε + εlog) ^ 2 * (Va + Vb) :=
        calc ε * (Ca * (ε + εlog) ^ 2 * Va + Cb * (ε + εlog) ^ 2 * Vb)
            ≤ 1 * (max Ca Cb * (ε + εlog) ^ 2 * (Va + Vb)) :=
              mul_le_mul hε_le_one hiii hLHSnonneg (by linarith)
          _ = max Ca Cb * (ε + εlog) ^ 2 * (Va + Vb) := by ring
      rw [abs_le]
      have hΔ2' := abs_le.mp hΔ2
      constructor <;> linarith [hΔ2'.1, hΔ2'.2, hi, hii, hiii, hiv]
  | sub a b iha ihb =>
      intro ⟨hpa, hpb, hlt⟩ ⟨hla, hlb⟩ ⟨hsa, hsb⟩
      have hVa := Positive.eval_pos hpa
      have hVb := Positive.eval_pos hpb
      have hm0 : (0:ℝ) ≤ ε + εlog := by linarith
      have hea := iha hpa hla hsa
      have heb := ihb hpb hlb hsb
      rw [abs_of_pos hVa] at hea
      rw [abs_of_pos hVb] at heb
      have hDpos : (0:ℝ) < eval env a - eval env b := sub_pos.mpr hlt
      show |evalRnd rnd rndLog env (Expr.sub a b) - eval env (Expr.sub a b)| ≤
          (errBound ε εlog env (Expr.sub a b) + C env (Expr.sub a b) * (ε + εlog) ^ 2) *
            |eval env (Expr.sub a b)|
      have heval : eval env (Expr.sub a b) = eval env a - eval env b := rfl
      have hrndeval : evalRnd rnd rndLog env (Expr.sub a b) =
          rnd (evalRnd rnd rndLog env a - evalRnd rnd rndLog env b) := rfl
      rw [heval, hrndeval, abs_of_pos hDpos]
      simp only [errBound, C]
      set Ra := evalRnd rnd rndLog env a
      set Rb := evalRnd rnd rndLog env b
      set Va := eval env a
      set Vb := eval env b
      set θa := errBound ε εlog env a
      set θb := errBound ε εlog env b
      set Ca := C env a
      set Cb := C env b
      have hWa_nonneg := W_nonneg env hpa hla
      have hWb_nonneg := W_nonneg env hpb hlb
      have hθWa := errBound_le_W_mul hε hεlog env a hpa hla
      have hθWb := errBound_le_W_mul hε hεlog env b hpb hlb
      have hCa_nonneg : (0:ℝ) ≤ Ca := C_nonneg env a hpa hla
      have hCb_nonneg : (0:ℝ) ≤ Cb := C_nonneg env b hpb hlb
      have hθa_nonneg : (0:ℝ) ≤ θa := errBound_nonneg hε hεlog env a hpa hla
      have hθb_nonneg : (0:ℝ) ≤ θb := errBound_nonneg hε hεlog env b hpb hlb
      have hsqnonneg : (0:ℝ) ≤ (ε + εlog) ^ 2 := sq_nonneg _
      have hBa_nonneg : (0:ℝ) ≤ θa + Ca * (ε + εlog) ^ 2 :=
        add_nonneg hθa_nonneg (mul_nonneg hCa_nonneg hsqnonneg)
      have hBb_nonneg : (0:ℝ) ≤ θb + Cb * (ε + εlog) ^ 2 :=
        add_nonneg hθb_nonneg (mul_nonneg hCb_nonneg hsqnonneg)
      have hea' := abs_le.mp hea
      have heb' := abs_le.mp heb
      -- Fold the accumulated child bounds into single opaque names (the `mul`
      -- case's `Δbig` trick), so every step below stays short.
      set Ba := θa + Ca * (ε + εlog) ^ 2 with hBa_def
      set Bb := θb + Cb * (ε + εlog) ^ 2 with hBb_def
      clear_value Ba Bb
      set N := Ba * Va + Bb * Vb with hN_def
      clear_value N
      -- Step A: the additive triangle bound on the *unrounded* difference.
      -- Note the numerator `N` is proportional to `Va`, `Vb` separately — this
      -- is exactly the cancellation amplification the `sub` rule pays for.
      have hNnonneg : (0:ℝ) ≤ N := by
        rw [hN_def]; exact add_nonneg (mul_nonneg hBa_nonneg hVa.le) (mul_nonneg hBb_nonneg hVb.le)
      have hN : |Ra - Rb - (Va - Vb)| ≤ N := by
        rw [hN_def, abs_le]; constructor <;> linarith [hea'.1, hea'.2, heb'.1, heb'.2]
      have hN' := abs_le.mp hN
      -- Step B: bound on `|Ra - Rb|` itself, feeding the rounding-oracle bound.
      have hSabs : |Ra - Rb| ≤ (Va - Vb) + N := by
        rw [abs_le]; constructor <;> linarith [hN'.1, hN'.2]
      have hrnd' := abs_le.mp (hrnd (Ra - Rb))
      have heps := mul_le_mul_of_nonneg_left hSabs hε
      -- Step C: the full rounded-difference bound, unsimplified.
      have hFull : |rnd (Ra - Rb) - (Va - Vb)| ≤ ε * ((Va - Vb) + N) + N := by
        rw [abs_le]; constructor <;> linarith [hrnd'.1, hrnd'.2, heps, hN'.1, hN'.2]
      -- Step D: dominate the genuinely-`O(ε²)` pieces into `C (sub a b)`.
      have hmm : (ε + εlog) ^ 2 ≤ (ε + εlog) * 1 := by nlinarith [hm0, hm]
      have hBa_le : Ba ≤ (W env a + Ca) * (ε + εlog) := by
        rw [hBa_def]; nlinarith [hθWa, mul_le_mul_of_nonneg_left hmm hCa_nonneg]
      have hBb_le : Bb ≤ (W env b + Cb) * (ε + εlog) := by
        rw [hBb_def]; nlinarith [hθWb, mul_le_mul_of_nonneg_left hmm hCb_nonneg]
      have hNle : N ≤ ((W env a + Ca) * (ε + εlog)) * Va + ((W env b + Cb) * (ε + εlog)) * Vb := by
        rw [hN_def]
        exact add_le_add (mul_le_mul_of_nonneg_right hBa_le hVa.le)
          (mul_le_mul_of_nonneg_right hBb_le hVb.le)
      have hepsN : ε * N ≤
          (ε + εlog) * (((W env a + Ca) * (ε + εlog)) * Va + ((W env b + Cb) * (ε + εlog)) * Vb) :=
        le_trans (mul_le_mul_of_nonneg_right (by linarith) hNnonneg)
          (mul_le_mul_of_nonneg_left hNle hm0)
      have hN_expand : N = θa * Va + θb * Vb + (Ca * Va + Cb * Vb) * (ε + εlog) ^ 2 := by
        rw [hN_def, hBa_def, hBb_def]; ring
      have hCoeff : ε * ((Va - Vb) + N) + N ≤
          (θa * Va + θb * Vb) + ε * (Va - Vb) +
            ((2 * Ca + W env a) * Va + (2 * Cb + W env b) * Vb) * (ε + εlog) ^ 2 := by
        linarith [hepsN, hN_expand]
      -- Step E: `((·)/(Va-Vb)) * (Va-Vb)` cancels, since `Va - Vb > 0`.
      have hRHS : ((θa * Va + θb * Vb) / (Va - Vb) + ε +
            ((2 * Ca + W env a) * Va + (2 * Cb + W env b) * Vb) / (Va - Vb) *
              (ε + εlog) ^ 2) * (Va - Vb) =
          (θa * Va + θb * Vb) + ε * (Va - Vb) +
            ((2 * Ca + W env a) * Va + (2 * Cb + W env b) * Vb) * (ε + εlog) ^ 2 := by
        field_simp
      rw [hRHS]
      exact le_trans hFull hCoeff
  | mul a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩ ⟨hsa, hsb⟩
      have hVa := Positive.eval_pos hpa
      have hVb := Positive.eval_pos hpb
      have hm0 : (0:ℝ) ≤ ε + εlog := by linarith
      have hVaVb_pos : (0:ℝ) < eval env a * eval env b := mul_pos hVa hVb
      have hea := iha hpa hla hsa
      have heb := ihb hpb hlb hsb
      rw [abs_of_pos hVa] at hea
      rw [abs_of_pos hVb] at heb
      show |evalRnd rnd rndLog env (Expr.mul a b) - eval env (Expr.mul a b)| ≤
          (errBound ε εlog env (Expr.mul a b) + C env (Expr.mul a b) * (ε + εlog) ^ 2) *
            |eval env (Expr.mul a b)|
      have heval : eval env (Expr.mul a b) = eval env a * eval env b := rfl
      have hrndeval : evalRnd rnd rndLog env (Expr.mul a b) =
          rnd (evalRnd rnd rndLog env a * evalRnd rnd rndLog env b) := rfl
      rw [heval, hrndeval, abs_of_pos hVaVb_pos]
      simp only [errBound, C]
      set Ra := evalRnd rnd rndLog env a
      set Rb := evalRnd rnd rndLog env b
      set Va := eval env a
      set Vb := eval env b
      set θa := errBound ε εlog env a
      set θb := errBound ε εlog env b
      set Ca := C env a
      set Cb := C env b
      have hWa_nonneg := W_nonneg env hpa hla
      have hWb_nonneg := W_nonneg env hpb hlb
      have hθWa := errBound_le_W_mul hε hεlog env a hpa hla
      have hθWb := errBound_le_W_mul hε hεlog env b hpb hlb
      have hCa_nonneg : (0:ℝ) ≤ Ca := C_nonneg env a hpa hla
      have hCb_nonneg : (0:ℝ) ≤ Cb := C_nonneg env b hpb hlb
      have hθa_nonneg : (0:ℝ) ≤ θa := errBound_nonneg hε hεlog env a hpa hla
      have hθb_nonneg : (0:ℝ) ≤ θb := errBound_nonneg hε hεlog env b hpb hlb
      have hsqnonneg : (0:ℝ) ≤ (ε + εlog) ^ 2 := sq_nonneg _
      have hEa_nonneg : (0:ℝ) ≤ θa + Ca * (ε + εlog) ^ 2 :=
        add_nonneg hθa_nonneg (mul_nonneg hCa_nonneg hsqnonneg)
      have hEb_nonneg : (0:ℝ) ≤ θb + Cb * (ε + εlog) ^ 2 :=
        add_nonneg hθb_nonneg (mul_nonneg hCb_nonneg hsqnonneg)
      -- Step 1: the exact `ring` identity behind `Ra*Rb - Va*Vb`, and the
      -- resulting bound on it, split into the "linear" pieces and the
      -- genuinely-quadratic cross term `P`.
      have hterm1 : |Va * (Rb - Vb)| ≤ θb * (Va * Vb) + Cb * (ε + εlog) ^ 2 * (Va * Vb) := by
        rw [abs_mul, abs_of_pos hVa]
        calc Va * |Rb - Vb| ≤ Va * ((θb + Cb * (ε + εlog) ^ 2) * Vb) :=
              mul_le_mul_of_nonneg_left heb hVa.le
          _ = θb * (Va * Vb) + Cb * (ε + εlog) ^ 2 * (Va * Vb) := by ring
      have hterm2 : |Vb * (Ra - Va)| ≤ θa * (Va * Vb) + Ca * (ε + εlog) ^ 2 * (Va * Vb) := by
        rw [abs_mul, abs_of_pos hVb]
        calc Vb * |Ra - Va| ≤ Vb * ((θa + Ca * (ε + εlog) ^ 2) * Va) :=
              mul_le_mul_of_nonneg_left hea hVb.le
          _ = θa * (Va * Vb) + Ca * (ε + εlog) ^ 2 * (Va * Vb) := by ring
      have hterm3 : |(Ra - Va) * (Rb - Vb)| ≤
          (θa + Ca * (ε + εlog) ^ 2) * Va * ((θb + Cb * (ε + εlog) ^ 2) * Vb) := by
        rw [abs_mul]
        exact mul_le_mul hea heb (abs_nonneg _)
          (mul_nonneg hEa_nonneg hVa.le)
      have hid : Ra * Rb - Va * Vb = Va * (Rb - Vb) + Vb * (Ra - Va) + (Ra - Va) * (Rb - Vb) := by
        ring
      have hΔ : |Ra * Rb - Va * Vb| ≤
          (θb * (Va * Vb) + Cb * (ε + εlog) ^ 2 * (Va * Vb)) +
          (θa * (Va * Vb) + Ca * (ε + εlog) ^ 2 * (Va * Vb)) +
          (θa + Ca * (ε + εlog) ^ 2) * Va * ((θb + Cb * (ε + εlog) ^ 2) * Vb) := by
        rw [hid, abs_le]
        constructor <;>
          linarith [abs_le.mp hterm1 |>.1, abs_le.mp hterm1 |>.2,
            abs_le.mp hterm2 |>.1, abs_le.mp hterm2 |>.2,
            abs_le.mp hterm3 |>.1, abs_le.mp hterm3 |>.2]
      -- Fold the (large) triangle-inequality bound into a single opaque name:
      -- keeping every later statement short is what keeps `ring`/`linarith`
      -- fast below (an un-folded copy of this expression recurs 3-4 times
      -- otherwise, and elaborating that repeatedly is what timed out).
      set Δbig := (θb * (Va * Vb) + Cb * (ε + εlog) ^ 2 * (Va * Vb)) +
          (θa * (Va * Vb) + Ca * (ε + εlog) ^ 2 * (Va * Vb)) +
          (θa + Ca * (ε + εlog) ^ 2) * Va * ((θb + Cb * (ε + εlog) ^ 2) * Vb) with hΔbig_def
      have hΔ' := abs_le.mp hΔ
      -- Step 2: bound on `|Ra*Rb|` itself.
      have hSabs : |Ra * Rb| ≤ Va * Vb + Δbig := by
        rw [abs_le]; constructor <;> linarith [hΔ'.1, hΔ'.2]
      have hrnd' := abs_le.mp (hrnd (Ra * Rb))
      have hepsRaRb : ε * |Ra * Rb| ≤ ε * (Va * Vb + Δbig) := mul_le_mul_of_nonneg_left hSabs hε
      -- Step 3/4: the full rounded-product bound, unsimplified.
      have hΔ2 : |rnd (Ra * Rb) - Va * Vb| ≤ ε * (Va * Vb + Δbig) + Δbig := by
        rw [abs_le]
        constructor <;> linarith [hrnd'.1, hrnd'.2, hepsRaRb, hΔ'.1, hΔ'.2]
      -- Re-associate the bound so the final assembly is a bare linear
      -- combination against `hA`, `hB`, `hC` below (no further `ring`
      -- discovery needed at that point). The one `ring` call below is the
      -- only place the fully-expanded expression is elaborated at all.
      have hΔ2_expand : |rnd (Ra * Rb) - Va * Vb| ≤
          ε * (Va * Vb) +
          (θa * (Va * Vb) + θb * (Va * Vb)) +
          ε * (θb * (Va * Vb) + θa * (Va * Vb)) +
          (1 + ε) * (Cb * (ε + εlog) ^ 2 * (Va * Vb) + Ca * (ε + εlog) ^ 2 * (Va * Vb)) +
          (1 + ε) * ((θa + Ca * (ε + εlog) ^ 2) * Va * ((θb + Cb * (ε + εlog) ^ 2) * Vb)) := by
        have heq : ε * (Va * Vb + Δbig) + Δbig =
            ε * (Va * Vb) +
            (θa * (Va * Vb) + θb * (Va * Vb)) +
            ε * (θb * (Va * Vb) + θa * (Va * Vb)) +
            (1 + ε) * (Cb * (ε + εlog) ^ 2 * (Va * Vb) + Ca * (ε + εlog) ^ 2 * (Va * Vb)) +
            (1 + ε) * ((θa + Ca * (ε + εlog) ^ 2) * Va * ((θb + Cb * (ε + εlog) ^ 2) * Vb)) := by
          rw [hΔbig_def]; ring
        rw [← heq]; exact hΔ2
      have hΔ2' := abs_le.mp hΔ2_expand
      -- Step 5: dominate the genuinely-`O(ε²)` cross terms.
      have hVaVb_nonneg : (0:ℝ) ≤ Va * Vb := mul_nonneg hVa.le hVb.le
      have hA : ε * (θb * (Va * Vb) + θa * (Va * Vb)) ≤
          (W env a + W env b) * (ε + εlog) ^ 2 * (Va * Vb) := by
        have hstepa : ε * (θa * (Va * Vb)) ≤ W env a * (ε + εlog) ^ 2 * (Va * Vb) := by
          calc ε * (θa * (Va * Vb)) ≤ ε * (W env a * (ε + εlog) * (Va * Vb)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hθWa hVaVb_nonneg) hε
            _ ≤ (ε + εlog) * (W env a * (ε + εlog) * (Va * Vb)) := by
                have hnn : (0:ℝ) ≤ W env a * (ε + εlog) * (Va * Vb) :=
                  mul_nonneg (mul_nonneg hWa_nonneg hm0) hVaVb_nonneg
                exact mul_le_mul_of_nonneg_right (by linarith) hnn
            _ = W env a * (ε + εlog) ^ 2 * (Va * Vb) := by ring
        have hstepb : ε * (θb * (Va * Vb)) ≤ W env b * (ε + εlog) ^ 2 * (Va * Vb) := by
          calc ε * (θb * (Va * Vb)) ≤ ε * (W env b * (ε + εlog) * (Va * Vb)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hθWb hVaVb_nonneg) hε
            _ ≤ (ε + εlog) * (W env b * (ε + εlog) * (Va * Vb)) := by
                have hnn : (0:ℝ) ≤ W env b * (ε + εlog) * (Va * Vb) :=
                  mul_nonneg (mul_nonneg hWb_nonneg hm0) hVaVb_nonneg
                exact mul_le_mul_of_nonneg_right (by linarith) hnn
            _ = W env b * (ε + εlog) ^ 2 * (Va * Vb) := by ring
        linarith [hstepa, hstepb]
      have hB : (1 + ε) * (Cb * (ε + εlog) ^ 2 * (Va * Vb) + Ca * (ε + εlog) ^ 2 * (Va * Vb)) ≤
          2 * (Ca + Cb) * (ε + εlog) ^ 2 * (Va * Vb) := by
        have h2ε : (1:ℝ) + ε ≤ 2 := by linarith
        have hnn : (0:ℝ) ≤ Cb * (ε + εlog) ^ 2 * (Va * Vb) + Ca * (ε + εlog) ^ 2 * (Va * Vb) :=
          add_nonneg (mul_nonneg (mul_nonneg hCb_nonneg hsqnonneg) hVaVb_nonneg)
            (mul_nonneg (mul_nonneg hCa_nonneg hsqnonneg) hVaVb_nonneg)
        linarith [mul_le_mul_of_nonneg_right h2ε hnn]
      have hC : (1 + ε) * ((θa + Ca * (ε + εlog) ^ 2) * Va * ((θb + Cb * (ε + εlog) ^ 2) * Vb)) ≤
          2 * (W env a + Ca) * (W env b + Cb) * (ε + εlog) ^ 2 * (Va * Vb) := by
        have hfa : θa + Ca * (ε + εlog) ^ 2 ≤ (W env a + Ca) * (ε + εlog) := by
          have hmm : (ε + εlog) ^ 2 ≤ (ε + εlog) * 1 := by nlinarith [hsqnonneg]
          nlinarith [hθWa, mul_le_mul_of_nonneg_left hmm hCa_nonneg]
        have hfb : θb + Cb * (ε + εlog) ^ 2 ≤ (W env b + Cb) * (ε + εlog) := by
          have hmm : (ε + εlog) ^ 2 ≤ (ε + εlog) * 1 := by nlinarith [hsqnonneg]
          nlinarith [hθWb, mul_le_mul_of_nonneg_left hmm hCb_nonneg]
        have hfa_nonneg : (0:ℝ) ≤ θa + Ca * (ε + εlog) ^ 2 := by linarith
        have hfb_nonneg : (0:ℝ) ≤ θb + Cb * (ε + εlog) ^ 2 := by linarith
        have hprod : (θa + Ca * (ε + εlog) ^ 2) * (θb + Cb * (ε + εlog) ^ 2) ≤
            (W env a + Ca) * (ε + εlog) * ((W env b + Cb) * (ε + εlog)) :=
          mul_le_mul hfa hfb hfb_nonneg (by nlinarith [hWa_nonneg, hCa_nonneg])
        have h2ε : (1:ℝ) + ε ≤ 2 := by linarith
        have hprod_nonneg : (0:ℝ) ≤
            (W env a + Ca) * (ε + εlog) * ((W env b + Cb) * (ε + εlog)) := by
          have hWCa_nonneg : (0:ℝ) ≤ W env a + Ca := by linarith
          have hWCb_nonneg : (0:ℝ) ≤ W env b + Cb := by linarith
          exact mul_nonneg (mul_nonneg hWCa_nonneg hm0) (mul_nonneg hWCb_nonneg hm0)
        calc (1 + ε) * ((θa + Ca * (ε + εlog) ^ 2) * Va * ((θb + Cb * (ε + εlog) ^ 2) * Vb))
            = (1 + ε) * ((θa + Ca * (ε + εlog) ^ 2) * (θb + Cb * (ε + εlog) ^ 2)) * (Va * Vb) := by
              ring
          _ ≤ 2 * ((W env a + Ca) * (ε + εlog) * ((W env b + Cb) * (ε + εlog))) * (Va * Vb) := by
              have hstep : (1 + ε) * ((θa + Ca * (ε + εlog) ^ 2) * (θb + Cb * (ε + εlog) ^ 2)) ≤
                  2 * ((W env a + Ca) * (ε + εlog) * ((W env b + Cb) * (ε + εlog))) := by
                calc (1 + ε) * ((θa + Ca * (ε + εlog) ^ 2) * (θb + Cb * (ε + εlog) ^ 2))
                    ≤ 2 * ((θa + Ca * (ε + εlog) ^ 2) * (θb + Cb * (ε + εlog) ^ 2)) := by
                      have hprodnn2 : (0:ℝ) ≤
                          (θa + Ca * (ε + εlog) ^ 2) * (θb + Cb * (ε + εlog) ^ 2) :=
                        mul_nonneg hfa_nonneg hfb_nonneg
                      exact mul_le_mul_of_nonneg_right h2ε hprodnn2
                  _ ≤ 2 * ((W env a + Ca) * (ε + εlog) * ((W env b + Cb) * (ε + εlog))) := by
                      linarith [hprod]
              exact mul_le_mul_of_nonneg_right hstep hVaVb_nonneg
          _ = 2 * (W env a + Ca) * (W env b + Cb) * (ε + εlog) ^ 2 * (Va * Vb) := by ring
      rw [abs_le]
      constructor <;> linarith [hΔ2'.1, hΔ2'.2, hA, hB, hC]
  | div a b iha ihb =>
      intro ⟨hpa, hpb⟩ ⟨hla, hlb⟩ ⟨hsa, hsb, hsmall⟩
      have hVa := Positive.eval_pos hpa
      have hVb := Positive.eval_pos hpb
      have hm0 : (0:ℝ) ≤ ε + εlog := by linarith
      have hea := iha hpa hla hsa
      have heb := ihb hpb hlb hsb
      rw [abs_of_pos hVa] at hea
      rw [abs_of_pos hVb] at heb
      have hVaVb_pos : (0:ℝ) < eval env a / eval env b := div_pos hVa hVb
      show |evalRnd rnd rndLog env (Expr.div a b) - eval env (Expr.div a b)| ≤
          (errBound ε εlog env (Expr.div a b) + C env (Expr.div a b) * (ε + εlog) ^ 2) *
            |eval env (Expr.div a b)|
      have heval : eval env (Expr.div a b) = eval env a / eval env b := rfl
      have hrndeval : evalRnd rnd rndLog env (Expr.div a b) =
          rnd (evalRnd rnd rndLog env a / evalRnd rnd rndLog env b) := rfl
      rw [heval, hrndeval, abs_of_pos hVaVb_pos]
      simp only [errBound, C]
      set Ra := evalRnd rnd rndLog env a
      set Rb := evalRnd rnd rndLog env b
      set Va := eval env a
      set Vb := eval env b
      set θa := errBound ε εlog env a
      set θb := errBound ε εlog env b
      set Ca := C env a
      set Cb := C env b
      have hWa_nonneg := W_nonneg env hpa hla
      have hWb_nonneg := W_nonneg env hpb hlb
      have hθWa := errBound_le_W_mul hε hεlog env a hpa hla
      have hθWb := errBound_le_W_mul hε hεlog env b hpb hlb
      have hCa_nonneg : (0:ℝ) ≤ Ca := C_nonneg env a hpa hla
      have hCb_nonneg : (0:ℝ) ≤ Cb := C_nonneg env b hpb hlb
      have hθa_nonneg : (0:ℝ) ≤ θa := errBound_nonneg hε hεlog env a hpa hla
      have hθb_nonneg : (0:ℝ) ≤ θb := errBound_nonneg hε hεlog env b hpb hlb
      have hsqnonneg : (0:ℝ) ≤ (ε + εlog) ^ 2 := sq_nonneg _
      have hBa_nonneg : (0:ℝ) ≤ θa + Ca * (ε + εlog) ^ 2 :=
        add_nonneg hθa_nonneg (mul_nonneg hCa_nonneg hsqnonneg)
      have hBb_nonneg : (0:ℝ) ≤ θb + Cb * (ε + εlog) ^ 2 :=
        add_nonneg hθb_nonneg (mul_nonneg hCb_nonneg hsqnonneg)
      -- Fold the accumulated child bounds into single *opaque* names (the `mul`
      -- case's `Δbig` trick, sharpened by `clear_value` so that `linarith`'s
      -- preprocessing cannot re-expand them): every statement below then stays
      -- short, which is what keeps `linarith`/`nlinarith` fast here.
      set Ba := θa + Ca * (ε + εlog) ^ 2 with hBa_def
      set Bb := θb + Cb * (ε + εlog) ^ 2 with hBb_def
      clear_value Ba Bb
      -- The relative errors `δa`, `δb` of `a`, `b`.
      set δa := (Ra - Va) / Va with hδa_def
      set δb := (Rb - Vb) / Vb with hδb_def
      have hδa_abs : |δa| ≤ Ba := by
        rw [hδa_def, abs_div, abs_of_pos hVa, div_le_iff₀ hVa]; linarith [hea]
      have hδb_abs : |δb| ≤ Bb := by
        rw [hδb_def, abs_div, abs_of_pos hVb, div_le_iff₀ hVb]; linarith [heb]
      have hδa_abs' := abs_le.mp hδa_abs
      have hδb_abs' := abs_le.mp hδb_abs
      have hRa_eq : Va * (1 + δa) = Ra := by rw [hδa_def]; field_simp
      have hRb_eq : Vb * (1 + δb) = Rb := by rw [hδb_def]; field_simp
      -- `Rb`'s error stays below `1/2` (`ErrSmall`), so `1+δb` stays positive
      -- and comfortably clear of `0`.
      have h1db_ge_half : (1:ℝ) / 2 ≤ 1 + δb := by linarith [hδb_abs'.1, hsmall]
      have h1db_pos : (0:ℝ) < 1 + δb := by linarith
      have hinv_le_2 : (1:ℝ) / (1 + δb) ≤ 2 := by
        rw [div_le_iff₀ h1db_pos]; linarith
      have hinv_pos : (0:ℝ) < 1 / (1 + δb) := by positivity
      -- `Ra/Rb = (Va/Vb)·(1+δa)/(1+δb)`.
      have hRaRb_eq : Ra / Rb = (Va / Vb) * ((1 + δa) / (1 + δb)) := by
        rw [← hRa_eq, ← hRb_eq]
        have hVb_ne : Vb ≠ 0 := hVb.ne'
        have h1db_ne : (1 + δb) ≠ 0 := h1db_pos.ne'
        field_simp
      -- The exact first-order remainder identity.
      have hrem_eq : (1 + δa) / (1 + δb) - 1 - (δa - δb) = -((δa - δb) * δb) / (1 + δb) := by
        have h1db_ne : (1 + δb) ≠ 0 := h1db_pos.ne'
        field_simp
        ring
      have hδab_abs : |δa - δb| ≤ Ba + Bb := by
        rw [abs_le]
        constructor <;> linarith [hδa_abs'.1, hδa_abs'.2, hδb_abs'.1, hδb_abs'.2]
      have hprod_le : |δa - δb| * |δb| ≤ (Ba + Bb) * Bb :=
        mul_le_mul hδab_abs hδb_abs (abs_nonneg _) (by linarith)
      have hK_nonneg : (0:ℝ) ≤ (Ba + Bb) * Bb := mul_nonneg (by linarith) hBb_nonneg
      -- The unrounded division bound.
      have hrem_bound : |(1 + δa) / (1 + δb) - 1 - (δa - δb)| ≤ 2 * ((Ba + Bb) * Bb) := by
        rw [hrem_eq, abs_div, abs_neg, abs_mul, abs_of_pos h1db_pos, div_le_iff₀ h1db_pos]
        nlinarith [hprod_le, hK_nonneg, h1db_ge_half]
      have hDivBound : |Ra / Rb - Va / Vb| ≤
          (Va / Vb) * ((Ba + Bb) + 2 * ((Ba + Bb) * Bb)) := by
        have hstep : Ra / Rb - Va / Vb =
            (Va / Vb) * ((δa - δb) + ((1 + δa) / (1 + δb) - 1 - (δa - δb))) := by
          rw [hRaRb_eq]; ring
        rw [hstep, abs_mul, abs_of_pos hVaVb_pos]
        have hrem_bound' := abs_le.mp hrem_bound
        have hδab_abs' := abs_le.mp hδab_abs
        refine mul_le_mul_of_nonneg_left ?_ hVaVb_pos.le
        rw [abs_le]
        constructor <;>
          linarith [hrem_bound'.1, hrem_bound'.2, hδab_abs'.1, hδab_abs'.2]
      -- Rounding step at the division node, then domination of the genuinely
      -- `O(ε²)` pieces into `C (div a b)`.
      set S := Ba + Bb + 2 * ((Ba + Bb) * Bb) with hS_def
      clear_value S
      have hDivBound' := abs_le.mp hDivBound
      have hQabs : |Ra / Rb| ≤ (Va / Vb) + (Va / Vb) * S := by
        rw [abs_le]; constructor <;> linarith [hDivBound'.1, hDivBound'.2]
      have hrnd' := abs_le.mp (hrnd (Ra / Rb))
      have hepsQ := mul_le_mul_of_nonneg_left hQabs hε
      have hFull : |rnd (Ra / Rb) - Va / Vb| ≤ (Va / Vb) * (ε + (1 + ε) * S) := by
        rw [abs_le]
        constructor <;> linarith [hrnd'.1, hrnd'.2, hepsQ, hDivBound'.1, hDivBound'.2]
      -- Coefficient-level domination (no `Va/Vb` factor).
      have hmm : (ε + εlog) ^ 2 ≤ (ε + εlog) * 1 := by nlinarith [hm0, hm]
      have hBa_le : Ba ≤ (W env a + Ca) * (ε + εlog) := by
        rw [hBa_def]; nlinarith [hθWa, mul_le_mul_of_nonneg_left hmm hCa_nonneg]
      have hBb_le : Bb ≤ (W env b + Cb) * (ε + εlog) := by
        rw [hBb_def]; nlinarith [hθWb, mul_le_mul_of_nonneg_left hmm hCb_nonneg]
      have h1a : ε * Ba ≤ (W env a + Ca) * (ε + εlog) ^ 2 :=
        calc ε * Ba ≤ (ε + εlog) * Ba := mul_le_mul_of_nonneg_right (by linarith) hBa_nonneg
          _ ≤ (ε + εlog) * ((W env a + Ca) * (ε + εlog)) :=
              mul_le_mul_of_nonneg_left hBa_le hm0
          _ = (W env a + Ca) * (ε + εlog) ^ 2 := by ring
      have h1b : ε * Bb ≤ (W env b + Cb) * (ε + εlog) ^ 2 :=
        calc ε * Bb ≤ (ε + εlog) * Bb := mul_le_mul_of_nonneg_right (by linarith) hBb_nonneg
          _ ≤ (ε + εlog) * ((W env b + Cb) * (ε + εlog)) :=
              mul_le_mul_of_nonneg_left hBb_le hm0
          _ = (W env b + Cb) * (ε + εlog) ^ 2 := by ring
      have hprodBB : (Ba + Bb) * Bb ≤
          ((W env a + Ca + (W env b + Cb)) * (ε + εlog)) * ((W env b + Cb) * (ε + εlog)) := by
        refine mul_le_mul ?_ hBb_le hBb_nonneg ?_
        · linarith [hBa_le, hBb_le]
        · exact mul_nonneg (by linarith) hm0
      have hprodBB_nonneg : (0:ℝ) ≤ (Ba + Bb) * Bb := mul_nonneg (by linarith) hBb_nonneg
      have h2ε : (1:ℝ) + ε ≤ 2 := by linarith
      have h2P := mul_le_mul_of_nonneg_right h2ε hprodBB_nonneg
      have hBaBb : Ba + Bb = θa + θb + (Ca + Cb) * (ε + εlog) ^ 2 := by
        rw [hBa_def, hBb_def]; ring
      have hCoeff : ε + (1 + ε) * S ≤
          θa + θb + ε +
            (Ca + Cb + (W env a + W env b + Ca + Cb) +
              4 * (W env a + Ca + W env b + Cb) * (W env b + Cb)) * (ε + εlog) ^ 2 := by
        rw [hS_def]
        linarith [h1a, h1b, h2P, hprodBB, hBaBb]
      have hFinal := mul_le_mul_of_nonneg_left hCoeff hVaVb_pos.le
      linarith [hFull, hFinal]
  | sqrt a iha =>
      intro hpa hla ⟨hsa, hsmall⟩
      replace hpa : Positive env a := hpa
      replace hla : ValidLb env a := hla
      have hVa := Positive.eval_pos hpa
      have hea := iha hpa hla hsa
      rw [abs_of_pos hVa] at hea
      have hm0 : (0:ℝ) ≤ ε + εlog := by linarith
      have hsqrtVa_pos : (0:ℝ) < Real.sqrt (eval env a) := Real.sqrt_pos.mpr hVa
      show |evalRnd rnd rndLog env (Expr.sqrt a) - eval env (Expr.sqrt a)| ≤
          (errBound ε εlog env (Expr.sqrt a) + C env (Expr.sqrt a) * (ε + εlog) ^ 2) *
            |eval env (Expr.sqrt a)|
      have heval : eval env (Expr.sqrt a) = Real.sqrt (eval env a) := rfl
      have hrndeval : evalRnd rnd rndLog env (Expr.sqrt a) =
          rnd (Real.sqrt (evalRnd rnd rndLog env a)) := rfl
      rw [heval, hrndeval, abs_of_pos hsqrtVa_pos]
      simp only [errBound, C]
      set Ra := evalRnd rnd rndLog env a
      set Va := eval env a
      set θa := errBound ε εlog env a
      set Ca := C env a
      -- `hea : |Ra - Va| ≤ (θa + Ca*(ε+εlog)^2)*Va`, `hsmall : θa + Ca*(ε+εlog)^2 ≤ 1/2`.
      have hWa_nonneg := W_nonneg env hpa hla
      have hθWa := errBound_le_W_mul hε hεlog env a hpa hla
      have hCa_nonneg : (0:ℝ) ≤ Ca := C_nonneg env a hpa hla
      have hθa_nonneg : (0:ℝ) ≤ θa := errBound_nonneg hε hεlog env a hpa hla
      have hsqnonneg : (0:ℝ) ≤ (ε + εlog) ^ 2 := sq_nonneg _
      have hBa_nonneg : (0:ℝ) ≤ θa + Ca * (ε + εlog) ^ 2 :=
        add_nonneg hθa_nonneg (mul_nonneg hCa_nonneg hsqnonneg)
      -- The relative error `δ` of `a`, and the exact factorization `Ra = Va*(1+δ)`.
      set δ := (Ra - Va) / Va with hδ_def
      have hδ_abs : |δ| ≤ θa + Ca * (ε + εlog) ^ 2 := by
        rw [hδ_def, abs_div, abs_of_pos hVa, div_le_iff₀ hVa]
        linarith [hea]
      have hδ_abs' := abs_le.mp hδ_abs
      have hδ1 : (-1:ℝ) ≤ δ := by linarith [hδ_abs'.1]
      have hRa_eq : Va * (1 + δ) = Ra := by rw [hδ_def]; field_simp
      have hsqrt_eq : Real.sqrt Ra = Real.sqrt Va * Real.sqrt (1 + δ) := by
        rw [← hRa_eq, Real.sqrt_mul hVa.le]
      have hTaylor := abs_sqrt_one_add_sub_one_sub_half_le hδ1
      have hTaylor' := abs_le.mp hTaylor
      -- The unrounded-`sqrt` bound: `|√Ra - √Va - √Va·δ/2| ≤ √Va·δ²/2`.
      have hE1 : |Real.sqrt Ra - Real.sqrt Va| ≤
          Real.sqrt Va * ((θa + Ca * (ε + εlog) ^ 2) / 2 + (θa + Ca * (ε + εlog) ^ 2) ^ 2 / 2) := by
        have hstep : Real.sqrt Ra - Real.sqrt Va =
            Real.sqrt Va * (δ / 2) + Real.sqrt Va * (Real.sqrt (1 + δ) - 1 - δ / 2) := by
          rw [hsqrt_eq]; ring
        rw [hstep, abs_le]
        have hδsq : δ ^ 2 ≤ (θa + Ca * (ε + εlog) ^ 2) ^ 2 := by
          have := abs_le_abs hδ_abs'.2 (by linarith [hδ_abs'.1])
          nlinarith [sq_abs δ, this, hδ_abs]
        constructor <;>
          nlinarith [hTaylor'.1, hTaylor'.2, hδ_abs'.1, hδ_abs'.2, hδsq,
            Real.sqrt_nonneg Va, mul_le_mul_of_nonneg_left hTaylor'.2 (Real.sqrt_nonneg Va),
            mul_le_mul_of_nonneg_left hTaylor'.1 (Real.sqrt_nonneg Va)]
      -- Rounding step.
      have hrnd' := abs_le.mp (hrnd (Real.sqrt Ra))
      have hSabs : |Real.sqrt Ra| ≤ Real.sqrt Va +
          Real.sqrt Va * ((θa + Ca * (ε + εlog) ^ 2) / 2 + (θa + Ca * (ε + εlog) ^ 2) ^ 2 / 2) := by
        have hE1' := abs_le.mp hE1
        rw [abs_le]; constructor <;> linarith [hE1'.1, hE1'.2]
      have hepsRt : ε * |Real.sqrt Ra| ≤
          ε * (Real.sqrt Va +
            Real.sqrt Va * ((θa + Ca * (ε + εlog) ^ 2) / 2 + (θa + Ca * (ε + εlog) ^ 2) ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hSabs hε
      have hE1' := abs_le.mp hE1
      -- Coefficient-level bound (no `√Va` factor): the same "linear domination"
      -- pattern as the `mul`/`div` cases, now for `Ba := θa + Ca·m²`.
      have hBa_le : θa + Ca * (ε + εlog) ^ 2 ≤ (W env a + Ca) * (ε + εlog) := by
        have hmm : (ε + εlog) ^ 2 ≤ (ε + εlog) * 1 := by
          nlinarith [mul_le_mul_of_nonneg_left hm hm0]
        nlinarith [hθWa, mul_le_mul_of_nonneg_left hmm hCa_nonneg]
      have hBa_sq_le : (θa + Ca * (ε + εlog) ^ 2) ^ 2 ≤ (W env a + Ca) ^ 2 * (ε + εlog) ^ 2 := by
        have hWCa_nonneg : (0:ℝ) ≤ W env a + Ca := by linarith
        have hWCam_nonneg : (0:ℝ) ≤ (W env a + Ca) * (ε + εlog) := mul_nonneg hWCa_nonneg hm0
        nlinarith [mul_le_mul hBa_le hBa_le hBa_nonneg hWCam_nonneg]
      have hCoeff : ε + (1 + ε) * ((θa + Ca * (ε + εlog) ^ 2) / 2 +
            (θa + Ca * (ε + εlog) ^ 2) ^ 2 / 2) ≤
          θa / 2 + ε + (2 * (W env a + Ca) ^ 2 + (W env a + Ca) + 1) * (ε + εlog) ^ 2 := by
        have hεθa : ε * θa ≤ W env a * (ε + εlog) ^ 2 := by
          calc ε * θa ≤ ε * (W env a * (ε + εlog)) :=
                mul_le_mul_of_nonneg_left hθWa hε
            _ ≤ (ε + εlog) * (W env a * (ε + εlog)) :=
                mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            _ = W env a * (ε + εlog) ^ 2 := by ring
        have h2ε : (1:ℝ) + ε ≤ 2 := by linarith
        nlinarith [hεθa, hBa_sq_le, mul_le_mul_of_nonneg_right h2ε hCa_nonneg,
          mul_nonneg hCa_nonneg hsqnonneg, sq_nonneg (W env a + Ca)]
      have hCoeff_scaled := mul_le_mul_of_nonneg_left hCoeff (Real.sqrt_nonneg Va)
      rw [abs_le]
      constructor <;> linarith [hrnd'.1, hrnd'.2, hepsRt, hE1'.1, hE1'.2, hCoeff_scaled]
  | log a lb iha =>
      intro ⟨hpa, hlogpos⟩ ⟨hlb0, hlbval, hla⟩ ⟨hsa, hsmall⟩
      have hVa := Positive.eval_pos hpa
      have hm0 : (0:ℝ) ≤ ε + εlog := by linarith
      have hea := iha hpa hla hsa
      rw [abs_of_pos hVa] at hea
      show |evalRnd rnd rndLog env (Expr.log a lb) - eval env (Expr.log a lb)| ≤
          (errBound ε εlog env (Expr.log a lb) + C env (Expr.log a lb) * (ε + εlog) ^ 2) *
            |eval env (Expr.log a lb)|
      have heval : eval env (Expr.log a lb) = Real.log (eval env a) := rfl
      have hrndeval : evalRnd rnd rndLog env (Expr.log a lb) =
          rndLog (Real.log (evalRnd rnd rndLog env a)) := rfl
      rw [heval, hrndeval, abs_of_pos hlogpos]
      simp only [errBound, C]
      set Ra := evalRnd rnd rndLog env a
      set Va := eval env a
      set θa := errBound ε εlog env a
      set Ca := C env a
      have hlbv : lb ≤ Real.log Va := by
        rw [abs_of_pos hlogpos] at hlbval; exact hlbval
      have hWa_nonneg := W_nonneg env hpa hla
      have hθWa := errBound_le_W_mul hε hεlog env a hpa hla
      have hCa_nonneg : (0:ℝ) ≤ Ca := C_nonneg env a hpa hla
      have hθa_nonneg : (0:ℝ) ≤ θa := errBound_nonneg hε hεlog env a hpa hla
      have hsqnonneg : (0:ℝ) ≤ (ε + εlog) ^ 2 := sq_nonneg _
      have hBa_nonneg : (0:ℝ) ≤ θa + Ca * (ε + εlog) ^ 2 :=
        add_nonneg hθa_nonneg (mul_nonneg hCa_nonneg hsqnonneg)
      -- Fold the accumulated child bound into a single opaque name `Ba`.
      set Ba := θa + Ca * (ε + εlog) ^ 2 with hBa_def
      clear_value Ba
      -- The relative error `δ` of the argument, and `Ra = Va·(1+δ)`.
      set δ := (Ra - Va) / Va with hδ_def
      have hδ_abs : |δ| ≤ Ba := by
        rw [hδ_def, abs_div, abs_of_pos hVa, div_le_iff₀ hVa]; linarith [hea]
      have hδ_half : |δ| ≤ 1 / 2 := le_trans hδ_abs hsmall
      have hδ_half' := abs_le.mp hδ_half
      have h1δ_pos : (0:ℝ) < 1 + δ := by linarith [hδ_half'.1]
      have hRa_eq : Va * (1 + δ) = Ra := by rw [hδ_def]; field_simp
      have hlogRa : Real.log Ra = Real.log Va + Real.log (1 + δ) := by
        rw [← hRa_eq, Real.log_mul hVa.ne' h1δ_pos.ne']
      -- `|log Ra - log Va| = |log (1+δ)| ≤ |δ| + 2δ² ≤ Ba + 2·Ba²`.
      have hTaylor := abs_log_one_add_le hδ_half
      have hδsq : δ ^ 2 ≤ Ba ^ 2 := by nlinarith [sq_abs δ, hδ_abs, abs_nonneg δ]
      set T := Ba + 2 * Ba ^ 2 with hT_def
      clear_value T
      have hD1 : |Real.log Ra - Real.log Va| ≤ T := by
        have hsimp : Real.log Ra - Real.log Va = Real.log (1 + δ) := by rw [hlogRa]; ring
        rw [hsimp, hT_def]
        linarith [hTaylor, hδ_abs, hδsq]
      have hD1' := abs_le.mp hD1
      -- Rounding step at the `log` node itself.
      have hlogRa_abs : |Real.log Ra| ≤ Real.log Va + T := by
        rw [abs_le]; constructor <;> linarith [hD1'.1, hD1'.2, hlogpos]
      have hrl := abs_le.mp (hrndLog (Real.log Ra))
      have heps := mul_le_mul_of_nonneg_left hlogRa_abs hεlog
      have hFull : |rndLog (Real.log Ra) - Real.log Va| ≤ εlog * (Real.log Va + T) + T := by
        rw [abs_le]; constructor <;> linarith [hrl.1, hrl.2, heps, hD1'.1, hD1'.2]
      -- Dominate the genuinely-`O(ε²)` pieces by the *absolute*-error constant
      -- `K`; dividing by `lb ≤ log Va` then turns it into the relative one.
      have hmm : (ε + εlog) ^ 2 ≤ (ε + εlog) * 1 := by nlinarith [hm0, hm]
      have hBa_le : Ba ≤ (W env a + Ca) * (ε + εlog) := by
        rw [hBa_def]; nlinarith [hθWa, mul_le_mul_of_nonneg_left hmm hCa_nonneg]
      have hBa_sq_le : Ba ^ 2 ≤ (W env a + Ca) ^ 2 * (ε + εlog) ^ 2 := by
        have hWCam_nonneg : (0:ℝ) ≤ (W env a + Ca) * (ε + εlog) :=
          mul_nonneg (by linarith) hm0
        nlinarith [mul_le_mul hBa_le hBa_le hBa_nonneg hWCam_nonneg]
      have hepsBa : εlog * Ba ≤ (W env a + Ca) * (ε + εlog) ^ 2 :=
        calc εlog * Ba ≤ (ε + εlog) * Ba := mul_le_mul_of_nonneg_right (by linarith) hBa_nonneg
          _ ≤ (ε + εlog) * ((W env a + Ca) * (ε + εlog)) :=
              mul_le_mul_of_nonneg_left hBa_le hm0
          _ = (W env a + Ca) * (ε + εlog) ^ 2 := by ring
      have hεBasq : εlog * Ba ^ 2 ≤ Ba ^ 2 := by
        nlinarith [sq_nonneg Ba, hεlog, hε, hm]
      have hCoeff : εlog * T + T ≤
          θa + (2 * Ca + W env a + 4 * (W env a + Ca) ^ 2) * (ε + εlog) ^ 2 := by
        rw [hT_def]
        linarith [hepsBa, hBa_sq_le, hεBasq, hBa_def]
      have hK_nonneg : (0:ℝ) ≤ 2 * Ca + W env a + 4 * (W env a + Ca) ^ 2 := by
        nlinarith [sq_nonneg (W env a + Ca)]
      have hQ_nonneg : (0:ℝ) ≤
          θa + (2 * Ca + W env a + 4 * (W env a + Ca) ^ 2) * (ε + εlog) ^ 2 :=
        add_nonneg hθa_nonneg (mul_nonneg hK_nonneg hsqnonneg)
      have hscale : θa + (2 * Ca + W env a + 4 * (W env a + Ca) ^ 2) * (ε + εlog) ^ 2 ≤
          (θa / lb + (2 * Ca + W env a + 4 * (W env a + Ca) ^ 2) / lb * (ε + εlog) ^ 2) *
            Real.log Va := by
        have hEq : (θa / lb +
              (2 * Ca + W env a + 4 * (W env a + Ca) ^ 2) / lb * (ε + εlog) ^ 2) * Real.log Va =
            (θa + (2 * Ca + W env a + 4 * (W env a + Ca) ^ 2) * (ε + εlog) ^ 2) *
              Real.log Va / lb := by
          field_simp
        rw [hEq]
        rw [le_div_iff₀ hlb0]
        nlinarith [mul_le_mul_of_nonneg_left hlbv hQ_nonneg]
      linarith [hFull, hCoeff, hscale]

end Expr

end Arlib.Numerics
