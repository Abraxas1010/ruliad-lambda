import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKY

/-!
# Lambda.Syntax — untyped λ-calculus (de Bruijn)

This module defines a small untyped λ-calculus with de Bruijn indices:

* syntax `Term` (`var/app/lam`)
* basic size measures (`nodeCount`, `leafCount`)
* shifting and substitution (`shift`, `subst`, `substTop`)
* a bridge to the existing bracket-abstraction compiler:
  `Term.toNamed : Term → Bracket.Lam Nat` and `Term.compileClosed? : Term → Option Comb`.

The goal is to support “ruliology”-style bounded enumeration and multiway β-reduction
exploration without introducing variable-name hygiene issues.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Lambda

open HeytingLean.LoF

inductive Term where
  | var (idx : Nat)
  | app (f a : Term)
  | lam (body : Term)
deriving DecidableEq, Repr

namespace Term

/-! ## Size measures -/

def nodeCount : Term → Nat
  | .var _ => 1
  | .app f a => 1 + nodeCount f + nodeCount a
  | .lam body => 1 + nodeCount body

def leafCount : Term → Nat
  | .var _ => 1
  | .app f a => leafCount f + leafCount a
  | .lam body => leafCount body

/-! ## Shifting -/

private def shiftIndex (cutoff inc idx : Nat) : Nat :=
  if idx ≥ cutoff then idx + inc else idx

/-- Shift all indices `≥ cutoff` by `inc` (classic de Bruijn weakening). -/
def shift : Term → Nat → Nat → Term
  | .var i, cutoff, inc => .var (shiftIndex cutoff inc i)
  | .app f a, cutoff, inc => .app (shift f cutoff inc) (shift a cutoff inc)
  | .lam body, cutoff, inc => .lam (shift body (cutoff + 1) inc)

@[simp] theorem shift_var_lt (cutoff inc i : Nat) (h : i < cutoff) :
    shift (.var i) cutoff inc = .var i := by
  have : ¬ i ≥ cutoff := Nat.not_le_of_gt h
  simp [shift, shiftIndex, this]

@[simp] theorem shift_var_ge (cutoff inc i : Nat) (h : cutoff ≤ i) :
    shift (.var i) cutoff inc = .var (i + inc) := by
  have : i ≥ cutoff := h
  simp [shift, shiftIndex, this]

private def shiftDownIndex (cutoff dec idx : Nat) : Nat :=
  if idx ≥ cutoff then idx - dec else idx

/-- Shift all indices `≥ cutoff` *down* by `dec`.

This is total (`Nat` subtraction saturates), but intended to be used on well-scoped terms
where underflow does not occur (e.g. `substTop`). -/
def shiftDown : Term → Nat → Nat → Term
  | .var i, cutoff, dec => .var (shiftDownIndex cutoff dec i)
  | .app f a, cutoff, dec => .app (shiftDown f cutoff dec) (shiftDown a cutoff dec)
  | .lam body, cutoff, dec => .lam (shiftDown body (cutoff + 1) dec)

@[simp] theorem shiftDown_var_lt (cutoff dec i : Nat) (h : i < cutoff) :
    shiftDown (.var i) cutoff dec = .var i := by
  have : ¬ i ≥ cutoff := Nat.not_le_of_gt h
  simp [shiftDown, shiftDownIndex, this]

@[simp] theorem shiftDown_var_ge (cutoff dec i : Nat) (h : cutoff ≤ i) :
    shiftDown (.var i) cutoff dec = .var (i - dec) := by
  have : i ≥ cutoff := h
  simp [shiftDown, shiftDownIndex, this]

/-! ## Substitution -/

/-- Capture-avoiding substitution on de Bruijn indices.

`subst s j t` replaces free occurrences of index `j` in `t` by `s`.
-/
def subst (s : Term) : Nat → Term → Term
  | j, .var k => if k = j then s else .var k
  | j, .app f a => .app (subst s j f) (subst s j a)
  | j, .lam body => .lam (subst (shift s 0 1) (j + 1) body)

/-- Top-level β-substitution: substitute `arg` for index `0` in `body`,
then drop one binder level. -/
def substTop (arg body : Term) : Term :=
  shiftDown (subst (shift arg 0 1) 0 body) 0 1

/-! ## Closedness (well-scopedness) -/

def closedAt : Nat → Term → Prop
  | n, .var i => i < n
  | n, .app f a => closedAt n f ∧ closedAt n a
  | n, .lam body => closedAt (n + 1) body

def Closed (t : Term) : Prop :=
  closedAt 0 t

private def closedAtDec : (n : Nat) → (t : Term) → Decidable (closedAt n t)
  | n, .var i =>
      show Decidable (i < n) by infer_instance
  | n, .app f a =>
      match closedAtDec n f, closedAtDec n a with
      | isTrue hf, isTrue ha => isTrue ⟨hf, ha⟩
      | isFalse hf, _ => isFalse (fun h => hf h.1)
      | _, isFalse ha => isFalse (fun h => ha h.2)
  | n, .lam body =>
      closedAtDec (n + 1) body

instance (n : Nat) (t : Term) : Decidable (closedAt n t) :=
  closedAtDec n t

instance (t : Term) : Decidable (Closed t) := by
  dsimp [Closed]
  infer_instance

/-! ## Basic lemmas (closedness, shift/subst hygiene) -/

theorem closedAt_mono {t : Term} {n m : Nat} (h : closedAt n t) (hnm : n ≤ m) : closedAt m t := by
  induction t generalizing n m with
  | var i =>
      dsimp [closedAt] at h ⊢
      exact Nat.lt_of_lt_of_le h hnm
  | app f a ihf iha =>
      rcases h with ⟨hf, ha⟩
      exact ⟨ihf hf hnm, iha ha hnm⟩
  | lam body ih =>
      simpa [closedAt] using ih (n := n + 1) (m := m + 1) h (Nat.succ_le_succ hnm)

theorem shift_eq_of_closedAt {t : Term} {cutoff inc : Nat} (h : closedAt cutoff t) :
    shift t cutoff inc = t := by
  induction t generalizing cutoff with
  | var i =>
      dsimp [closedAt] at h
      dsimp [shift, shiftIndex]
      have : ¬i ≥ cutoff := Nat.not_le_of_gt h
      simp [this]
  | app f a ihf iha =>
      rcases h with ⟨hf, ha⟩
      simp [shift, ihf hf, iha ha]
  | lam body ih =>
      simpa [shift, closedAt] using congrArg Term.lam (ih (cutoff := cutoff + 1) (by simpa [closedAt] using h))

theorem shiftDown_eq_of_closedAt {t : Term} {cutoff dec : Nat} (h : closedAt cutoff t) :
    shiftDown t cutoff dec = t := by
  induction t generalizing cutoff with
  | var i =>
      dsimp [closedAt] at h
      dsimp [shiftDown, shiftDownIndex]
      have : ¬i ≥ cutoff := Nat.not_le_of_gt h
      simp [this]
  | app f a ihf iha =>
      rcases h with ⟨hf, ha⟩
      simp [shiftDown, ihf hf, iha ha]
  | lam body ih =>
      simpa [shiftDown, closedAt] using
        congrArg Term.lam (ih (cutoff := cutoff + 1) (by simpa [closedAt] using h))

theorem subst_eq_of_closedAt {t : Term} (s : Term) {j : Nat} (h : closedAt j t) :
    subst s j t = t := by
  induction t generalizing j s with
  | var k =>
      dsimp [closedAt] at h
      have hk : k ≠ j := Nat.ne_of_lt h
      simp [subst, hk]
  | app f a ihf iha =>
      rcases h with ⟨hf, ha⟩
      simp [subst, ihf (s := s) (h := hf), iha (s := s) (h := ha)]
  | lam body ih =>
      have h' : subst (shift s 0 1) (j + 1) body = body :=
        ih (s := shift s 0 1) (j := j + 1) (by simpa [closedAt] using h)
      simpa [subst, closedAt] using congrArg Term.lam h'

theorem substTop_eq_of_closed {t arg : Term} (h : Closed t) : substTop arg t = t := by
  have hsub : subst (shift arg 0 1) 0 t = t := subst_eq_of_closedAt (s := shift arg 0 1) (j := 0) h
  have hsd : shiftDown t 0 1 = t := shiftDown_eq_of_closedAt (t := t) (cutoff := 0) (dec := 1) h
  simp [substTop, hsub, hsd]

/-! ## Bridge: de Bruijn λ → named λ (for bracket abstraction) -/

open Bracket

private def toNamedAux (env : List Nat) : Term → Bracket.Lam Nat
  | .var i =>
      match env[i]? with
      | some x => .var x
      | none => .var (env.length + i)
  | .app f a => .app (toNamedAux env f) (toNamedAux env a)
  | .lam body =>
      let x := env.length
      .lam x (toNamedAux (x :: env) body)

/-- Convert a de Bruijn term into a named term over `Nat` variable names. -/
def toNamed (t : Term) : Bracket.Lam Nat :=
  toNamedAux [] t

/-- Compile a (possibly open) de Bruijn term to SKY, returning `none` if free variables remain. -/
def compileClosed? (t : Term) : Option Comb :=
  Bracket.Lam.compileClosed? (Var := Nat) (toNamed t)

theorem compileClosed?_app (f a : Term) :
    compileClosed? (.app f a) =
      match compileClosed? f, compileClosed? a with
      | some cf, some ca => some (Comb.app cf ca)
      | _, _ => none := by
  simp [compileClosed?, toNamed, toNamedAux, Bracket.Lam.compileClosed?, Bracket.Lam.compile, Bracket.CExp.erase?]
  rfl

/-! ## Bridge: SKY → de Bruijn λ (standard encodings) -/

def KEnc : Term :=
  .lam (.lam (.var 1))

def SEnc : Term :=
  .lam <| .lam <| .lam <|
    .app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0))

def YEnc : Term :=
  .lam <|
    let inner : Term := .app (.var 1) (.app (.var 0) (.var 0))
    .app (.lam inner) (.lam inner)

def ofComb : Comb → Term
  | .K => KEnc
  | .S => SEnc
  | .Y => YEnc
  | .app f a => .app (ofComb f) (ofComb a)

theorem closed_KEnc : Closed KEnc := by
  simp [KEnc, Closed, closedAt]

theorem closed_SEnc : Closed SEnc := by
  simp [SEnc, Closed, closedAt]

theorem closed_YEnc : Closed YEnc := by
  simp [YEnc, Closed, closedAt]

theorem closed_ofComb : ∀ c : Comb, Closed (ofComb c)
  | .K => closed_KEnc
  | .S => closed_SEnc
  | .Y => closed_YEnc
  | .app f a => by
      simpa [ofComb, Closed, closedAt] using And.intro (closed_ofComb f) (closed_ofComb a)

end Term

end Lambda
end Combinators
end LoF
end HeytingLean
