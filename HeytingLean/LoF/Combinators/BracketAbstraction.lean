import HeytingLean.LoF.Combinators.SKY

/-!
# BracketAbstraction — λ → SKY compilation (Phase 2 scaffold)

This file provides a small *syntactic* bracket abstraction compiler:

* a combinator-expression syntax `CExp Var` that extends SKY with free variables,
* Turner's style abstraction elimination `[x]E`,
* a tiny untyped λ syntax `Lam Var`,
* and a compiler `Lam.compile` into `CExp Var`.

Correctness proofs (β/η simulation, optimization soundness) are planned follow-ups.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

open HeytingLean.LoF

namespace Bracket

/-! ## Combinator expressions with variables -/

inductive CExp (Var : Type) where
  | var (v : Var)
  | K
  | S
  | Y
  | app (f a : CExp Var)
deriving Repr, DecidableEq

namespace CExp

variable {Var : Type}

def I : CExp Var :=
  .app (.app .S .K) .K

def occurs [DecidableEq Var] (x : Var) : CExp Var → Bool
  | .var v => decide (v = x)
  | .K => false
  | .S => false
  | .Y => false
  | .app f a => occurs x f || occurs x a

def opt [DecidableEq Var] : CExp Var → CExp Var
  | .app (.app .S (.app .K e)) (.app .K f) => .app .K (.app e f)
  | .app (.app .S (.app .K e)) a =>
      if a = I then e else .app (.app .S (.app .K e)) a
  | e => e

def bracket [DecidableEq Var] (x : Var) : CExp Var → CExp Var
  | .var v =>
      if v = x then I else .app .K (.var v)
  | .K => .app .K .K
  | .S => .app .K .S
  | .Y => .app .K .Y
  | .app f a =>
      if occurs x f || occurs x a then
        opt (.app (.app .S (bracket x f)) (bracket x a))
      else
        .app .K (.app f a)

def denote (ρ : Var → Comb) : CExp Var → Comb
  | .var v => ρ v
  | .K => .K
  | .S => .S
  | .Y => .Y
  | .app f a => .app (denote ρ f) (denote ρ a)

def erase : CExp PEmpty → Comb
  | .var v => nomatch v
  | .K => .K
  | .S => .S
  | .Y => .Y
  | .app f a => .app (erase f) (erase a)

def erase? : CExp Var → Option Comb
  | .var _ => none
  | .K => some .K
  | .S => some .S
  | .Y => some .Y
  | .app f a =>
      match erase? f, erase? a with
      | some f', some a' => some (.app f' a')
      | _, _ => none

end CExp

/-! ## Untyped lambda terms (named variables) -/

inductive Lam (Var : Type) where
  | var (v : Var)
  | app (f a : Lam Var)
  | lam (x : Var) (body : Lam Var)
  | K
  | S
  | Y
deriving Repr

namespace Lam

variable {Var : Type} [DecidableEq Var]

def compile : Lam Var → CExp Var
  | .var v => .var v
  | .app f a => .app (compile f) (compile a)
  | .lam x body => CExp.bracket x (compile body)
  | .K => .K
  | .S => .S
  | .Y => .Y

def compileClosed? (t : Lam Var) : Option Comb :=
  (compile t).erase?

end Lam

end Bracket
end Combinators
end LoF
end HeytingLean
