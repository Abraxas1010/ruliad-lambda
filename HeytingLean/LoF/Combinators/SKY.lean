import HeytingLean.LoF.HoTT.Identity

/-
Minimal SKY combinator layer and rewrite system.

This module provides a tiny, self-contained model of the combinators
`K`, `S`, and `Y` together with a small-step reduction relation.  It is
intended as a combinatorial counterpart to the HoTT/Glue layer: later
phases can relate confluence (Church–Rosser) of this system to RT-1/RT-2
style transport contracts.
-/

namespace HeytingLean
namespace LoF

inductive Comb where
  | K
  | S
  | Y
  | app (f a : Comb)
deriving DecidableEq, Repr

namespace Comb

/-- One-step SK(Y) reduction. This is deliberately minimal and only
captures the core K/S/Y schemata. -/
inductive Step : Comb -> Comb -> Prop where
  | K_rule (x y : Comb) :
      Step (Comb.app (Comb.app .K x) y) x
  | S_rule (x y z : Comb) :
      Step (Comb.app (Comb.app (Comb.app .S x) y) z)
           (Comb.app (Comb.app x z) (Comb.app y z))
  | Y_rule (f : Comb) :
      Step (Comb.app .Y f) (Comb.app f (Comb.app .Y f))
  | app_left {f f' a} :
      Step f f' -> Step (Comb.app f a) (Comb.app f' a)
  | app_right {f a a'} :
      Step a a' -> Step (Comb.app f a) (Comb.app f a')

/-- Multi-step (reflexive transitive closure) of `Step`. -/
inductive Steps : Comb -> Comb -> Prop where
  | refl (t : Comb) : Steps t t
  | trans {t u v} : Step t u -> Steps u v -> Steps t v

/-- Promote definitional equality of terms to the multi-step relation. -/
theorem Steps.of_eq {t u : Comb} (h : t = u) : Steps t u := by
  subst h
  exact Steps.refl _

/-- A term is in normal form if it admits no `Step` successors. -/
def Normal (t : Comb) : Prop :=
  ∀ u : Comb, ¬ Step t u

/-- The combinator `K` is in normal form. -/
theorem K_normal : Normal Comb.K := by
  intro u h
  cases h

/-- The combinator `S` is in normal form. -/
theorem S_normal : Normal Comb.S := by
  intro u h
  cases h

/-- The combinator `Y` is in normal form. -/
theorem Y_normal : Normal Comb.Y := by
  intro u h
  cases h

/-- The combinator `K · S` is in normal form. -/
theorem K_app_S_normal : Normal (Comb.app Comb.K Comb.S) := by
  intro u h
  cases h with
  | app_left h' =>
      -- The function part would need to step, but `K` is normal.
      exact (K_normal _ h')
  | app_right h' =>
      -- The argument would need to step, but `S` is normal.
      exact (S_normal _ h')

/-! ### A derived identity combinator -/

/-- The standard SK combinator encoding of the identity: `I := S K K`. -/
def I : Comb := Comb.app (Comb.app .S .K) .K

/-- One-step reduction from `I` applied to `t` to
`(K` applied to `t)` applied again to `K` and `t`. -/
theorem I_step (t : Comb) :
  Step (Comb.app I t) (Comb.app (Comb.app .K t) (Comb.app .K t)) := by
  -- This is an instance of the S-rule with `x = K`, `y = K`, `z = t`.
  simpa [I] using
    Step.S_rule (x := .K) (y := .K) (z := t)

/-- The term `(K · t) · (K · t)` reduces in one step to `t`. -/
theorem K_app_app_step (t : Comb) :
  Step (Comb.app (Comb.app .K t) (Comb.app .K t)) t := by
  -- Apply the K-rule with arguments `t` and `K · t`.
  simpa using Step.K_rule (x := t) (y := Comb.app .K t)

/-- The SKI encoding of identity: `I` behaves extensionally as the
identity combinator. -/
theorem I_reduces (t : Comb) : Steps (Comb.app I t) t := by
  refine Steps.trans (t := Comb.app I t)
    (u := Comb.app (Comb.app .K t) (Comb.app .K t))
    (v := t) ?h₁ ?h₂
  · exact I_step t
  · refine Steps.trans
      (t := Comb.app (Comb.app .K t) (Comb.app .K t))
      (u := t) (v := t) ?_ (Steps.refl t)
    exact K_app_app_step t

end Comb

end LoF
end HeytingLean
