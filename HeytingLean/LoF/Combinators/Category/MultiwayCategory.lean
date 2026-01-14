import Mathlib.CategoryTheory.Category.Basic
import HeytingLean.LoF.Combinators.SKYMultiway

/-!
# MultiwayCategory — a non-thin path category for SKY rewriting

The topos/gluing layer treats reachability `Comb.Steps` as a **preorder**, hence a *thin* category.
For multiway semantics we need **multiple distinct morphisms** between the same objects
(different redex choices / labels), so we introduce a separate wrapper category:

- objects: `MWObj` (a wrapper around `Comb`)
- morphisms: explicit *labeled* multi-step paths `LSteps` built from enumerated one-step events
  (`Comb.stepEdges` from `SKYMultiway`)

This intentionally does **not** install a global `Category Comb` instance to avoid clashing with the
preorder-derived category instance used by `Topos/StepsSite.lean`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-! ## Objects -/

/-- Wrapper for SKY terms when we want a non-thin category of *paths*. -/
structure MWObj where
  term : Comb
deriving DecidableEq, Repr

namespace MWObj

@[simp] theorem eta (X : MWObj) : MWObj.mk X.term = X := by
  cases X
  rfl

end MWObj

/-! ## One-step labeled edges -/

/-- A labeled one-step edge `t ⟶ u`, where the label is the event data from
`Comb.stepEdges` (rule tag + redex path). -/
structure LStep (t u : Comb) where
  ed : EventData
  mem : (ed, u) ∈ Comb.stepEdges t

namespace LStep

/-- Forget the label: any labeled step is a propositional `Comb.Step`. -/
theorem toStep {t u : Comb} (s : LStep t u) : Comb.Step t u :=
  Comb.stepEdges_sound (t := t) (ed := s.ed) (u := u) s.mem

end LStep

/-! ## Multi-step labeled paths -/

/-- Labeled multi-step paths, as a `Type` (so distinct label sequences are distinct morphisms). -/
inductive LSteps : Comb → Comb → Type where
  | refl (t : Comb) : LSteps t t
  | trans {t u v : Comb} : LStep t u → LSteps u v → LSteps t v

namespace LSteps

/-- Path length (number of one-step edges). -/
def length : {t u : Comb} → LSteps t u → Nat
  | _, _, .refl _ => 0
  | _, _, .trans _ p => length p + 1

/-- Concatenate paths (`p` then `q`). -/
def comp : {t u v : Comb} → LSteps t u → LSteps u v → LSteps t v
  | _, _, _, .refl _, q => q
  | _, _, _, .trans s p, q => .trans s (comp p q)

@[simp] theorem comp_refl_left {t u : Comb} (p : LSteps t u) :
    comp (.refl t) p = p := by
  rfl

@[simp] theorem comp_refl_right {t u : Comb} (p : LSteps t u) :
    comp p (.refl u) = p := by
  induction p with
  | refl t =>
      rfl
  | trans s p ih =>
      simp [comp, ih]

theorem comp_assoc {t u v w : Comb} (p : LSteps t u) (q : LSteps u v) (r : LSteps v w) :
    comp (comp p q) r = comp p (comp q r) := by
  induction p with
  | refl t =>
      rfl
  | trans s p ih =>
      simp [comp, ih]

/-- Length is additive under path concatenation. -/
theorem length_comp {t u v : Comb} (p : LSteps t u) (q : LSteps u v) :
    (comp p q).length = p.length + q.length := by
  induction p with
  | refl t =>
      simp [comp, length]
  | trans s p ih =>
      -- `length (s :: p ⋙ q) = length (p ⋙ q) + 1`
      simp [comp, length, ih, Nat.add_assoc, Nat.add_comm]

/-- Casting a path along endpoint equality does not change its length. -/
theorem length_cast {t u v : Comb} (h : u = v) (p : LSteps t u) :
    length (cast (by cases h; rfl) p) = length p := by
  cases h
  rfl

/-- Casting a path along the endpoint-equality induced `LSteps` congruence does not change its length. -/
theorem length_cast_congr {t u v : Comb} (h : u = v) (p : LSteps t u) :
    length (cast (congrArg (fun w => LSteps t w) h) p) = length p := by
  cases h
  rfl

/-- Forget labels: any labeled path induces reachability `Comb.Steps`. -/
def toSteps : {t u : Comb} → LSteps t u → Comb.Steps t u
  | _, _, .refl t => Comb.Steps.refl t
  | _, _, .trans s p => Comb.Steps.trans (s.toStep) (toSteps p)

end LSteps

/-! ## The multiway path category -/

instance : CategoryTheory.Category MWObj where
  Hom X Y := LSteps X.term Y.term
  id X := LSteps.refl X.term
  comp f g := LSteps.comp f g
  id_comp := by
    intro X Y f
    rfl
  comp_id := by
    intro X Y f
    exact (LSteps.comp_refl_right (t := X.term) (u := Y.term) f)
  assoc := by
    intro X Y Z W f g h
    exact (LSteps.comp_assoc (t := X.term) (u := Y.term) (v := Z.term) (w := W.term) f g h)

end Category
end Combinators
end LoF
end HeytingLean
