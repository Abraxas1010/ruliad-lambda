import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
import HeytingLean.LoF.Combinators.Category.MultiwayCategory

/-!
# Groupoid — formal invertibility via the free groupoid on the one-step quiver

For the topos/gluing layer we use the *thin* preorder category on `Comb` (reachability).
For multiway semantics we built a *non-thin* path category on labeled paths (`MWObj`, `LSteps`).

To talk about “formal inverses” (categorical localization / groupoid completion) we use Mathlib’s
`Quiver.FreeGroupoid`: the free groupoid on a quiver.

Here the generating quiver is:
- vertices: SKY terms (wrapped as `MW1Obj`)
- edges: labeled one-step reductions `LStep`

This yields a `Groupoid` where inverses are *formal* (not computational reductions).
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-! ## The one-step quiver -/

/-- Wrapper used to define a `Quiver` whose arrows are *one-step* labeled reductions.

We keep this separate from `MWObj` to avoid instance clashes: `MWObj` already carries a
`Category` structure (with homs = multi-step paths). -/
structure MW1Obj where
  term : Comb
deriving DecidableEq, Repr

namespace MW1Obj

def ofTerm (t : Comb) : MW1Obj := ⟨t⟩

@[simp] theorem term_ofTerm (t : Comb) : (MW1Obj.ofTerm t).term = t := rfl

end MW1Obj

instance : Quiver MW1Obj where
  Hom X Y := LStep X.term Y.term

/-! ## Free groupoid completion -/

/-- The free groupoid on the SKY one-step quiver. -/
abbrev MWFreeGroupoid : Type := Quiver.FreeGroupoid MW1Obj

instance : Groupoid MWFreeGroupoid := by
  infer_instance

/-- Embed a SKY term as an object in the free groupoid. -/
abbrev GObj (t : Comb) : MWFreeGroupoid :=
  (Quiver.FreeGroupoid.of MW1Obj).obj (MW1Obj.ofTerm t)

namespace LStep

/-- View a labeled one-step reduction as a morphism in the free groupoid. -/
def toGroupoid {t u : Comb} (s : LStep t u) : GObj t ⟶ GObj u :=
  (Quiver.FreeGroupoid.of MW1Obj).map (X := MW1Obj.ofTerm t) (Y := MW1Obj.ofTerm u) s

end LStep

namespace LSteps

/-- View a labeled multi-step reduction path as a morphism in the free groupoid. -/
def toGroupoid : {t u : Comb} → LSteps t u → (GObj t ⟶ GObj u)
  | t, _, .refl _ => 𝟙 (GObj t)
  | t, _, .trans s p => (LStep.toGroupoid (t := t) (u := _) s) ≫ toGroupoid p

end LSteps

end Category
end Combinators
end LoF
end HeytingLean

