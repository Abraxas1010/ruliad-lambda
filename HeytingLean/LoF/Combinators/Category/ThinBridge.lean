import Mathlib.CategoryTheory.Category.Preorder
import HeytingLean.LoF.Combinators.Category.MultiwayCategory
import HeytingLean.LoF.Combinators.Topos.StepsSite

/-!
# ThinBridge — forgetting labels/multiplicity down to reachability

The topos/Grothendieck layer for SKY uses the **thin** reachability category:

* objects: `Comb`
* morphisms: proofs of reachability `Comb.Steps` (a preorder category)

The multiway layer uses a **non-thin** path category:

* objects: `MWObj` (wrapper around `Comb`)
* morphisms: labeled paths `LSteps` (a `Type`, so distinct label sequences are distinct morphisms)

This file provides the bridge functor that forgets labels and collapses all parallel paths to the
unique morphism in the preorder category.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-- Forget labels and path multiplicity: map a labeled path to its reachability proof. -/
def forgetToStepsCat : MWObj ⥤ HeytingLean.LoF.Comb where
  obj X := X.term
  map {X Y} p := CategoryTheory.homOfLE (LSteps.toSteps p)
  map_id := by
    intro X
    -- Target category is a preorder category, so homs are subsingletons.
    apply Subsingleton.elim
  map_comp := by
    intro X Y Z f g
    -- Target category is a preorder category, so homs are subsingletons.
    apply Subsingleton.elim

end Category
end Combinators
end LoF
end HeytingLean

