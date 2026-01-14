import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Data.ULift
import HeytingLean.LoF.Combinators.Category.CompletionHomotopy

/-!
# CompletionBicategory — a bicategory of SKY paths with completion-homotopy 2-cells

We equip the SKY multiway path category `MWObj` with a `CategoryTheory.Bicategory` structure by:

- keeping 1-morphisms as labeled paths `LSteps`, and
- taking 2-morphisms between paths `p q` to be (a lifted) `CompletionHomotopy p q`.

This is a conservative, proof-irrelevant 2-dimensional structure: each hom-category is thin
(`PLift` of a Prop), so all coherence axioms hold automatically.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory

open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-! ## The hom-category on paths: `p ⟶ q` means `CompletionHomotopy p q` -/

instance (a b : MWObj) : Category (a ⟶ b) where
  Hom p q := PLift (CompletionHomotopy p q)
  id p := PLift.up (CompletionHomotopy.refl p)
  comp η θ := PLift.up (CompletionHomotopy.trans η.down θ.down)
  id_comp := by
    intro X Y f
    apply Subsingleton.elim
  comp_id := by
    intro X Y f
    apply Subsingleton.elim
  assoc := by
    intro W X Y Z f g h
    apply Subsingleton.elim

/-! ## Bicategory instance on `MWObj` -/

instance : Bicategory MWObj where
  toCategoryStruct := (inferInstance : CategoryStruct MWObj)
  homCategory a b := by infer_instance
  whiskerLeft {a b c} f {g h} η := by
    have η' : PLift (CompletionHomotopy g h) := by
      simpa using η
    exact PLift.up (CompletionHomotopy.whisker_left f η'.down)
  whiskerRight {a b c} {f g} η h := by
    have η' : PLift (CompletionHomotopy f g) := by
      simpa using η
    exact PLift.up (CompletionHomotopy.whisker_right η'.down h)
  associator {a b c d} f g h :=
    eqToIso (LSteps.comp_assoc f g h)
  leftUnitor {a b} f :=
    eqToIso (by rfl)
  rightUnitor {a b} f :=
    eqToIso (LSteps.comp_refl_right f)

/-- The bicategory structure on `MWObj` whose 2-morphisms are completion homotopies. -/
abbrev skyCompletionBicategory : Bicategory MWObj :=
  inferInstance

end Category
end Combinators
end LoF
end HeytingLean
