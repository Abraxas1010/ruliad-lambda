import Mathlib.CategoryTheory.PathCategory.Basic
import HeytingLean.LoF.Combinators.Category.BranchialSpan

/-!
# BranchialCategory — a compositional structure on branchial adjacency

In general, composing *spans* requires pullbacks. The SKY multiway path category `MWObj` does not
come with pullbacks, so we do **not** construct the bicategory of spans here.

Instead, we provide an honest fallback: treat `BranchialSpan` witnesses as **edges** in a quiver and
use the path category construction to obtain a category whose morphisms are finite sequences of
branchial edges (i.e. paths in the branchial graph).

This is sufficient to:
- speak about “branchial reachability” (connectedness via branchial adjacency),
- compose branchial evidence by concatenation,
- keep the witness data for each adjacency step.

When a genuine span composition becomes available (e.g. via a pullback story on an appropriate
completion), this file can be revisited.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-- Wrapper object to avoid instance clashes: `Comb` already carries the preorder-category instance. -/
structure BranchialObj where
  term : Comb
deriving DecidableEq, Repr

namespace BranchialObj

def ofTerm (t : Comb) : BranchialObj := ⟨t⟩

@[simp] theorem term_ofTerm (t : Comb) : (BranchialObj.ofTerm t).term = t := rfl

end BranchialObj

instance : Quiver BranchialObj where
  Hom X Y := BranchialSpan X.term Y.term

/-- The category whose morphisms are (finite) paths of branchial adjacency witnesses. -/
abbrev BranchialPathCat : Type :=
  CategoryTheory.Paths BranchialObj

instance : CategoryTheory.Category BranchialPathCat := by
  infer_instance

end Category
end Combinators
end LoF
end HeytingLean

