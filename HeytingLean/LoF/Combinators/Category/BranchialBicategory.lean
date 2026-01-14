import HeytingLean.LoF.Combinators.Category.BranchialSpan
import HeytingLean.LoF.Combinators.Category.SpanBicategoryType

/-!
# BranchialBicategory — a span/bicategory model for branchial structure (in `Type`)

The “branchial relation” in multiway rewriting is often stated as:

> `t` and `u` are branchially related if they share a common ancestor.

`BranchialSpan.lean` records this as **witness data**:
an ancestor plus two reduction paths.

To support *genuine* span composition (via pullbacks), we also package the branchial relation as an
actual **span in `Type`**, using the bicategory-of-spans construction from
`SpanBicategoryType.lean`.

This is a conservative, “Type-level” substrate:
it does **not** assert that the SKY multiway path category itself has pullbacks.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

namespace Branchial

open SpanType

/-! ## Ancestor objects -/

/-- The type of labeled ancestors of `t`: an ancestor term together with a labeled path to `t`. -/
abbrev LAncestors (t : Comb) : Type :=
  Σ a : Comb, LSteps a t

/-- The “ancestor object” for `t` in the span bicategory of `Type`. -/
def LAncObj (t : Comb) : SpanType.Obj :=
  SpanType.Obj.of (LAncestors t)

/-! ## Common-ancestor span -/

/-- The type of labeled common ancestors of `t` and `u`. -/
abbrev LCommonAncestors (t u : Comb) : Type :=
  Σ a : Comb, LSteps a t × LSteps a u

/-- The canonical span selecting a common labeled ancestor:

`LAncObj t ⟵ LCommonAncestors t u ⟶ LAncObj u`.
-/
def lCommonSpan (t u : Comb) : SpanType.Span (LAncObj t) (LAncObj u) where
  apex := LCommonAncestors t u
  fst := fun x => ⟨x.1, x.2.1⟩
  snd := fun x => ⟨x.1, x.2.2⟩

end Branchial

namespace BranchialSpan

open Branchial

/-- View a `BranchialSpan` witness as a point of the canonical common-ancestor span apex. -/
def toCommonApex {t u : Comb} (s : BranchialSpan t u) : (lCommonSpan t u).apex :=
  ⟨s.ancestor, (s.pathToLeft, s.pathToRight)⟩

/-- Build a `BranchialSpan` witness from a point of the canonical common-ancestor span apex. -/
def ofCommonApex {t u : Comb} (x : (lCommonSpan t u).apex) : BranchialSpan t u :=
  { ancestor := x.1
    pathToLeft := x.2.1
    pathToRight := x.2.2 }

@[simp] theorem ofCommonApex_toCommonApex {t u : Comb} (s : BranchialSpan t u) :
    ofCommonApex (toCommonApex s) = s := by
  cases s
  rfl

@[simp] theorem toCommonApex_ofCommonApex {t u : Comb} (x : (lCommonSpan t u).apex) :
    toCommonApex (ofCommonApex x) = x := by
  cases x
  rfl

/-- `BranchialSpan t u` is equivalent to a point of the canonical common-ancestor span apex. -/
def equivCommonApex (t u : Comb) : BranchialSpan t u ≃ (lCommonSpan t u).apex where
  toFun := toCommonApex
  invFun := ofCommonApex
  left_inv := ofCommonApex_toCommonApex
  right_inv := toCommonApex_ofCommonApex

end BranchialSpan

end Category
end Combinators
end LoF
end HeytingLean
