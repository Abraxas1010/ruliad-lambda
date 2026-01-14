import HeytingLean.LoF.Combinators.Category.BranchialBicategory
import HeytingLean.LoF.Combinators.Category.PathTruncation

/-!
# BranchialBicategoryTrunc — branchial spans with path-insensitive ancestor objects

`BranchialBicategory.lean` packages the branchial “common ancestor” relation as a span in `Type`
using **labeled** multi-step paths:

* `LAncestors t = Σ a, LSteps a t`

This is composition-friendly (pullbacks exist in `Type`), but it is *path-sensitive* at the middle
object.

This file provides a coarser, more “branchial graph”–like alternative by truncating the path
component:

* `LAncestorsTrunc t = Σ a, Trunc (LSteps a t)`

so that only *existence* of a path is remembered, not the path itself.

This remains conservative: we still compose spans in `Type`, and we do not assert any pullback
structure in the actual SKY multiway path category.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

namespace Branchial

open SpanType

/-! ## Truncated ancestor objects -/

/-- Path-insensitive ancestors of `t`: an ancestor together with a truncated labeled path to `t`. -/
abbrev LAncestorsTrunc (t : Comb) : Type :=
  Σ a : Comb, Trunc (LSteps a t)

/-- The path-insensitive “ancestor object” for `t` in the span bicategory of `Type`. -/
def LAncObjTrunc (t : Comb) : SpanType.Obj :=
  SpanType.Obj.of (LAncestorsTrunc t)

/-! ## Truncated common-ancestor span -/

/-- Path-insensitive common ancestors of `t` and `u`. -/
abbrev LCommonAncestorsTrunc (t u : Comb) : Type :=
  Σ a : Comb, Trunc (LSteps a t) × Trunc (LSteps a u)

/-- The canonical common-ancestor span on truncated ancestor objects. -/
def lCommonSpanTrunc (t u : Comb) : SpanType.Span (LAncObjTrunc t) (LAncObjTrunc u) where
  apex := LCommonAncestorsTrunc t u
  fst := fun x => ⟨x.1, x.2.1⟩
  snd := fun x => ⟨x.1, x.2.2⟩

/-! ## Relationship to the labeled span (forgetful truncation) -/

/-- Forget explicit labeled common-ancestor data into the truncated version. -/
def truncCommon {t u : Comb} : LCommonAncestors t u → LCommonAncestorsTrunc t u
  | ⟨a, (p, q)⟩ => ⟨a, (Trunc.mk p, Trunc.mk q)⟩

end Branchial

end Category
end Combinators
end LoF
end HeytingLean

