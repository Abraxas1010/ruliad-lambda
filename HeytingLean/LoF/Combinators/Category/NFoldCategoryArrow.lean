import Mathlib.CategoryTheory.Comma.Arrow
import HeytingLean.LoF.Combinators.Category.CompletionQuotient

/-!
# NFoldCategoryArrow — strict n-fold “hypercube tower” via iterated Arrow categories

This file provides a **paper-faithful strict cubical tower** for Phase A of the
SKY–Heyting–∞-groupoid program, directly mirroring the Arsiwalla et al. (2021)
construction idea:

> i-cells are i-dimensional hypercubes, and (i+1)-cells are (i+1)-hypercubes between them.

In Lean, the simplest strict realization is the **iterated arrow category**:

- `Arrow C` has:
  - objects = morphisms in `C` (1-cells)
  - morphisms = commutative squares in `C` (2-cells)
- `Arrow (Arrow C)` has:
  - objects = squares in `C` (2-cells)
  - morphisms = commutative squares of squares (3-cells / cubes)
- …

We take the base category `M₀` to be the **completion-quotiented** path category `MWQuotObj`
from `CompletionQuotient.lean`.  This makes “commuting squares” strict (equalities in the
quotient), so we can iterate `Arrow` without introducing higher coherence obligations.

Objectivity boundary:
- This file constructs a strict cubical tower. It does **not** claim this is the unique or
  best higher-categorical model of SKY with `Y`, and it does **not** assert any `n→∞` limit.
- Non-thin witness-carrying higher cells are tracked separately (see `Completion2PathBicategory.lean`).
 -/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory

/-- A small “category package” so we can define the tower recursively without relying on
typeclass search for the previous stage while defining the next stage. -/
structure CatPkg where
  Obj : Type _
  inst : CategoryTheory.Category Obj

attribute [instance] CatPkg.inst

/-- The Arsiwalla-style tower `M₀, M₁, …` as an explicit recursion:
`M₀` is `MWQuotObj`, and `M_{n+1}` is the arrow category of `Mₙ`. -/
def MWCatPkg : Nat → CatPkg
  | 0 => { Obj := MWQuotObj, inst := by infer_instance }
  | Nat.succ n =>
      let C := MWCatPkg n
      letI : CategoryTheory.Category C.Obj := C.inst
      { Obj := CategoryTheory.Arrow C.Obj, inst := by infer_instance }

/-- The underlying type of objects at level `n` (i-cells). -/
abbrev MWCat (n : Nat) : Type _ := (MWCatPkg n).Obj

instance (n : Nat) : CategoryTheory.Category (MWCat n) :=
  (MWCatPkg n).inst

@[simp] theorem MWCat_zero : MWCat 0 = MWQuotObj := rfl
@[simp] theorem MWCat_succ (n : Nat) : MWCat (Nat.succ n) = CategoryTheory.Arrow (MWCat n) := rfl

/-- Source object of an (n+1)-cell (domain of the underlying arrow). -/
abbrev src {n : Nat} (f : MWCat (Nat.succ n)) : MWCat n := f.left

/-- Target object of an (n+1)-cell (codomain of the underlying arrow). -/
abbrev tgt {n : Nat} (f : MWCat (Nat.succ n)) : MWCat n := f.right

/-- The underlying arrow in the previous level category (the “boundary” of the (n+1)-cell). -/
abbrev edge {n : Nat} (f : MWCat (Nat.succ n)) : src f ⟶ tgt f := f.hom

end Category
end Combinators
end LoF
end HeytingLean
