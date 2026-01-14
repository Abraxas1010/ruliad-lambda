import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.ComposableArrows
import Mathlib.CategoryTheory.Square
import HeytingLean.LoF.Combinators.Category.NFoldCategoryArrow

/-!
# NFoldCategoryArsiwalla — Arsiwalla-style structure maps for the Arrow tower

Arsiwalla et al. define strict 2-fold categories (double categories) as **internal categories in**
`Cat`, and strict n-fold categories by iterating this viewpoint. In particular, for a strict
3-fold category they describe a tower of categories `𝒟₀, 𝒟₁, 𝒟₂` where:

- objects are objects of `𝒟₀`,
- vertical arrows are morphisms of `𝒟₀`,
- horizontal arrows are objects of `𝒟₁`,
- squares are morphisms of `𝒟₁`,
- “horizontal squares” are objects of `𝒟₂`,
- cubes are morphisms of `𝒟₂`.

Mathlib does not currently ship a dedicated `InternalCategory` record in `Cat`, but it provides
the canonical strict “cube tower” primitives:

- `Arrow C` whose objects are arrows of `C` and morphisms are commutative squares, and
- `ComposableArrows C 2` (chains `X₀ ⟶ X₁ ⟶ X₂`) which is a convenient concrete model of
  “composable horizontal arrows”.

This file packages the two canonical structure maps used repeatedly in the Arsiwalla tower:

1. `idArrow : C ⥤ Arrow C` sending `X` to `𝟙 X`, and
2. `compArrow : ComposableArrows C 2 ⥤ Arrow C` sending a 2-chain to its composite arrow.

We then specialize these functors to the SKY completion-quotiented tower `MWCat n` from
`NFoldCategoryArrow.lean`.

Objectivity boundary:
- This is a **strict** tower driven by `Arrow`/commutative-squares. It is intended as the
  paper-faithful strict cubical infrastructure. Witness-carrying completion 2- and 3-cells live in
  the separate “completion” track.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory

universe u v

/-! ## Generic `Arrow`-tower structure maps -/

/-- The canonical morphism `(0 : Fin 3) ⟶ (2 : Fin 3)` used to extract the composite
arrow from a 2-chain `X₀ ⟶ X₁ ⟶ X₂`. -/
def hom02 : (0 : Fin 3) ⟶ (2 : Fin 3) :=
  homOfLE (by decide : (0 : Fin 3) ≤ 2)

/-- Arsiwalla-style strict 2-fold category data specialized to the canonical `Arrow` construction.

This is the “internal category in `Cat`” presentation, restricted to the case where the arrow
category is literally `Arrow C` and composable pairs are modeled by `ComposableArrows C 2`. -/
structure Arsiwalla2Fold (C : Type u) [Category.{v} C] where
  /-- Source/left boundary of a horizontal arrow. -/
  src : Arrow C ⥤ C
  /-- Target/right boundary of a horizontal arrow. -/
  tgt : Arrow C ⥤ C
  /-- Identity horizontal arrow. -/
  id : C ⥤ Arrow C
  /-- Composition of composable horizontal arrows. -/
  comp : ComposableArrows C 2 ⥤ Arrow C

/-- The identity embedding `C ⥤ Arrow C`, sending `X` to `𝟙 X`. -/
def idArrow {C : Type u} [Category.{v} C] : C ⥤ Arrow C where
  obj X := Arrow.mk (𝟙 X)
  map {X Y} f :=
    Arrow.homMk' (u := f) (v := f) (by simp)
  map_id := by
    intro X
    ext <;> simp
  map_comp := by
    intro X Y Z f g
    ext <;> simp

/-- Compose a composable 2-chain into a single arrow, packaged as an object of `Arrow C`. -/
def compArrow {C : Type u} [Category.{v} C] : ComposableArrows C 2 ⥤ Arrow C where
  obj F := Arrow.mk (F.map hom02)
  map {F G} φ :=
    Arrow.homMk'
      (u := φ.app 0)
      (v := φ.app 2)
      (w := by
        have h := φ.naturality hom02
        exact h.symm)
  map_id := by
    intro F
    ext <;> simp [hom02]
  map_comp := by
    intro F G H φ ψ
    ext <;> simp [hom02]

namespace Arsiwalla2Fold

/-- The canonical strict 2-fold category data on a category `C`, built from `Arrow C`. -/
def ofCategory (C : Type u) [Category.{v} C] : Arsiwalla2Fold C where
  src := Arrow.leftFunc
  tgt := Arrow.rightFunc
  id := idArrow (C := C)
  comp := compArrow (C := C)

end Arsiwalla2Fold

/-! ## Specialization to the SKY `MWCat` tower -/

/-- Arsiwalla “identity horizontal arrow” map at level `n` in the SKY tower:
`MWCat n ⥤ MWCat (n+1)` is definitionally `MWCat n ⥤ Arrow (MWCat n)`. -/
abbrev MWIdArrow (n : Nat) : MWCat n ⥤ MWCat (Nat.succ n) :=
  idArrow (C := MWCat n)

/-- Arsiwalla “compose composable horizontals” map at level `n` in the SKY tower:
`ComposableArrows (MWCat n) 2 ⥤ MWCat (n+1)` is definitionally `… ⥤ Arrow (MWCat n)`. -/
abbrev MWCompArrow (n : Nat) : ComposableArrows (MWCat n) 2 ⥤ MWCat (Nat.succ n) :=
  compArrow (C := MWCat n)

/-- The canonical Arsiwalla strict 2-fold structure at level `n` of the SKY tower. -/
abbrev MWArsiwalla2Fold (n : Nat) : Arsiwalla2Fold (MWCat n) :=
  Arsiwalla2Fold.ofCategory (C := MWCat n)

/-! ## The `n=2`/`n=3` “square layer” equivalence (Mathlib reuse) -/

/-- Mathlib equivalence: commutative squares in `MWQuotObj` are the same as arrows in `Arrow (Arrow MWQuotObj)`.

This identifies the “horizontal square” layer described in the Arsiwalla 3-fold presentation
with the strict cubical `Arrow` tower at `MWCat 2`. -/
def squareEquiv_MWCat2 : Square MWQuotObj ≌ MWCat 2 :=
  (Square.arrowArrowEquivalence (C := MWQuotObj))

end Category
end Combinators
end LoF
end HeytingLean
