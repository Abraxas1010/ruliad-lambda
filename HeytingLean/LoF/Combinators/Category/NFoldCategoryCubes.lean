import HeytingLean.LoF.Combinators.Category.NFoldCategoryArsiwalla

/-!
# NFoldCategoryCubes — the strict “cube layer” for the Arrow tower

Mathlib provides `Square C`, the **category of commutative squares** in a category `C`;
morphisms in `Square C` are commuting **cubes** between squares.

In the Arsiwalla strict n-fold picture:
* objects of `C` are 0-cells,
* objects of `Arrow C` are 1-cells,
* morphisms of `Arrow C` are 2-cells (commutative squares),
* objects of `Arrow (Arrow C)` are “horizontal squares”, and
* morphisms of `Arrow (Arrow C)` are 3-cells (commutative cubes).

This file records the reusable identifications at the SKY base category `MWQuotObj`:

* `Square MWQuotObj` packages commuting **cubes** explicitly, and
* `Square MWQuotObj ≌ MWCat 2` is Mathlib’s `Square.arrowArrowEquivalence` instantiated at `MWQuotObj`.

Objectivity boundary:
* This is the **strict cubical** Arrow-tower layer. It does not claim that these cubes arise from
  rewriting completion rules; those live in the explicit completion-cell track.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory

universe u v

/-- The cube layer over the completion-quotiented path category. -/
abbrev MWCubeLayer : Type := Square MWQuotObj

/-- A “cube” between two commutative squares, i.e. a morphism in `Square MWQuotObj`. -/
abbrev MWCube (sq₁ sq₂ : MWCubeLayer) : Type := sq₁ ⟶ sq₂

/-- Mathlib equivalence identifying squares (and cubes) in `MWQuotObj` with the 2nd Arrow layer `MWCat 2`. -/
abbrev squareEquiv_MWCat2' : Square MWQuotObj ≌ MWCat 2 :=
  squareEquiv_MWCat2

end Category
end Combinators
end LoF
end HeytingLean

