import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.EqToHom
import HeytingLean.LoF.Combinators.Category.CompletionQuotient

/-!
# CompletionQuotientUniversal — universal property of the completion-homotopy quotient

`CompletionQuotient.lean` defines the category `MWQuotObj` whose morphisms are labeled SKY paths
quotiented by `CompletionHomotopy`, together with the quotient functor
`completionQuotientFunctor : MWObj ⥤ MWQuotObj`.

This file proves the expected universal property: any functor out of `MWObj` which respects
completion homotopy factors uniquely through `MWQuotObj`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory

open HeytingLean.LoF
open HeytingLean.LoF.Comb

namespace CompletionHomotopy

universe u v

/-- A functor `F : MWObj ⥤ D` *respects completion homotopy* if it maps completion-homotopic paths
to equal morphisms. -/
def Respects {D : Type u} [Category.{v} D] (F : MWObj ⥤ D) : Prop :=
  ∀ {X Y : MWObj} {p q : X ⟶ Y}, CompletionHomotopy p q → F.map p = F.map q

/-- Lift a functor `MWObj ⥤ D` that respects `CompletionHomotopy` to the quotient category
`MWQuotObj`. -/
def liftFunctor {D : Type u} [Category.{v} D] (F : MWObj ⥤ D) (hF : Respects (D := D) F) :
    MWQuotObj ⥤ D where
  obj X := F.obj ⟨X.term⟩
  map {X Y} f :=
    Quotient.liftOn f
      (fun p => F.map (X := (⟨X.term⟩ : MWObj)) (Y := (⟨Y.term⟩ : MWObj)) p)
      (by
        intro p q h
        exact hF (X := (⟨X.term⟩ : MWObj)) (Y := (⟨Y.term⟩ : MWObj)) (p := p) (q := q) h)
  map_id := by
    intro X
    change
      Quotient.liftOn
          (Quotient.mk (s := (inferInstance : Setoid (LSteps X.term X.term))) (LSteps.refl X.term))
          (fun p => F.map (X := (⟨X.term⟩ : MWObj)) (Y := (⟨X.term⟩ : MWObj)) p)
          (by
            intro p q h
            exact hF (X := (⟨X.term⟩ : MWObj)) (Y := (⟨X.term⟩ : MWObj)) (p := p) (q := q) h) =
        𝟙 (F.obj (⟨X.term⟩ : MWObj))
    simp
    exact F.map_id (X := (⟨X.term⟩ : MWObj))
  map_comp := by
    intro X Y Z f g
    refine Quotient.inductionOn₂ f g ?_
    intro p q
    change
      Quotient.liftOn
          (Quotient.mk (s := (inferInstance : Setoid (LSteps X.term Z.term))) (LSteps.comp p q))
          (fun r => F.map (X := (⟨X.term⟩ : MWObj)) (Y := (⟨Z.term⟩ : MWObj)) r)
          (by
            intro p' q' h
            exact hF (X := (⟨X.term⟩ : MWObj)) (Y := (⟨Z.term⟩ : MWObj)) (p := p') (q := q') h) =
        F.map (X := (⟨X.term⟩ : MWObj)) (Y := (⟨Y.term⟩ : MWObj)) p ≫
          F.map (X := (⟨Y.term⟩ : MWObj)) (Y := (⟨Z.term⟩ : MWObj)) q
    simp
    exact
      F.map_comp
        (X := (⟨X.term⟩ : MWObj))
        (Y := (⟨Y.term⟩ : MWObj))
        (Z := (⟨Z.term⟩ : MWObj))
        p q

/-- The lifted functor factors `F` through `completionQuotientFunctor`. -/
theorem fac {D : Type u} [Category.{v} D] (F : MWObj ⥤ D) (hF : Respects (D := D) F) :
    completionQuotientFunctor ⋙ liftFunctor (D := D) F hF = F := by
  rfl

/-- Uniqueness of the lift through `MWQuotObj`. -/
theorem uniq {D : Type u} [Category.{v} D] (F : MWObj ⥤ D) (hF : Respects (D := D) F)
    (G : MWQuotObj ⥤ D) (hG : completionQuotientFunctor ⋙ G = F) :
    G = liftFunctor (D := D) F hF := by
  have hObj : ∀ X : MWQuotObj, G.obj X = F.obj (⟨X.term⟩ : MWObj) := by
    intro X
    have := CategoryTheory.Functor.congr_obj hG (⟨X.term⟩ : MWObj)
    simpa [completionQuotientFunctor] using this

  refine
    CategoryTheory.Functor.ext
      (F := G)
      (G := liftFunctor (D := D) F hF)
      (fun X => by
        simpa [liftFunctor] using hObj X)
      (fun X Y f => ?_)

  refine Quotient.inductionOn f ?_
  intro p
  have hMap :=
    (CategoryTheory.Functor.congr_hom hG
      (X := (⟨X.term⟩ : MWObj))
      (Y := (⟨Y.term⟩ : MWObj))
      p)
  simpa [completionQuotientFunctor, liftFunctor, hObj] using hMap

end CompletionHomotopy

end Category
end Combinators
end LoF
end HeytingLean
