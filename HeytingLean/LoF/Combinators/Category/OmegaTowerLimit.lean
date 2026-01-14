import Mathlib.CategoryTheory.Comma.Arrow
import HeytingLean.LoF.Combinators.Category.NFoldCategoryArrow

/-!
# OmegaTowerLimit — a minimal ω-limit (inverse limit) interface for the strict Arrow tower

Phase A.4 asks for a Lean formalization of an `n → ∞` limit notion for the strict cubical tower.

Instead of committing to a strong (and likely false) semantic claim like “the SKY+`Y` ∞-groupoid
exists”, we provide a conservative, explicit notion:

- a **tower of categories** `C₀ ← C₁ ← C₂ ← …` given by functors `dropₙ : C_{n+1} ⥤ Cₙ`, and
- its **inverse-limit category** whose objects are compatible families of objects, and whose
  morphisms are compatible families of morphisms.

This is the categorical ω-limit of a diagram of shape `ℕᵒᵖ` once one fixes a canonical projection.
For the strict Arrow tower we provide two natural projections:

- `dropLeftₙ : Arrow(Cₙ) ⥤ Cₙ` (left boundary), and
- `dropRightₙ : Arrow(Cₙ) ⥤ Cₙ` (right boundary).

Objectivity boundary:
- This file is infrastructure only. It does **not** identify this limit with an ∞-groupoid of
  rewrite homotopies; it merely packages a precise ω-limit notion for later comparison.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory

universe u v

/-! ## A tower of categories -/

structure CatTower where
  Obj : Nat → Type u
  inst : ∀ n, Category.{v} (Obj n)
  drop : ∀ n, Obj (n + 1) ⥤ Obj n

attribute [instance] CatTower.inst

/-! ## The inverse-limit category of a tower -/

structure TowerLimit (T : CatTower) where
  obj : ∀ n, T.Obj n
  compat : ∀ n, (T.drop n).obj (obj (n + 1)) = obj n

namespace TowerLimit

@[ext]
theorem ext {T : CatTower} {X Y : TowerLimit T} (h : ∀ n, X.obj n = Y.obj n) : X = Y := by
  cases X with
  | mk objX compatX =>
    cases Y with
    | mk objY compatY =>
      have hObj : objX = objY := by
        funext n
        exact h n
      cases hObj
      have : compatX = compatY := by
        apply Subsingleton.elim
      cases this
      rfl

structure Hom {T : CatTower} (X Y : TowerLimit T) where
  app : ∀ n, X.obj n ⟶ Y.obj n
  /-- Compatibility with the drop functors (with coercions along `X.compat` and `Y.compat`). -/
  comm : ∀ n,
    eqToHom (X.compat n).symm ≫ (T.drop n).map (app (n + 1)) ≫ eqToHom (Y.compat n) = app n

@[ext]
theorem Hom.ext {T : CatTower} {X Y : TowerLimit T} {f g : Hom X Y}
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f with
  | mk appf commf =>
    cases g with
    | mk appg commg =>
      have happ : appf = appg := by
        funext n
        exact h n
      cases happ
      have : commf = commg := by
        apply Subsingleton.elim
      cases this
      rfl

instance {T : CatTower} : Category (TowerLimit T) where
  Hom X Y := Hom X Y
  id X :=
    { app := fun n => 𝟙 (X.obj n)
      comm := by
        intro n
        simp }
  comp {X Y Z} f g :=
    { app := fun n => f.app n ≫ g.app n
      comm := by
        intro n
        -- Push the drop through composition, then use the component commutativity of `f` and `g`,
        -- with the coercions along `X.compat` / `Y.compat` / `Z.compat`.
        simp [Functor.map_comp, Category.assoc]
        have hf :
            eqToHom (X.compat n).symm ≫ (T.drop n).map (f.app (n + 1)) =
              f.app n ≫ eqToHom (Y.compat n).symm := by
          simpa [Category.assoc] using
            congrArg (fun t => t ≫ eqToHom (Y.compat n).symm) (f.comm n)
        have hg :
            f.app n ≫
                (eqToHom (Y.compat n).symm ≫ (T.drop n).map (g.app (n + 1)) ≫ eqToHom (Z.compat n)) =
              f.app n ≫ g.app n := by
          simpa [Category.assoc] using congrArg (fun t => f.app n ≫ t) (g.comm n)
        calc
          eqToHom (X.compat n).symm ≫ (T.drop n).map (f.app (n + 1)) ≫ (T.drop n).map (g.app (n + 1)) ≫
              eqToHom (Z.compat n) =
              (eqToHom (X.compat n).symm ≫ (T.drop n).map (f.app (n + 1))) ≫ (T.drop n).map (g.app (n + 1)) ≫
                eqToHom (Z.compat n) := by
              simp [Category.assoc]
          _ =
              (f.app n ≫ eqToHom (Y.compat n).symm) ≫ (T.drop n).map (g.app (n + 1)) ≫ eqToHom (Z.compat n) := by
              simp [Category.assoc, hf]
          _ =
              f.app n ≫ (eqToHom (Y.compat n).symm ≫ (T.drop n).map (g.app (n + 1)) ≫ eqToHom (Z.compat n)) := by
              simp [Category.assoc]
          _ = f.app n ≫ g.app n := by
              simpa using hg }
  id_comp := by
    intro X Y f
    ext n
    simp
  comp_id := by
    intro X Y f
    ext n
    simp
  assoc := by
    intro W X Y Z f g h
    ext n
    simp [Category.assoc]

/-- Component of the identity morphism in the tower limit category. -/
@[simp] theorem id_app {T : CatTower} (X : TowerLimit T) (n : Nat) :
    ((𝟙 X : X ⟶ X).app n) = 𝟙 (X.obj n) := rfl

/-- Component of composition in the tower limit category. -/
@[simp] theorem comp_app {T : CatTower} {X Y Z : TowerLimit T} (f : X ⟶ Y) (g : Y ⟶ Z) (n : Nat) :
    ((f ≫ g).app n) = f.app n ≫ g.app n := rfl

/-- Evaluation functor from the ω-limit category to level `n`. -/
def eval {T : CatTower} (n : Nat) : (TowerLimit T) ⥤ (T.Obj n) where
  obj X := X.obj n
  map {X Y} f := f.app n
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

end TowerLimit

/-! ## The strict SKY Arrow tower as a category tower -/

/-- One-step projection `MWCat (n+1) ⥤ MWCat n` picking the left boundary. -/
abbrev MWDropLeft (n : Nat) : MWCat (n + 1) ⥤ MWCat n :=
  Arrow.leftFunc (C := MWCat n)

/-- One-step projection `MWCat (n+1) ⥤ MWCat n` picking the right boundary. -/
abbrev MWDropRight (n : Nat) : MWCat (n + 1) ⥤ MWCat n :=
  Arrow.rightFunc (C := MWCat n)

/-- The strict SKY Arrow tower with `drop = Arrow.leftFunc`. -/
def MWLeftTower : CatTower where
  Obj := MWCat
  inst := fun n => by infer_instance
  drop := fun n => MWDropLeft n

/-- The strict SKY Arrow tower with `drop = Arrow.rightFunc`. -/
def MWRightTower : CatTower where
  Obj := MWCat
  inst := fun n => by infer_instance
  drop := fun n => MWDropRight n

end Category
end Combinators
end LoF
end HeytingLean
