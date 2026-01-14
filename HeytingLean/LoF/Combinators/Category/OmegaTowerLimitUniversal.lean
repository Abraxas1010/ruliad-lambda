import Mathlib.CategoryTheory.EqToHom
import HeytingLean.LoF.Combinators.Category.OmegaTowerLimit

/-!
# OmegaTowerLimitUniversal — strict ω-limit universal property for `TowerLimit`

This file complements `OmegaTowerLimit.lean` by proving a strict universal property:

- given a tower of categories `C₀ ← C₁ ← C₂ ← …` (a `CatTower`), and
- a **strict cone** `D ⟶ Cₙ` commuting on-the-nose with the drop functors,

then there is a canonical functor `D ⥤ TowerLimit T` and it is unique among functors
that realize all the projections.

Objectivity boundary:
- This is purely categorical infrastructure about the explicit inverse-limit category.
- It does **not** assert any semantic “∞-groupoid exists” claim for SKY.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory

universe u v

/-- A strict cone over a category tower `T` with apex `D`. -/
structure TowerCone (T : CatTower) (D : Type u) [Category.{v} D] where
  π : ∀ n, D ⥤ T.Obj n
  comm : ∀ n, π (n + 1) ⋙ T.drop n = π n

namespace TowerCone

variable {T : CatTower} {D : Type u} [Category.{v} D]

/-- The canonical functor from a strict cone into the inverse-limit category `TowerLimit T`. -/
def lift (c : TowerCone T D) : D ⥤ TowerLimit T where
  obj d :=
    { obj := fun n => (c.π n).obj d
      compat := by
        intro n
        simpa using (Functor.congr_obj (c.comm n) d) }
  map {X Y} f :=
    { app := fun n => (c.π n).map f
      comm := by
        intro n
        have hEq : c.π (n + 1) ⋙ T.drop n = c.π n := c.comm n
        have hX : (T.drop n).obj ((c.π (n + 1)).obj X) = (c.π n).obj X :=
          Functor.congr_obj hEq X
        have hY : (T.drop n).obj ((c.π (n + 1)).obj Y) = (c.π n).obj Y :=
          Functor.congr_obj hEq Y
        have hHom :
            (T.drop n).map ((c.π (n + 1)).map f) = eqToHom hX ≫ (c.π n).map f ≫ eqToHom hY.symm := by
          simpa [Functor.comp_map] using (Functor.congr_hom hEq f)
        calc
          eqToHom hX.symm ≫ (T.drop n).map ((c.π (n + 1)).map f) ≫ eqToHom hY =
              eqToHom hX.symm ≫ (eqToHom hX ≫ (c.π n).map f ≫ eqToHom hY.symm) ≫ eqToHom hY := by
              simp [hHom, Category.assoc]
          _ = (c.π n).map f := by
              simp [Category.assoc] }
  map_id := by
    intro X
    apply TowerLimit.Hom.ext
    intro n
    change (c.π n).map (𝟙 X) = 𝟙 ((c.π n).obj X)
    simp
  map_comp := by
    intro X Y Z f g
    apply TowerLimit.Hom.ext
    intro n
    change (c.π n).map (f ≫ g) = (c.π n).map f ≫ (c.π n).map g
    simp

/-- `lift` factors each projection functor strictly. -/
theorem lift_fac (c : TowerCone T D) (n : Nat) : (lift c) ⋙ TowerLimit.eval n = c.π n := by
  rfl

/-- Component description of `eqToHom` in the ω-limit category. -/
@[simp] theorem eqToHom_app {X Y : TowerLimit T} (hXY : X = Y) (n : Nat) :
    ((eqToHom hXY : X ⟶ Y).app n) = eqToHom (congrArg (fun Z : TowerLimit T => Z.obj n) hXY) := by
  subst hXY
  rfl

/-- Uniqueness: a functor into `TowerLimit T` is determined by all its projections. -/
theorem lift_uniq (c : TowerCone T D) (F : D ⥤ TowerLimit T)
    (h : ∀ n, F ⋙ TowerLimit.eval n = c.π n) : F = lift c := by
  classical
  have hObj : ∀ d : D, F.obj d = (lift (T := T) (D := D) c).obj d := by
    intro d
    apply TowerLimit.ext
    intro n
    have hn := Functor.congr_obj (h n) d
    simpa [TowerLimit.eval, lift] using hn
  refine CategoryTheory.Functor.ext (F := F) (G := lift (T := T) (D := D) c) hObj ?_
  intro X Y f
  apply TowerLimit.Hom.ext
  intro n
  have hn := Functor.congr_hom (h n) f
  have hn' : (F.map f).app n =
      eqToHom (Functor.congr_obj (h n) X) ≫ (c.π n).map f ≫ eqToHom (Functor.congr_obj (h n) Y).symm := by
    simpa [TowerLimit.eval, Functor.comp_map] using hn
  change (F.map f).app n =
      ((eqToHom (hObj X) : F.obj X ⟶ (lift (T := T) (D := D) c).obj X).app n) ≫
        ((lift (T := T) (D := D) c).map f).app n ≫
        ((eqToHom ((hObj Y).symm) : (lift (T := T) (D := D) c).obj Y ⟶ F.obj Y).app n)
  simp [eqToHom_app, lift]
  have hx : congrArg (fun Z : TowerLimit T => Z.obj n) (hObj X) = Functor.congr_obj (h n) X := by
    apply Subsingleton.elim
  have hy :
      congrArg (fun Z : TowerLimit T => Z.obj n) ((hObj Y).symm) = (Functor.congr_obj (h n) Y).symm := by
    apply Subsingleton.elim
  simpa [hx, hy] using hn'

end TowerCone

end Category
end Combinators
end LoF
end HeytingLean

