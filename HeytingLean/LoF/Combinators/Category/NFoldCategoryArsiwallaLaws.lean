import HeytingLean.LoF.Combinators.Category.NFoldCategoryArsiwalla

/-!
# NFoldCategoryArsiwallaLaws — basic laws for the Arsiwalla `Arrow`-tower structure maps

`NFoldCategoryArsiwalla.lean` defines the strict Arsiwalla-style structure maps

- `idArrow : C ⥤ Arrow C` and
- `compArrow : ComposableArrows C 2 ⥤ Arrow C`.

Phase A.1 asks not only for data but also for explicit **laws**.  For the strict `Arrow` tower,
these laws reduce to definitional equalities (or `Category.assoc`) and can be stated directly.

Objectivity boundary:
- These are strict tower laws for the `Arrow` construction. They do not assert any semantic
  completeness claim about rewriting/completion in SKY.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory

universe u v

/-! ## Evaluation functors on `ComposableArrows C 2 = (Fin 3 ⥤ C)` -/

namespace ComposableArrows

/-- Evaluate a 2-chain at the left endpoint (`0`). -/
def eval0 (C : Type u) [Category.{v} C] : ComposableArrows C 2 ⥤ C where
  obj F := F.obj ⟨0, by decide⟩
  map {F G} φ := φ.app ⟨0, by decide⟩
  map_id := by intro F; rfl
  map_comp := by intro F G H φ ψ; rfl

/-- Evaluate a 2-chain at the middle object (`1`). -/
def eval1 (C : Type u) [Category.{v} C] : ComposableArrows C 2 ⥤ C where
  obj F := F.obj ⟨1, by decide⟩
  map {F G} φ := φ.app ⟨1, by decide⟩
  map_id := by intro F; rfl
  map_comp := by intro F G H φ ψ; rfl

/-- Evaluate a 2-chain at the right endpoint (`2`). -/
def eval2 (C : Type u) [Category.{v} C] : ComposableArrows C 2 ⥤ C where
  obj F := F.obj ⟨2, by decide⟩
  map {F G} φ := φ.app ⟨2, by decide⟩
  map_id := by intro F; rfl
  map_comp := by intro F G H φ ψ; rfl

end ComposableArrows

/-! ## Strict laws for `idArrow` / `compArrow` -/

section

variable {C : Type u} [Category.{v} C]

theorem idArrow_src : (idArrow (C := C)) ⋙ (Arrow.leftFunc (C := C)) = 𝟭 C := by
  rfl

theorem idArrow_tgt : (idArrow (C := C)) ⋙ (Arrow.rightFunc (C := C)) = 𝟭 C := by
  rfl

theorem compArrow_src :
    (compArrow (C := C)) ⋙ (Arrow.leftFunc (C := C)) = ComposableArrows.eval0 (C := C) := by
  rfl

theorem compArrow_tgt :
    (compArrow (C := C)) ⋙ (Arrow.rightFunc (C := C)) = ComposableArrows.eval2 (C := C) := by
  rfl

/-! ### Unit laws (functor-level) -/

/-- Arsiwalla-style “left unit” inclusion `Arrow C ⥤ ComposableArrows C 2`,
sending `f : X ⟶ Y` to `X ⟶ Y ⟶ Y` (second arrow is an identity). -/
def unitLeft : Arrow C ⥤ ComposableArrows C 2 where
  obj f := ComposableArrows.mk₂ f.hom (𝟙 f.right)
  map {f g} φ := by
    refine
      CategoryTheory.ComposableArrows.homMk₂
        (f := ComposableArrows.mk₂ f.hom (𝟙 f.right))
        (g := ComposableArrows.mk₂ g.hom (𝟙 g.right))
        φ.left φ.right φ.right ?_ ?_
    ·
      dsimp [ComposableArrows.map', ComposableArrows.mk₂, ComposableArrows.precomp]
      simp
    ·
      dsimp [ComposableArrows.map', ComposableArrows.mk₂, ComposableArrows.precomp]
      have hf :
          ComposableArrows.Precomp.map (ComposableArrows.mk₁ (𝟙 f.right)) f.hom 1 2
              (by simp [Fin.le_def]) =
            𝟙 f.right := by
        simpa using
          (ComposableArrows.Precomp.map_one_succ
            (F := ComposableArrows.mk₁ (𝟙 f.right)) (f := f.hom) (j := 1) (hj := by decide))
      have hg :
          ComposableArrows.Precomp.map (ComposableArrows.mk₁ (𝟙 g.right)) g.hom 1 2
              (by simp [Fin.le_def]) =
            𝟙 g.right := by
        simpa using
          (ComposableArrows.Precomp.map_one_succ
            (F := ComposableArrows.mk₁ (𝟙 g.right)) (f := g.hom) (j := 1) (hj := by decide))
      simp [hf, hg]
  map_id := by
    intro f
    ext <;> rfl
  map_comp := by
    intro f g h φ ψ
    ext <;> rfl

lemma unitLeft_map_app_two {f g : Arrow C} (φ : f ⟶ g) :
    ((unitLeft (C := C)).map φ).app (2 : Fin 3) = φ.right := by
  dsimp [unitLeft]
  simpa using
    (CategoryTheory.ComposableArrows.homMk₂_app_two
      (f := ComposableArrows.mk₂ f.hom (𝟙 f.right))
      (g := ComposableArrows.mk₂ g.hom (𝟙 g.right))
      φ.left φ.right φ.right _ _)

theorem compArrow_unitLeft : (unitLeft (C := C)) ⋙ (compArrow (C := C)) = 𝟭 (Arrow C) := by
  refine CategoryTheory.Functor.ext (fun f => ?_) (fun f g φ => ?_)
  ·
    refine Arrow.ext (h₁ := rfl) (h₂ := rfl) ?_
    dsimp [compArrow, unitLeft]
    simpa using
      (ComposableArrows.Precomp.map_zero_succ_succ (F := ComposableArrows.mk₁ (𝟙 f.right))
        (f := f.hom) (j := 0) (hj := by decide))
  ·
    ext
    ·
      dsimp [Arrow]
      simp [compArrow, unitLeft]
    ·
      dsimp [Arrow]
      simp [compArrow, unitLeft_map_app_two]

/-- Arsiwalla-style “right unit” inclusion `Arrow C ⥤ ComposableArrows C 2`,
sending `f : X ⟶ Y` to `X ⟶ X ⟶ Y` (first arrow is an identity). -/
def unitRight : Arrow C ⥤ ComposableArrows C 2 where
  obj f := ComposableArrows.mk₂ (𝟙 f.left) f.hom
  map {f g} φ := by
    refine
      CategoryTheory.ComposableArrows.homMk₂
        (f := ComposableArrows.mk₂ (𝟙 f.left) f.hom)
        (g := ComposableArrows.mk₂ (𝟙 g.left) g.hom)
        φ.left φ.left φ.right ?_ ?_
    ·
      dsimp [ComposableArrows.map', ComposableArrows.mk₂, ComposableArrows.precomp]
      simp
    ·
      dsimp [ComposableArrows.map', ComposableArrows.mk₂, ComposableArrows.precomp]
      have hf :
          ComposableArrows.Precomp.map (ComposableArrows.mk₁ f.hom) (𝟙 f.left) 1 2 (by simp [Fin.le_def]) =
            f.hom := by
        simpa using
          (ComposableArrows.Precomp.map_one_succ (F := ComposableArrows.mk₁ f.hom) (f := 𝟙 f.left)
            (j := 1) (hj := by decide))
      have hg :
          ComposableArrows.Precomp.map (ComposableArrows.mk₁ g.hom) (𝟙 g.left) 1 2 (by simp [Fin.le_def]) =
            g.hom := by
        simpa using
          (ComposableArrows.Precomp.map_one_succ (F := ComposableArrows.mk₁ g.hom) (f := 𝟙 g.left)
            (j := 1) (hj := by decide))
      simp [hf, hg]
  map_id := by
    intro f
    ext <;> rfl
  map_comp := by
    intro f g h φ ψ
    ext <;> rfl

lemma unitRight_map_app_zero {f g : Arrow C} (φ : f ⟶ g) :
    ((unitRight (C := C)).map φ).app (0 : Fin 3) = φ.left := by
  dsimp [unitRight]

lemma unitRight_map_app_two {f g : Arrow C} (φ : f ⟶ g) :
    ((unitRight (C := C)).map φ).app (2 : Fin 3) = φ.right := by
  dsimp [unitRight]
  simpa using
    (CategoryTheory.ComposableArrows.homMk₂_app_two
      (f := ComposableArrows.mk₂ (𝟙 f.left) f.hom)
      (g := ComposableArrows.mk₂ (𝟙 g.left) g.hom)
      φ.left φ.left φ.right _ _)

theorem compArrow_unitRight : (unitRight (C := C)) ⋙ (compArrow (C := C)) = 𝟭 (Arrow C) := by
  refine CategoryTheory.Functor.ext (fun f => ?_) (fun f g φ => ?_)
  ·
    refine Arrow.ext (h₁ := rfl) (h₂ := rfl) ?_
    dsimp [compArrow, unitRight]
    simpa using
      (ComposableArrows.Precomp.map_zero_succ_succ (F := ComposableArrows.mk₁ f.hom) (f := 𝟙 f.left)
        (j := 0) (hj := by decide))
  ·
    ext
    ·
      dsimp [Arrow]
      simp [compArrow, unitRight_map_app_zero]
    ·
      dsimp [Arrow]
      simp [compArrow, unitRight_map_app_two]

/-! ### Associativity law (object-level) -/

theorem compArrow_assoc_obj {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (compArrow (C := C)).obj (ComposableArrows.mk₂ (f ≫ g) h) =
      (compArrow (C := C)).obj (ComposableArrows.mk₂ f (g ≫ h)) := by
  -- Reduce to associativity in `C` on the underlying arrow.
  change Arrow.mk ((f ≫ g) ≫ h) = Arrow.mk (f ≫ (g ≫ h))
  refine Arrow.ext (h₁ := rfl) (h₂ := rfl) ?_
  simp [Category.assoc]

/-! ### Associativity law (functor-level) -/

private def Φ₀₂₃ : Fin 3 ⥤ Fin 4 where
  obj
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 2
    | ⟨2, _⟩ => 3
  map {i j} hij :=
    homOfLE (by
      have hij' : i ≤ j := leOfHom hij
      fin_cases i <;> fin_cases j <;> simp at hij' <;> simp)

private def Φ₀₁₃ : Fin 3 ⥤ Fin 4 where
  obj
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 3
  map {i j} hij :=
    homOfLE (by
      have hij' : i ≤ j := leOfHom hij
      fin_cases i <;> fin_cases j <;> simp at hij' <;> simp)

theorem compArrow_assoc :
    (CategoryTheory.ComposableArrows.whiskerLeftFunctor (C := C) (m := 3) (n := 2) Φ₀₂₃) ⋙
        (compArrow (C := C)) =
      (CategoryTheory.ComposableArrows.whiskerLeftFunctor (C := C) (m := 3) (n := 2) Φ₀₁₃) ⋙
        (compArrow (C := C)) := by
  refine CategoryTheory.Functor.ext (fun F => ?_) (fun F G φ => ?_)
  ·
    refine Arrow.ext (h₁ := rfl) (h₂ := rfl) ?_
    dsimp [CategoryTheory.ComposableArrows.whiskerLeftFunctor, CategoryTheory.ComposableArrows.whiskerLeft,
      compArrow]
    have h : Φ₀₂₃.map hom02 = Φ₀₁₃.map hom02 := by
      apply Subsingleton.elim
    simp [h]
  ·
    ext
    ·
      dsimp [CategoryTheory.ComposableArrows.whiskerLeftFunctor, CategoryTheory.ComposableArrows.whiskerLeft,
        compArrow]
      simp [Φ₀₂₃, Φ₀₁₃]
    ·
      dsimp [CategoryTheory.ComposableArrows.whiskerLeftFunctor, CategoryTheory.ComposableArrows.whiskerLeft,
        compArrow]
      simp [Φ₀₂₃, Φ₀₁₃]

end

end Category
end Combinators
end LoF
end HeytingLean
