import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!
# SpanBicategoryType — the bicategory of spans in `Type`

This file provides a lightweight, **self-contained** bicategory-of-spans construction in the
ambient category of types.

We intentionally build spans using the *explicit pullback object* in `Type`:

`{ (x : X, y : Y) // f x = g y }`

This keeps the associator/unitor data computational and makes coherence proofs tractable without
additional categorical infrastructure.

This is used as a “branchial geometry” substrate: branchial structure can be packaged as spans of
ancestor types, and span composition is the correct categorical analogue of relational composition.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

namespace SpanType

open CategoryTheory

universe u

/-! ## Objects -/

/-- Wrapper to avoid instance clashes: `Type u` already carries a category instance. -/
structure Obj where
  carrier : Type u

namespace Obj

instance : CoeSort Obj (Type u) where
  coe X := X.carrier

def of (α : Type u) : Obj := ⟨α⟩

@[simp] theorem carrier_of (α : Type u) : (Obj.of α).carrier = α := rfl

end Obj

/-! ## 1-morphisms (spans) -/

/-- A span `A ⟵ X ⟶ B` in `Type`. -/
structure Span (A B : Obj.{u}) where
  apex : Type u
  fst : apex → A
  snd : apex → B

namespace Span

variable {A B C : Obj.{u}}

/-- Identity span `A ⟵ A ⟶ A`. -/
def idSpan (A : Obj.{u}) : Span A A where
  apex := A
  fst := _root_.id
  snd := _root_.id

@[simp] theorem idSpan_apex (A : Obj.{u}) : (Span.idSpan A).apex = A := rfl

@[simp] theorem idSpan_fst (A : Obj.{u}) : (Span.idSpan A).fst = (_root_.id : A → A) := rfl

@[simp] theorem idSpan_snd (A : Obj.{u}) : (Span.idSpan A).snd = (_root_.id : A → A) := rfl

/-- Pullback-style apex for composing spans in `Type`. -/
abbrev compApex (S : Span A B) (T : Span B C) : Type u :=
  {p : S.apex × T.apex // S.snd p.1 = T.fst p.2}

/-- Span composition by explicit pullback in `Type`. -/
def comp (S : Span A B) (T : Span B C) : Span A C where
  apex := compApex (A := A) (B := B) (C := C) S T
  fst := fun p => S.fst p.1.1
  snd := fun p => T.snd p.1.2

@[simp] theorem comp_fst (S : Span A B) (T : Span B C) (p : (comp S T).apex) :
    (comp S T).fst p = S.fst p.1.1 := rfl

@[simp] theorem comp_snd (S : Span A B) (T : Span B C) (p : (comp S T).apex) :
    (comp S T).snd p = T.snd p.1.2 := rfl

end Span

/-! ## 2-morphisms (maps of spans) -/

namespace SpanHom

variable {A B : Obj.{u}}

/-- A 2-morphism between spans is a map between apex types commuting with both legs. -/
abbrev Hom (S T : Span A B) : Type u :=
  {f : S.apex → T.apex // (∀ x, T.fst (f x) = S.fst x) ∧ (∀ x, T.snd (f x) = S.snd x)}

instance (S T : Span A B) : CoeFun (Hom S T) (fun _ => S.apex → T.apex) where
  coe f := f.1

@[simp] theorem fst_comp {S T : Span A B} (f : Hom S T) (x : S.apex) :
    T.fst (f x) = S.fst x :=
  (f.2.1 x)

@[simp] theorem snd_comp {S T : Span A B} (f : Hom S T) (x : S.apex) :
    T.snd (f x) = S.snd x :=
  (f.2.2 x)

@[ext] theorem ext {S T : Span A B} {f g : Hom S T}
    (h : ∀ x, f x = g x) : f = g := by
  apply Subtype.ext
  funext x
  exact h x

end SpanHom

namespace Span

variable {A B : Obj.{u}}

instance : Category (Span A B) where
  Hom S T := SpanHom.Hom S T
  id S := ⟨_root_.id, by constructor <;> intro x <;> rfl⟩
  comp f g :=
    ⟨fun x => g (f x), by
      constructor
      · intro x
        exact
          (SpanHom.fst_comp (f := g) (x := f x)).trans (SpanHom.fst_comp (f := f) (x := x))
      · intro x
        exact
          (SpanHom.snd_comp (f := g) (x := f x)).trans (SpanHom.snd_comp (f := f) (x := x))⟩
  id_comp := by
    intro S T f
    apply Subtype.ext
    funext x
    rfl
  comp_id := by
    intro S T f
    apply Subtype.ext
    funext x
    rfl
  assoc := by
    intro S T U V f g h
    apply Subtype.ext
    funext x
    rfl

end Span

/-! ## Bicategory structure -/

namespace BicategoryData

open Span
open SpanHom

variable {A B C D : Obj.{u}}

/-! ### Whiskering -/

def whiskerLeft (S : Span A B) {T U : Span B C} (η : T ⟶ U) :
    Span.comp (A := A) (B := B) (C := C) S T ⟶ Span.comp (A := A) (B := B) (C := C) S U :=
  ⟨fun p =>
      ⟨(p.1.1, η.1 p.1.2),
        by
          -- `S.snd p.1.1 = T.fst p.1.2` and `U.fst (η _) = T.fst _`
          calc
            S.snd p.1.1 = T.fst p.1.2 := p.2
            _ = U.fst (η.1 p.1.2) := (η.2.1 p.1.2).symm⟩,
    by
      constructor
      · intro p
        rfl
      · intro p
        -- second leg uses the `snd` commutation of `η`.
        exact (η.2.2 p.1.2)⟩

def whiskerRight {S T : Span A B} (η : S ⟶ T) (U : Span B C) :
    Span.comp (A := A) (B := B) (C := C) S U ⟶ Span.comp (A := A) (B := B) (C := C) T U :=
  ⟨fun p =>
      ⟨(η.1 p.1.1, p.1.2),
        by
          -- `S.snd p.1.1 = U.fst p.1.2` and `T.snd (η _) = S.snd _`
          calc
            T.snd (η.1 p.1.1) = S.snd p.1.1 := (η.2.2 p.1.1)
            _ = U.fst p.1.2 := p.2⟩,
    by
      constructor
      · intro p
        -- first leg uses `fst` commutation of `η`.
        exact (η.2.1 p.1.1)
      · intro p
        rfl⟩

/-! ### Associator and unitors -/

def associatorHom (S : Span A B) (T : Span B C) (U : Span C D) :
    (Span.comp (A := A) (B := C) (C := D) (Span.comp (A := A) (B := B) (C := C) S T) U) ⟶
      (Span.comp (A := A) (B := B) (C := D) S (Span.comp (A := B) (B := C) (C := D) T U)) :=
  ⟨fun p =>
      -- p : (((x,y),eq1), z, eq2)  ↦  (x, ((y,z),eq2), eq1)
      ⟨(p.1.1.1.1, ⟨(p.1.1.1.2, p.1.2), p.2⟩), p.1.1.2⟩,
    by
      constructor
      · intro p
        rfl
      · intro p
        rfl⟩

def associatorInv (S : Span A B) (T : Span B C) (U : Span C D) :
    (Span.comp (A := A) (B := B) (C := D) S (Span.comp (A := B) (B := C) (C := D) T U)) ⟶
      (Span.comp (A := A) (B := C) (C := D) (Span.comp (A := A) (B := B) (C := C) S T) U) :=
  ⟨fun p =>
      -- inverse reassociation
      ⟨(⟨(p.1.1, p.1.2.1.1), p.2⟩, p.1.2.1.2), p.1.2.2⟩,
    by
      constructor
      · intro p
        rfl
      · intro p
        rfl⟩

noncomputable def associatorIso (S : Span A B) (T : Span B C) (U : Span C D) :
    (Span.comp (A := A) (B := C) (C := D) (Span.comp (A := A) (B := B) (C := C) S T) U) ≅
      (Span.comp (A := A) (B := B) (C := D) S (Span.comp (A := B) (B := C) (C := D) T U)) where
  hom := associatorHom (A := A) (B := B) (C := C) (D := D) S T U
  inv := associatorInv (A := A) (B := B) (C := C) (D := D) S T U
  hom_inv_id := by
    apply Subtype.ext
    funext p
    rfl
  inv_hom_id := by
    apply Subtype.ext
    funext p
    rfl

def leftUnitorHom (S : Span A B) :
    Span.comp (A := A) (B := A) (C := B) (Span.idSpan A) S ⟶ S :=
  ⟨fun p => p.1.2,
    by
      constructor
      · intro p
        -- `p.1.1 = S.fst p.1.2`
        simpa using p.2.symm
      · intro p
        rfl⟩

def leftUnitorInv (S : Span A B) :
    S ⟶ Span.comp (A := A) (B := A) (C := B) (Span.idSpan A) S :=
  ⟨fun x => ⟨(S.fst x, x), rfl⟩,
    by
      constructor
      · intro x
        rfl
      · intro x
        rfl⟩

noncomputable def leftUnitorIso (S : Span A B) :
    Span.comp (A := A) (B := A) (C := B) (Span.idSpan A) S ≅ S where
  hom := leftUnitorHom (A := A) (B := B) S
  inv := leftUnitorInv (A := A) (B := B) S
  hom_inv_id := by
    apply Subtype.ext
    funext p
    cases p with
    | mk p hp =>
      cases p with
      | mk a x =>
        apply Subtype.ext
        apply Prod.ext
        · have h : a = S.fst x := by
            simpa using hp
          simpa using h.symm
        · rfl
  inv_hom_id := by
    apply Subtype.ext
    funext x
    rfl

def rightUnitorHom (S : Span A B) :
    Span.comp (A := A) (B := B) (C := B) S (Span.idSpan B) ⟶ S :=
  ⟨fun p => p.1.1,
    by
      constructor
      · intro p
        rfl
      · intro p
        -- `S.snd p.1.1 = p.1.2`
        simpa using p.2⟩

def rightUnitorInv (S : Span A B) :
    S ⟶ Span.comp (A := A) (B := B) (C := B) S (Span.idSpan B) :=
  ⟨fun x => ⟨(x, S.snd x), rfl⟩,
    by
      constructor
      · intro x
        rfl
      · intro x
        rfl⟩

noncomputable def rightUnitorIso (S : Span A B) :
    Span.comp (A := A) (B := B) (C := B) S (Span.idSpan B) ≅ S where
  hom := rightUnitorHom (A := A) (B := B) S
  inv := rightUnitorInv (A := A) (B := B) S
  hom_inv_id := by
    apply Subtype.ext
    funext p
    cases p with
    | mk p hp =>
      cases p with
      | mk x b =>
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have h : S.snd x = b := by
            simpa using hp
          exact h
  inv_hom_id := by
    apply Subtype.ext
    funext x
    rfl

end BicategoryData

open BicategoryData

noncomputable instance : Bicategory (Obj.{u}) where
  Hom A B := Span A B
  id A := Span.idSpan A
  comp S T := Span.comp S T
  homCategory A B := by
    infer_instance
  whiskerLeft := fun f _ _ η => whiskerLeft f η
  whiskerRight := fun η h => whiskerRight η h
  associator := fun f g h => associatorIso f g h
  leftUnitor := fun f => leftUnitorIso f
  rightUnitor := fun f => rightUnitorIso f
  whiskerLeft_id := by
    intro A B C f g
    apply Subtype.ext
    funext p
    rfl
  whiskerLeft_comp := by
    intro A B C f g h i η θ
    apply Subtype.ext
    funext p
    rfl
  id_whiskerLeft := by
    intro A B f g η
    apply Subtype.ext
    funext x
    apply Subtype.ext
    apply Prod.ext
    · have hx : x.1.1 = f.fst x.1.2 := by
        simpa using x.2
      have hη : g.fst (η.1 x.1.2) = f.fst x.1.2 := η.2.1 x.1.2
      exact (hη.trans hx.symm).symm
    · rfl
  comp_whiskerLeft := by
    intro A B C D f g h h' η
    apply Subtype.ext
    funext p
    rfl
  id_whiskerRight := by
    intro A B C f g
    apply Subtype.ext
    funext p
    rfl
  comp_whiskerRight := by
    intro A B C f g h η θ i
    apply Subtype.ext
    funext p
    rfl
  whiskerRight_id := by
    intro A B f g η
    apply Subtype.ext
    funext x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hx : f.snd x.1.1 = x.1.2 := by
        simpa using x.2
      have hη : g.snd (η.1 x.1.1) = f.snd x.1.1 := η.2.2 x.1.1
      exact (hη.trans hx).symm
  whiskerRight_comp := by
    intro A B C D f f' η g h
    apply Subtype.ext
    funext p
    rfl
  whisker_assoc := by
    intro A B C D f g g' η h
    apply Subtype.ext
    funext p
    rfl
  whisker_exchange := by
    intro A B C f g h i η θ
    apply Subtype.ext
    funext p
    rfl
  pentagon := by
    intro A B C D E f g h i
    apply Subtype.ext
    funext p
    rfl
  triangle := by
    intro A B C f g
    apply Subtype.ext
    funext p
    rfl

end SpanType

end Category
end Combinators
end LoF
end HeytingLean
