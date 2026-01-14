import Mathlib.CategoryTheory.CommSq
import HeytingLean.LoF.Combinators.Category.NFoldCategory

/-!
# DoubleCategory — a thin strict double category interface for SKY path squares

Mathlib provides a strong API for commutative squares (`CategoryTheory.CommSq`) but does not ship a
general double-category structure.

For the SKY–Heyting–∞-groupoid program we keep a conservative, proof-irrelevant interface:

- horizontal and vertical 1-cells each form a category (encoded explicitly as `CatData`), and
- squares are represented by a **Prop-valued** cell predicate, with horizontal/vertical pasting.

This is sufficient to state and compose:

- strict commutative squares (cells = `CommSq`), and
- “weak” squares commuting up to completion-homotopy (`completionSqCell`).
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory

universe u v w

/-! ## An explicit “category as data” record (to avoid conflicting instances) -/

structure CatData (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id : ∀ a : Obj, Hom a a
  comp : ∀ {a b c : Obj}, Hom a b → Hom b c → Hom a c
  id_comp : ∀ {a b : Obj} (f : Hom a b), comp (id a) f = f
  comp_id : ∀ {a b : Obj} (f : Hom a b), comp f (id b) = f
  assoc : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp (comp f g) h = comp f (comp g h)

namespace CatData

def ofCategory (C : Type u) [Category C] : CatData (Obj := C) where
  Hom := fun a b => a ⟶ b
  id := fun a => 𝟙 a
  comp := fun f g => f ≫ g
  id_comp := by
    intro a b f
    simp
  comp_id := by
    intro a b f
    simp
  assoc := by
    intro a b c d f g h
    simp

end CatData

/-! ## Thin strict double categories -/

/-- A strict double category interface where the cell type is a Prop. -/
structure ThinDoubleCategory where
  Obj : Type u
  H : CatData (Obj := Obj)
  V : CatData (Obj := Obj)
  Cell :
    ∀ {a b c d : Obj}, H.Hom a b → H.Hom c d → V.Hom a c → V.Hom b d → Prop
  idCellH :
    ∀ {a b : Obj} (f : H.Hom a b), Cell f f (V.id a) (V.id b)
  idCellV :
    ∀ {a c : Obj} (g : V.Hom a c), Cell (H.id a) (H.id c) g g
  hcomp :
    ∀ {a b c a' b' c' : Obj}
      {top₁ : H.Hom a b} {top₂ : H.Hom b c}
      {bottom₁ : H.Hom a' b'} {bottom₂ : H.Hom b' c'}
      {left : V.Hom a a'} {mid : V.Hom b b'} {right : V.Hom c c'},
      Cell top₁ bottom₁ left mid →
        Cell top₂ bottom₂ mid right →
          Cell (H.comp top₁ top₂) (H.comp bottom₁ bottom₂) left right
  vcomp :
    ∀ {a b c d e f : Obj}
      {top : H.Hom a b} {mid : H.Hom c d} {bottom : H.Hom e f}
      {left₁ : V.Hom a c} {right₁ : V.Hom b d}
      {left₂ : V.Hom c e} {right₂ : V.Hom d f},
      Cell top mid left₁ right₁ →
        Cell mid bottom left₂ right₂ →
          Cell top bottom (V.comp left₁ left₂) (V.comp right₁ right₂)

namespace ThinDoubleCategory

variable {D : ThinDoubleCategory}

/-! ### Derived composition laws (Prop-valued cells are proof-irrelevant) -/

/-- Horizontal left unit: pasting an identity-on-horizontals square on the left changes nothing. -/
theorem hcomp_id_left
    {a b a' b' : D.Obj}
    {top : D.H.Hom a b} {bottom : D.H.Hom a' b'}
    {left : D.V.Hom a a'} {right : D.V.Hom b b'}
    (sq : D.Cell top bottom left right) :
    D.Cell top bottom left right := by
  have h :
      D.Cell (D.H.comp (D.H.id a) top) (D.H.comp (D.H.id a') bottom) left right :=
    D.hcomp
      (top₁ := D.H.id a) (top₂ := top)
      (bottom₁ := D.H.id a') (bottom₂ := bottom)
      (left := left) (mid := left) (right := right)
      (D.idCellV (g := left)) sq
  simpa [D.H.id_comp] using h

/-- Horizontal right unit: pasting an identity-on-horizontals square on the right changes nothing. -/
theorem hcomp_id_right
    {a b a' b' : D.Obj}
    {top : D.H.Hom a b} {bottom : D.H.Hom a' b'}
    {left : D.V.Hom a a'} {right : D.V.Hom b b'}
    (sq : D.Cell top bottom left right) :
    D.Cell top bottom left right := by
  have h :
      D.Cell (D.H.comp top (D.H.id b)) (D.H.comp bottom (D.H.id b')) left right :=
    D.hcomp
      (top₁ := top) (top₂ := D.H.id b)
      (bottom₁ := bottom) (bottom₂ := D.H.id b')
      (left := left) (mid := right) (right := right)
      sq (D.idCellV (g := right))
  simpa [D.H.comp_id] using h

/-- Vertical top unit: pasting an identity-on-verticals square on the top changes nothing. -/
theorem vcomp_id_top
    {a b c d : D.Obj}
    {top : D.H.Hom a b} {bottom : D.H.Hom c d}
    {left : D.V.Hom a c} {right : D.V.Hom b d}
    (sq : D.Cell top bottom left right) :
    D.Cell top bottom left right := by
  have h :
      D.Cell top bottom (D.V.comp (D.V.id a) left) (D.V.comp (D.V.id b) right) :=
    D.vcomp
      (top := top) (mid := top) (bottom := bottom)
      (left₁ := D.V.id a) (right₁ := D.V.id b)
      (left₂ := left) (right₂ := right)
      (D.idCellH (f := top)) sq
  simpa [D.V.id_comp] using h

/-- Vertical bottom unit: pasting an identity-on-verticals square on the bottom changes nothing. -/
theorem vcomp_id_bottom
    {a b c d : D.Obj}
    {top : D.H.Hom a b} {bottom : D.H.Hom c d}
    {left : D.V.Hom a c} {right : D.V.Hom b d}
    (sq : D.Cell top bottom left right) :
    D.Cell top bottom left right := by
  have h :
      D.Cell top bottom (D.V.comp left (D.V.id c)) (D.V.comp right (D.V.id d)) :=
    D.vcomp
      (top := top) (mid := bottom) (bottom := bottom)
      (left₁ := left) (right₁ := right)
      (left₂ := D.V.id c) (right₂ := D.V.id d)
      sq (D.idCellH (f := bottom))
  simpa [D.V.comp_id] using h

/-- Horizontal associativity (with the canonical right-associated target bracketing). -/
theorem hcomp_assoc
    {a b c d a' b' c' d' : D.Obj}
    {top₁ : D.H.Hom a b} {top₂ : D.H.Hom b c} {top₃ : D.H.Hom c d}
    {bottom₁ : D.H.Hom a' b'} {bottom₂ : D.H.Hom b' c'} {bottom₃ : D.H.Hom c' d'}
    {left : D.V.Hom a a'} {mid₁ : D.V.Hom b b'} {mid₂ : D.V.Hom c c'} {right : D.V.Hom d d'}
    (sq₁ : D.Cell top₁ bottom₁ left mid₁)
    (sq₂ : D.Cell top₂ bottom₂ mid₁ mid₂)
    (sq₃ : D.Cell top₃ bottom₃ mid₂ right) :
    D.Cell (D.H.comp top₁ (D.H.comp top₂ top₃)) (D.H.comp bottom₁ (D.H.comp bottom₂ bottom₃)) left right := by
  have sq₁₂ : D.Cell (D.H.comp top₁ top₂) (D.H.comp bottom₁ bottom₂) left mid₂ :=
    D.hcomp sq₁ sq₂
  have sq₁₂₃ :
      D.Cell (D.H.comp (D.H.comp top₁ top₂) top₃) (D.H.comp (D.H.comp bottom₁ bottom₂) bottom₃) left right :=
    D.hcomp sq₁₂ sq₃
  simpa [D.H.assoc] using sq₁₂₃

/-- Vertical associativity (with the canonical right-associated target bracketing). -/
theorem vcomp_assoc
    {a b c d e f g h : D.Obj}
    {top : D.H.Hom a b} {mid₁ : D.H.Hom c d} {mid₂ : D.H.Hom e f} {bottom : D.H.Hom g h}
    {left₁ : D.V.Hom a c} {right₁ : D.V.Hom b d}
    {left₂ : D.V.Hom c e} {right₂ : D.V.Hom d f}
    {left₃ : D.V.Hom e g} {right₃ : D.V.Hom f h}
    (sq₁ : D.Cell top mid₁ left₁ right₁)
    (sq₂ : D.Cell mid₁ mid₂ left₂ right₂)
    (sq₃ : D.Cell mid₂ bottom left₃ right₃) :
    D.Cell top bottom (D.V.comp left₁ (D.V.comp left₂ left₃)) (D.V.comp right₁ (D.V.comp right₂ right₃)) := by
  have sq₁₂ : D.Cell top mid₂ (D.V.comp left₁ left₂) (D.V.comp right₁ right₂) :=
    D.vcomp sq₁ sq₂
  have sq₁₂₃ :
      D.Cell top bottom (D.V.comp (D.V.comp left₁ left₂) left₃) (D.V.comp (D.V.comp right₁ right₂) right₃) :=
    D.vcomp sq₁₂ sq₃
  simpa [D.V.assoc] using sq₁₂₃

/-- Interchange: horizontal/vertical pasting commute (proof-irrelevance for Prop-valued cells). -/
theorem interchange
    {a b c a' b' c' a'' b'' c'' : D.Obj}
    {top₁ : D.H.Hom a b} {top₂ : D.H.Hom b c}
    {mid₁ : D.H.Hom a' b'} {mid₂ : D.H.Hom b' c'}
    {bottom₁ : D.H.Hom a'' b''} {bottom₂ : D.H.Hom b'' c''}
    {left₁ : D.V.Hom a a'} {midv₁ : D.V.Hom b b'} {right₁ : D.V.Hom c c'}
    {left₂ : D.V.Hom a' a''} {midv₂ : D.V.Hom b' b''} {right₂ : D.V.Hom c' c''}
    (sq₁₁ : D.Cell top₁ mid₁ left₁ midv₁)
    (sq₁₂ : D.Cell top₂ mid₂ midv₁ right₁)
    (sq₂₁ : D.Cell mid₁ bottom₁ left₂ midv₂)
    (sq₂₂ : D.Cell mid₂ bottom₂ midv₂ right₂) :
    D.vcomp (D.hcomp sq₁₁ sq₁₂) (D.hcomp sq₂₁ sq₂₂) =
      D.hcomp (D.vcomp sq₁₁ sq₂₁) (D.vcomp sq₁₂ sq₂₂) := by
  apply Subsingleton.elim

end ThinDoubleCategory

/-! ## The commutative-square double category of a category -/

/-- The thin double category whose squares are commutative squares in a category. -/
def commSqThinDoubleCategory (C : Type u) [Category C] : ThinDoubleCategory where
  Obj := C
  H := CatData.ofCategory C
  V := CatData.ofCategory C
  Cell := fun {a b c d} top bottom left right => CommSq top left right bottom
  idCellH := by
    intro a b f
    refine ⟨by simp [CatData.ofCategory]⟩
  idCellV := by
    intro a c g
    refine ⟨by simp [CatData.ofCategory]⟩
  hcomp := by
    intro a b c a' b' c' top₁ top₂ bottom₁ bottom₂ left mid right sq₁ sq₂
    exact CommSq.horiz_comp sq₁ sq₂
  vcomp := by
    intro a b c d e f top mid bottom left₁ right₁ left₂ right₂ sq₁ sq₂
    exact CommSq.vert_comp sq₁ sq₂

/-! ## Completion-homotopy squares paste horizontally/vertically -/

open HeytingLean.LoF.Comb

theorem completionSqCell_horiz_comp
    {a b c a' b' c' : MWObj}
    {top₁ : a ⟶ b} {top₂ : b ⟶ c}
    {bottom₁ : a' ⟶ b'} {bottom₂ : b' ⟶ c'}
    {left : a ⟶ a'} {mid : b ⟶ b'} {right : c ⟶ c'} :
    completionSqCell top₁ bottom₁ left mid →
      completionSqCell top₂ bottom₂ mid right →
        completionSqCell (top₁ ≫ top₂) (bottom₁ ≫ bottom₂) left right := by
  intro sq₁ sq₂
  dsimp [completionSqCell] at sq₁ sq₂ ⊢
  change
    CompletionHomotopy
      (LSteps.comp (LSteps.comp top₁ top₂) right)
      (LSteps.comp left (LSteps.comp bottom₁ bottom₂))
  -- Pasting: first apply the right square, then the left square.
  have h₂ :
      CompletionHomotopy
        (LSteps.comp top₁ (LSteps.comp top₂ right))
        (LSteps.comp top₁ (LSteps.comp mid bottom₂)) :=
    CompletionHomotopy.whisker_left top₁ sq₂
  have h₁raw :
      CompletionHomotopy
        (LSteps.comp (LSteps.comp top₁ mid) bottom₂)
        (LSteps.comp (LSteps.comp left bottom₁) bottom₂) :=
    CompletionHomotopy.whisker_right sq₁ bottom₂
  have h₁ :
      CompletionHomotopy
        (LSteps.comp top₁ (LSteps.comp mid bottom₂))
        (LSteps.comp left (LSteps.comp bottom₁ bottom₂)) := by
    simpa [LSteps.comp_assoc] using h₁raw
  have h :
      CompletionHomotopy
        (LSteps.comp top₁ (LSteps.comp top₂ right))
        (LSteps.comp left (LSteps.comp bottom₁ bottom₂)) :=
    CompletionHomotopy.trans h₂ h₁
  have hassoc :
      CompletionHomotopy
        (LSteps.comp (LSteps.comp top₁ top₂) right)
        (LSteps.comp top₁ (LSteps.comp top₂ right)) := by
    simpa [LSteps.comp_assoc] using
      (CompletionHomotopy.refl (LSteps.comp (LSteps.comp top₁ top₂) right))
  exact CompletionHomotopy.trans hassoc h

theorem completionSqCell_vert_comp
    {a b c d e f : MWObj}
    {top : a ⟶ b} {mid : c ⟶ d} {bottom : e ⟶ f}
    {left₁ : a ⟶ c} {right₁ : b ⟶ d}
    {left₂ : c ⟶ e} {right₂ : d ⟶ f} :
    completionSqCell top mid left₁ right₁ →
      completionSqCell mid bottom left₂ right₂ →
        completionSqCell top bottom (left₁ ≫ left₂) (right₁ ≫ right₂) := by
  intro sq₁ sq₂
  dsimp [completionSqCell] at sq₁ sq₂ ⊢
  change
    CompletionHomotopy
      (LSteps.comp top (LSteps.comp right₁ right₂))
      (LSteps.comp (LSteps.comp left₁ left₂) bottom)
  -- First use the upper square, then the lower square.
  have h₁raw :
      CompletionHomotopy
        (LSteps.comp (LSteps.comp top right₁) right₂)
        (LSteps.comp (LSteps.comp left₁ mid) right₂) :=
    CompletionHomotopy.whisker_right sq₁ right₂
  have h₁ :
      CompletionHomotopy
        (LSteps.comp top (LSteps.comp right₁ right₂))
        (LSteps.comp left₁ (LSteps.comp mid right₂)) := by
    simpa [LSteps.comp_assoc] using h₁raw
  have h₂ :
      CompletionHomotopy
        (LSteps.comp left₁ (LSteps.comp mid right₂))
        (LSteps.comp left₁ (LSteps.comp left₂ bottom)) :=
    CompletionHomotopy.whisker_left left₁ sq₂
  have h₂' :
      CompletionHomotopy
        (LSteps.comp left₁ (LSteps.comp mid right₂))
        (LSteps.comp (LSteps.comp left₁ left₂) bottom) := by
    simpa [LSteps.comp_assoc] using h₂
  have h :
      CompletionHomotopy
        (LSteps.comp top (LSteps.comp right₁ right₂))
        (LSteps.comp (LSteps.comp left₁ left₂) bottom) :=
    CompletionHomotopy.trans h₁ h₂'
  exact h

/-! ## The completion-homotopy square double category on `MWObj` -/

/-- The thin double category structure on the multiway path category whose squares commute up to completion homotopy. -/
def skyCompletionThinDoubleCategory : ThinDoubleCategory where
  Obj := MWObj
  H := CatData.ofCategory MWObj
  V := CatData.ofCategory MWObj
  Cell := fun {a b c d} top bottom left right => completionSqCell top bottom left right
  idCellH := by
    intro a b f
    dsimp [completionSqCell, CatData.ofCategory]
    change CompletionHomotopy (LSteps.comp f (LSteps.refl b.term)) (LSteps.comp (LSteps.refl a.term) f)
    simpa using (CompletionHomotopy.refl f)
  idCellV := by
    intro a c g
    dsimp [completionSqCell, CatData.ofCategory]
    change CompletionHomotopy (LSteps.comp (LSteps.refl a.term) g) (LSteps.comp g (LSteps.refl c.term))
    simpa using (CompletionHomotopy.refl g)
  hcomp := by
    intro a b c a' b' c' top₁ top₂ bottom₁ bottom₂ left mid right sq₁ sq₂
    exact completionSqCell_horiz_comp (top₁ := top₁) (top₂ := top₂) (bottom₁ := bottom₁) (bottom₂ := bottom₂)
      (left := left) (mid := mid) (right := right) sq₁ sq₂
  vcomp := by
    intro a b c d e f top mid bottom left₁ right₁ left₂ right₂ sq₁ sq₂
    exact completionSqCell_vert_comp (top := top) (mid := mid) (bottom := bottom)
      (left₁ := left₁) (right₁ := right₁) (left₂ := left₂) (right₂ := right₂) sq₁ sq₂

end Category
end Combinators
end LoF
end HeytingLean
