import HeytingLean.LoF.Combinators.Category.SpanBicategoryType

/-!
# SpanTricategoryThin — a canonical thin 3-cell layer for spans in `Type`

`SpanBicategoryType.lean` provides a bicategory of spans in `Type`, with 2-cells given by maps of
spans (morphisms in the hom-category `Span A B`).

For the SKY–Heyting–∞-groupoid program, Phase A.3 asks for a “higher cell” story beyond the
completion and strict Arrow-tower layers.  For the branchial-span substrate (spans in `Type`),
there is a canonical thin 3-cell layer:

- 3-cells between 2-cells are **equality of span maps**.

This is proof-irrelevant and therefore “thin” at the 3-cell level.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

namespace SpanType

universe u

/-- A thin 3-cell between span 2-cells: definitional equality of span maps. -/
abbrev Span3Cell {A B : Obj.{u}} {S T : Span A B} (η θ : S ⟶ T) : Prop :=
  η = θ

namespace Span3Cell

theorem refl {A B : Obj.{u}} {S T : Span A B} (η : S ⟶ T) : Span3Cell η η := rfl

theorem symm {A B : Obj.{u}} {S T : Span A B} {η θ : S ⟶ T} :
    Span3Cell η θ → Span3Cell θ η :=
  Eq.symm

theorem trans {A B : Obj.{u}} {S T : Span A B} {η θ κ : S ⟶ T} :
    Span3Cell η θ → Span3Cell θ κ → Span3Cell η κ :=
  Eq.trans

instance {A B : Obj.{u}} {S T : Span A B} (η θ : S ⟶ T) : Subsingleton (Span3Cell η θ) := by
  infer_instance

end Span3Cell

end SpanType

end Category
end Combinators
end LoF
end HeytingLean
