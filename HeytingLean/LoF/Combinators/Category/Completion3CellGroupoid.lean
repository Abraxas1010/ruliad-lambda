import Mathlib.CategoryTheory.Groupoid
import HeytingLean.LoF.Combinators.Category.Completion3Cell

/-!
# Completion3CellGroupoid — packaging the 3-cell witness layer into a strict groupoid (thin)

`Completion3Cell.lean` defines a `Type` of explicit 3-cell witnesses between parallel completion
2-paths, intended as a data-level reification of the Prop relation `Completion2PathRel`.

Those witnesses are *derivation trees*: two different derivations should be treated as “the same”
3-cell up to coherence, so they do **not** form a strict category by definitional equality.

For Phase A.3 we provide a conservative, strict packaging:

- morphisms `η ⟶ η'` are the **existence** of a 3-cell witness (`Nonempty`), lifted to `Type`
  via `PLift`;
- composition is induced by `Completion3Cell.trans`;
- inverses are induced by `Completion3Cell.symm`.

Because these hom-types are subsingleton, all category/groupoid laws hold trivially.

This is intentionally thin: it is a reliable “3-cell composition laws” interface while we keep the
fully witness-carrying higher-categorical structure as future work.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory

namespace Completion3Cell

/-- Thin (subsingleton) 3-cells: mere existence of an explicit `Completion3Cell` witness. -/
abbrev Exists3Cell {a b : MWObj} {p q : a ⟶ b} (η η' : Completion2Path p q) : Type :=
  PLift (Nonempty (Completion3Cell η η'))

namespace Exists3Cell

@[simp] def ofCell {a b : MWObj} {p q : a ⟶ b} {η η' : Completion2Path p q}
    (h : Completion3Cell η η') : Exists3Cell η η' :=
  ⟨⟨h⟩⟩

@[simp] def refl {a b : MWObj} {p q : a ⟶ b} (η : Completion2Path p q) : Exists3Cell η η :=
  ofCell (Completion3Cell.refl η)

@[simp] def trans {a b : MWObj} {p q : a ⟶ b} {η η' η'' : Completion2Path p q}
    (h₁ : Exists3Cell η η') (h₂ : Exists3Cell η' η'') : Exists3Cell η η'' :=
  ⟨by
    rcases h₁.down with ⟨c₁⟩
    rcases h₂.down with ⟨c₂⟩
    exact ⟨Completion3Cell.trans c₁ c₂⟩⟩

@[simp] def symm {a b : MWObj} {p q : a ⟶ b} {η η' : Completion2Path p q}
    (h : Exists3Cell η η') : Exists3Cell η' η :=
  ⟨by
    rcases h.down with ⟨c⟩
    exact ⟨Completion3Cell.symm c⟩⟩

end Exists3Cell

/-- For fixed boundaries `p q`, completion 2-paths form a **thin groupoid** under existence of 3-cells. -/
instance {a b : MWObj} (p q : a ⟶ b) : Groupoid (Completion2Path p q) where
  Hom η η' := Exists3Cell (p := p) (q := q) η η'
  id η := Exists3Cell.refl (p := p) (q := q) η
  comp h₁ h₂ := Exists3Cell.trans (p := p) (q := q) h₁ h₂
  id_comp := by
    intro η η' h
    apply Subsingleton.elim
  comp_id := by
    intro η η' h
    apply Subsingleton.elim
  assoc := by
    intro η₁ η₂ η₃ η₄ h₁ h₂ h₃
    apply Subsingleton.elim
  inv h := Exists3Cell.symm (p := p) (q := q) h
  inv_comp := by
    intro η η' h
    apply Subsingleton.elim
  comp_inv := by
    intro η η' h
    apply Subsingleton.elim

end Completion3Cell

end Category
end Combinators
end LoF
end HeytingLean

