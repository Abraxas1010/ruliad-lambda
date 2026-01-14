import HeytingLean.LoF.Combinators.Category.Completion3CellGroupoid

/-!
# CompletionTricategoryThin — packaging the completion 3-cell layer as a thin tricategory

Mathlib currently provides `Bicategory` but not a general tricategory/ω-category API.
For the SKY completion-homotopy track we nevertheless have:

- 1-cells: labeled paths `a ⟶ b` in `MWObj`,
- 2-cells: explicit completion 2-paths `Completion2Path f g`,
- 3-cells: explicit coherence witnesses `Completion3Cell η η'`.

For Phase A.3 we package this into a minimal **thin tricategory** record where 3-cells are taken
to be mere existence (`Exists3Cell`), so all 3-cell hom-types are subsingleton and composition laws
hold robustly.

Objectivity boundary:
- This file is a structural interface only; it does not assert semantic completeness of completion
  rules, nor existence of a genuine ∞-limit for SKY+`Y`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory

open Completion3Cell

/-! ## Packaged data -/

/-- A minimal thin tricategory record specialized to the SKY completion 2- and 3-cell layer. -/
structure SkyCompletionThinTricategory where
  /- 2-cell operations -/
  id₂ : ∀ {a b : MWObj} (f : a ⟶ b), Completion2Path f f
  vcomp₂ : ∀ {a b : MWObj} {f g h : a ⟶ b}, Completion2Path f g → Completion2Path g h → Completion2Path f h
  whiskerLeft₂ : ∀ {a b c : MWObj} (f : a ⟶ b) {g h : b ⟶ c},
      Completion2Path g h → Completion2Path (f ≫ g) (f ≫ h)
  whiskerRight₂ : ∀ {a b c : MWObj} {f g : a ⟶ b},
      Completion2Path f g → (h : b ⟶ c) → Completion2Path (f ≫ h) (g ≫ h)
  eqToHom₂ : ∀ {a b : MWObj} {f g : a ⟶ b}, f = g → Completion2Path f g

  /- 3-cell operations (thin groupoid) -/
  id₃ : ∀ {a b : MWObj} {f g : a ⟶ b} (η : Completion2Path f g), Exists3Cell η η
  vcomp₃ : ∀ {a b : MWObj} {f g : a ⟶ b} {η η' η'' : Completion2Path f g},
      Exists3Cell η η' → Exists3Cell η' η'' → Exists3Cell η η''
  inv₃ : ∀ {a b : MWObj} {f g : a ⟶ b} {η η' : Completion2Path f g},
      Exists3Cell η η' → Exists3Cell η' η

  /- named coherence 3-cells -/
  whiskerLeft_id : ∀ {a b c : MWObj} (f : a ⟶ b) (g : b ⟶ c),
      Exists3Cell (Completion2Path.whiskerLeft f (Completion2Path.id g)) (Completion2Path.id (f ≫ g))
  whiskerLeft_comp : ∀ {a b c : MWObj} (f : a ⟶ b) {g h i : b ⟶ c}
      (η : Completion2Path g h) (θ : Completion2Path h i),
      Exists3Cell (Completion2Path.whiskerLeft f (Completion2Path.vcomp η θ))
        (Completion2Path.vcomp (Completion2Path.whiskerLeft f η) (Completion2Path.whiskerLeft f θ))
  id_whiskerLeft : ∀ {a b : MWObj} {f g : a ⟶ b} (η : Completion2Path f g),
      Exists3Cell (Completion2Path.whiskerLeft (𝟙 a) η)
        (Completion2Path.vcomp (Completion2Path.id f) (Completion2Path.vcomp η (Completion2Path.id g)))
  comp_whiskerLeft : ∀ {a b c d : MWObj} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d}
      (η : Completion2Path h h'),
      Exists3Cell (Completion2Path.whiskerLeft (f ≫ g) η)
        (Completion2Path.vcomp (Completion2Path.eqToHom (LSteps.comp_assoc f g h))
          (Completion2Path.vcomp (Completion2Path.whiskerLeft f (Completion2Path.whiskerLeft g η))
            (Completion2Path.eqToHom (LSteps.comp_assoc f g h').symm)))

  id_whiskerRight : ∀ {a b c : MWObj} (f : a ⟶ b) (g : b ⟶ c),
      Exists3Cell (Completion2Path.whiskerRight (Completion2Path.id f) g) (Completion2Path.id (f ≫ g))
  comp_whiskerRight : ∀ {a b c : MWObj} {f g h : a ⟶ b}
      (η : Completion2Path f g) (θ : Completion2Path g h) (i : b ⟶ c),
      Exists3Cell (Completion2Path.whiskerRight (Completion2Path.vcomp η θ) i)
        (Completion2Path.vcomp (Completion2Path.whiskerRight η i) (Completion2Path.whiskerRight θ i))
  whiskerRight_id : ∀ {a b : MWObj} {f g : a ⟶ b} (η : Completion2Path f g),
      Exists3Cell (Completion2Path.whiskerRight η (𝟙 b))
        (Completion2Path.vcomp (Completion2Path.eqToHom (LSteps.comp_refl_right f))
          (Completion2Path.vcomp η (Completion2Path.eqToHom (LSteps.comp_refl_right g).symm)))
  whiskerRight_comp : ∀ {a b c d : MWObj} {f f' : a ⟶ b} (η : Completion2Path f f') (g : b ⟶ c) (h : c ⟶ d),
      Exists3Cell (Completion2Path.whiskerRight η (g ≫ h))
        (Completion2Path.vcomp (Completion2Path.eqToHom (LSteps.comp_assoc f g h).symm)
          (Completion2Path.vcomp (Completion2Path.whiskerRight (Completion2Path.whiskerRight η g) h)
            (Completion2Path.eqToHom (LSteps.comp_assoc f' g h))))
  whisker_assoc : ∀ {a b c d : MWObj} (f : a ⟶ b) {g g' : b ⟶ c} (η : Completion2Path g g') (h : c ⟶ d),
      Exists3Cell
        (Completion2Path.whiskerRight (Completion2Path.whiskerLeft f η) h)
        (Completion2Path.vcomp (Completion2Path.eqToHom (LSteps.comp_assoc f g h))
          (Completion2Path.vcomp (Completion2Path.whiskerLeft f (Completion2Path.whiskerRight η h))
            (Completion2Path.eqToHom (LSteps.comp_assoc f g' h).symm)))
  whisker_exchange : ∀ {a b c : MWObj} {f g : a ⟶ b} {h i : b ⟶ c}
      (η : Completion2Path f g) (θ : Completion2Path h i),
      Exists3Cell
        (Completion2Path.vcomp (Completion2Path.whiskerLeft f θ) (Completion2Path.whiskerRight η i))
        (Completion2Path.vcomp (Completion2Path.whiskerRight η h) (Completion2Path.whiskerLeft g θ))
  pentagon : ∀ {a b c d e : MWObj} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
      Exists3Cell
        (Completion2Path.vcomp
          (Completion2Path.whiskerRight (Completion2Path.eqToHom (LSteps.comp_assoc f g h)) i)
          (Completion2Path.vcomp (Completion2Path.eqToHom (LSteps.comp_assoc f (g ≫ h) i))
            (Completion2Path.whiskerLeft f (Completion2Path.eqToHom (LSteps.comp_assoc g h i)))))
        (Completion2Path.vcomp (Completion2Path.eqToHom (LSteps.comp_assoc (f ≫ g) h i))
          (Completion2Path.eqToHom (LSteps.comp_assoc f g (h ≫ i))))
  triangle : ∀ {a b c : MWObj} (f : a ⟶ b) (g : b ⟶ c),
      Exists3Cell
        (Completion2Path.vcomp (Completion2Path.eqToHom (LSteps.comp_assoc f (𝟙 b) g))
          (Completion2Path.whiskerLeft f (Completion2Path.id g)))
        (Completion2Path.whiskerRight (Completion2Path.eqToHom (LSteps.comp_refl_right f)) g)

/-- The packaged thin tricategory data for SKY completion 2- and 3-cells. -/
def skyCompletionThinTricategory : SkyCompletionThinTricategory where
  id₂ f := Completion2Path.id f
  vcomp₂ η θ := Completion2Path.vcomp η θ
  whiskerLeft₂ {a b c} f {_ _} η := Completion2Path.whiskerLeft (a := a) (b := b) (c := c) f η
  whiskerRight₂ {a b c} {_ _} η h := Completion2Path.whiskerRight (a := a) (b := b) (c := c) η h
  eqToHom₂ h := Completion2Path.eqToHom h
  id₃ η := Exists3Cell.refl η
  vcomp₃ h₁ h₂ := Exists3Cell.trans h₁ h₂
  inv₃ h := Exists3Cell.symm h

  whiskerLeft_id f g := Exists3Cell.ofCell (Completion3Cell.whisker_left_id (f := f) (g := g))
  whiskerLeft_comp {_ _ _} f {_ _ _} η θ :=
    Exists3Cell.ofCell (Completion3Cell.whisker_left_comp (f := f) (η := η) (θ := θ))
  id_whiskerLeft η := Exists3Cell.ofCell (Completion3Cell.id_whisker_left (η := η))
  comp_whiskerLeft {_ _ _ _} f g {_ _} η :=
    Exists3Cell.ofCell (Completion3Cell.comp_whisker_left (f := f) (g := g) (η := η))
  id_whiskerRight f g := Exists3Cell.ofCell (Completion3Cell.id_whisker_right (f := f) (g := g))
  comp_whiskerRight η θ i := Exists3Cell.ofCell (Completion3Cell.comp_whisker_right (η := η) (θ := θ) (i := i))
  whiskerRight_id η := Exists3Cell.ofCell (Completion3Cell.whisker_right_id (η := η))
  whiskerRight_comp η g h := Exists3Cell.ofCell (Completion3Cell.whisker_right_comp (η := η) (g := g) (h := h))
  whisker_assoc {_ _ _ _} f {_ _} η h := Exists3Cell.ofCell (Completion3Cell.whisker_assoc (f := f) (η := η) (h := h))
  whisker_exchange η θ := Exists3Cell.ofCell (Completion3Cell.whisker_exchange (η := η) (θ := θ))
  pentagon f g h i := Exists3Cell.ofCell (Completion3Cell.pentagon (f := f) (g := g) (h := h) (i := i))
  triangle f g := Exists3Cell.ofCell (Completion3Cell.triangle (f := f) (g := g))

end Category
end Combinators
end LoF
end HeytingLean
