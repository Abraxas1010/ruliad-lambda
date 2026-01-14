import HeytingLean.LoF.Combinators.Category.MultiwayCategory
import HeytingLean.LoF.Combinators.Topos.StepsSite

/-!
# BranchialSpan — common-ancestor witnesses for branchial structure

In multiway systems, the branchial relation is often phrased as:

> two states are “branchially related” if they share a common ancestor.

This file records the minimal *witness* data needed for that notion, expressed
using the non-thin labeled path type `LSteps`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-! ## Unbounded spans -/

/-- A branchial span between `t` and `u`: an ancestor together with two reduction paths. -/
structure BranchialSpan (t u : Comb) where
  ancestor : Comb
  pathToLeft : LSteps ancestor t
  pathToRight : LSteps ancestor u

namespace BranchialSpan

@[simp] def refl (t : Comb) : BranchialSpan t t :=
  { ancestor := t
    pathToLeft := .refl t
    pathToRight := .refl t }

def symm {t u : Comb} (s : BranchialSpan t u) : BranchialSpan u t :=
  { ancestor := s.ancestor
    pathToLeft := s.pathToRight
    pathToRight := s.pathToLeft }

/-- Internal helper: transitivity of propositional reachability `Comb.Steps`. -/
private theorem steps_transitive {t u v : Comb} : Steps t u → Steps u v → Steps t v := by
  intro htu huv
  induction htu with
  | refl _ =>
      simpa using huv
  | trans hstep hsteps ih =>
      exact Steps.trans hstep (ih huv)

/-- Two branchial spans are considered equivalent if their ancestors are *mutually reachable*
(isomorphic in the thin reachability category). -/
def AncestorEqv {t u : Comb} (s₁ s₂ : BranchialSpan t u) : Prop :=
  Steps s₁.ancestor s₂.ancestor ∧ Steps s₂.ancestor s₁.ancestor

namespace AncestorEqv

open CategoryTheory

/-- Build an isomorphism in the thin reachability category from mutual reachability. -/
def isoOfSteps {a b : Comb} (hab : Steps a b) (hba : Steps b a) : a ≅ b :=
  { hom := CategoryTheory.homOfLE hab
    inv := CategoryTheory.homOfLE hba
    hom_inv_id := by
      -- Homs in a preorder category are subsingletons.
      apply Subsingleton.elim
    inv_hom_id := by
      apply Subsingleton.elim }

/-- In a preorder category, being isomorphic is equivalent to mutual reachability. -/
theorem nonempty_iso_iff_steps (a b : Comb) :
    Nonempty (a ≅ b) ↔ (Steps a b ∧ Steps b a) := by
  constructor
  · intro h
    rcases h with ⟨i⟩
    refine ⟨CategoryTheory.leOfHom i.hom, CategoryTheory.leOfHom i.inv⟩
  · rintro ⟨hab, hba⟩
    exact ⟨isoOfSteps hab hba⟩

/-- The chosen equivalence relation on ancestors is precisely “isomorphic in the thin category”. -/
theorem iff_nonempty_iso {t u : Comb} (s₁ s₂ : BranchialSpan t u) :
    AncestorEqv s₁ s₂ ↔ Nonempty (s₁.ancestor ≅ s₂.ancestor) := by
  simpa [AncestorEqv] using (nonempty_iso_iff_steps s₁.ancestor s₂.ancestor).symm

theorem refl {t u : Comb} (s : BranchialSpan t u) : AncestorEqv s s :=
  ⟨Steps.refl _, Steps.refl _⟩

theorem symm {t u : Comb} {s₁ s₂ : BranchialSpan t u} :
    AncestorEqv s₁ s₂ → AncestorEqv s₂ s₁ := by
  intro h
  exact ⟨h.2, h.1⟩

theorem trans {t u : Comb} {s₁ s₂ s₃ : BranchialSpan t u} :
    AncestorEqv s₁ s₂ → AncestorEqv s₂ s₃ → AncestorEqv s₁ s₃ := by
  intro h12 h23
  refine ⟨?_, ?_⟩
  · exact steps_transitive h12.1 h23.1
  · exact steps_transitive h23.2 h12.2

end AncestorEqv

/-- The `Setoid` on branchial spans induced by ancestor mutual reachability. -/
def ancestorSetoid (t u : Comb) : Setoid (BranchialSpan t u) where
  r := AncestorEqv
  iseqv := by
    refine ⟨AncestorEqv.refl, AncestorEqv.symm, AncestorEqv.trans⟩

end BranchialSpan

/-! ## Depth-bounded branchial relation -/

/-- Depth-bounded branchial relatedness: `t` and `u` share some ancestor with
paths of **exact** length `n` to each. -/
def BranchialAt (n : Nat) (t u : Comb) : Prop :=
  ∃ a : Comb,
    (∃ p : LSteps a t, p.length = n) ∧ (∃ q : LSteps a u, q.length = n)

namespace BranchialAt

theorem refl0 (t : Comb) : BranchialAt 0 t t := by
  refine ⟨t, ?_, ?_⟩
  · refine ⟨.refl t, rfl⟩
  · refine ⟨.refl t, rfl⟩

theorem symm {n : Nat} {t u : Comb} : BranchialAt n t u → BranchialAt n u t := by
  rintro ⟨a, ⟨p, hp⟩, ⟨q, hq⟩⟩
  exact ⟨a, ⟨q, hq⟩, ⟨p, hp⟩⟩

end BranchialAt

end Category
end Combinators
end LoF
end HeytingLean
