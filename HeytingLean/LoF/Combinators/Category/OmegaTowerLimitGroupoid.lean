import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Groupoid
import HeytingLean.LoF.Combinators.Category.Groupoid
import HeytingLean.LoF.Combinators.Category.OmegaTowerLimit
import HeytingLean.LoF.Combinators.Category.PathTruncation
import HeytingLean.LoF.Combinators.Topos.StepsSite
import HeytingLean.LoF.Combinators.Topos.Truncation

/-!
# OmegaTowerLimitGroupoid — a strict ω-groupoid completion + truncation bridge (Phase A.4)

This file addresses the remaining “semantic gap” items in Phase A.4:

1. **A mathematically meaningful ω-groupoid exists (formal inverses)**:
   starting from the Mathlib free groupoid on the SKY one-step quiver (`MWFreeGroupoid`),
   we iterate the Arrow construction to obtain a strict cubical tower of groupoids,
   and show its ω-limit `TowerLimit` is itself a `Groupoid`.

2. **Closure/nucleus only sees truncated path data**:
   the topos layer is built on thin reachability `Comb.Steps`, which is mere existence of labeled
   multiway paths (`Trunc`/`Nonempty` of `LSteps`), recorded in `PathTruncation`.

Objectivity boundary:
- The “inverses” are **formal** (groupoid completion), not computational SKY reductions.
- The truncation connection is the Mathlib-native one: `Steps` is mere existence of `LSteps`,
  and sieve-closure is a kernel quotient of an idempotent reflector (see `Topos/Truncation.lean`).
- We do **not** claim HoTT HIT truncation or a homotopy-hypothesis equivalence here.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-! ## Arrow of a groupoid is a groupoid -/

noncomputable instance {C : Type*} [Groupoid C] : Groupoid (Arrow C) :=
  CategoryTheory.Groupoid.ofIsIso (C := Arrow C) (all_is_iso := by
    intro X Y f
    -- In a groupoid, both sides of the commutative square are isomorphisms.
    haveI : IsIso f.left := by infer_instance
    haveI : IsIso f.right := by infer_instance
    exact Arrow.isIso_of_isIso_left_of_isIso_right (ff := f))

/-! ## TowerLimit of groupoids is a groupoid -/

namespace TowerLimit

variable {T : CatTower}

noncomputable instance instGroupoid [∀ n, IsGroupoid (T.Obj n)] : Groupoid (TowerLimit T) where
  inv {X Y} f :=
    { app := fun n => inv (f.app n)
      comm := by
        intro n
        -- Invert the commutativity condition of `f` at level `n`.
        have h :=
          congrArg (fun k => inv k) (f.comm n).symm
        -- Normalize inverses of composites and `eqToHom` coercions.
        -- Also rewrite `inv (drop.map g)` as `drop.map (inv g)`.
        simpa [Category.assoc, Functor.map_inv, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc] using h.symm }
  inv_comp {X Y} f := by
    apply TowerLimit.Hom.ext
    intro n
    simp
  comp_inv {X Y} f := by
    apply TowerLimit.Hom.ext
    intro n
    simp

end TowerLimit

/-! ## The strict Arrow tower on the SKY free groupoid (formal ω-groupoid) -/

namespace FormalOmegaGroupoid

/-!
We follow the pattern from `NFoldCategoryArrow.lean`: package the previous stage together with its
`Groupoid` structure, so the next stage `Arrow _` elaborates without leaving unresolved typeclass
metavariables.
-/

/-- A small “groupoid package” for defining the Arrow tower recursively. -/
structure GroupoidPkg where
  Obj : Type _
  inst : Groupoid Obj

attribute [instance] GroupoidPkg.inst

/-- The strict Arrow tower starting from the SKY free groupoid completion. -/
noncomputable def MWGCatPkg : Nat → GroupoidPkg
  | 0 => { Obj := MWFreeGroupoid, inst := by infer_instance }
  | Nat.succ n =>
      let C := MWGCatPkg n
      letI : Groupoid C.Obj := C.inst
      { Obj := Arrow C.Obj, inst := by infer_instance }

/-- Underlying object type at level `n` of the formal groupoid tower. -/
abbrev MWGCat (n : Nat) : Type _ := (MWGCatPkg n).Obj

noncomputable instance (n : Nat) : Groupoid (MWGCat n) :=
  (MWGCatPkg n).inst

@[simp] theorem MWGCat_zero : MWGCat 0 = MWFreeGroupoid := rfl
@[simp] theorem MWGCat_succ (n : Nat) : MWGCat (Nat.succ n) = Arrow (MWGCat n) := rfl

/-- One-step left boundary projection in the groupoid Arrow tower. -/
noncomputable abbrev MWGDropLeft (n : Nat) : MWGCat (n + 1) ⥤ MWGCat n :=
  Arrow.leftFunc (C := MWGCat n)

/-- One-step right boundary projection in the groupoid Arrow tower. -/
noncomputable abbrev MWGDropRight (n : Nat) : MWGCat (n + 1) ⥤ MWGCat n :=
  Arrow.rightFunc (C := MWGCat n)

/-- The formal ω-groupoid tower using the left boundary projection. -/
noncomputable def MWGLeftTower : CatTower where
  Obj := MWGCat
  inst := fun n => by infer_instance
  drop := fun n => MWGDropLeft n

/-- The formal ω-groupoid tower using the right boundary projection. -/
noncomputable def MWGRightTower : CatTower where
  Obj := MWGCat
  inst := fun n => by infer_instance
  drop := fun n => MWGDropRight n

abbrev OmegaLeft : Type := TowerLimit MWGLeftTower
abbrev OmegaRight : Type := TowerLimit MWGRightTower

noncomputable instance : Groupoid OmegaLeft := by
  dsimp [OmegaLeft]
  infer_instance

noncomputable instance : Groupoid OmegaRight := by
  dsimp [OmegaRight]
  infer_instance

end FormalOmegaGroupoid

/-! ## Truncation boundary: thin reachability is mere existence of labeled paths -/

namespace TruncationBridge

open PathTruncation
open HeytingLean.LoF.Combinators.Topos

/-- Thin reachability is mere existence of a labeled path (restating `PathTruncation`). -/
theorem steps_iff_nonempty_lsteps (t u : Comb) :
    Comb.Steps t u ↔ Nonempty (LSteps t u) :=
  PathTruncation.steps_iff_nonempty_lsteps (t := t) (u := u)

/-- `Trunc (LSteps t u)` implies thin reachability (constructive). -/
theorem steps_of_trunc_lsteps (t u : Comb) : Trunc (LSteps t u) → Comb.Steps t u :=
  PathTruncation.steps_of_trunc_lsteps (t := t) (u := u)

/-- Kernel-quotient by closure is equivalent to closed sieves (specialized to the SKY reachability site). -/
noncomputable abbrev closeQuotEquivClosed_stepsDense (X : StepsCat) :
    CloseQuot (C := StepsCat) (J := stepsDenseTopology) X ≃ ClosedSieve (C := StepsCat) stepsDenseTopology X :=
  closeQuotEquivClosed (C := StepsCat) (J := stepsDenseTopology) X

end TruncationBridge

end Category
end Combinators
end LoF
end HeytingLean
