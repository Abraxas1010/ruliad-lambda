import Mathlib.Data.Quot
import HeytingLean.LoF.Combinators.Category.MultiwayCategory

/-!
# PathTruncation — bridging labeled multiway paths and thin reachability

The SKY multiway development uses **two** related notions of “path”:

* `Comb.Steps t u : Prop` — thin reachability (a preorder, used by the topos layer);
* `LSteps t u : Type` — explicit labeled multi-step paths (non-thin, used by multiway semantics).

This file makes the bridge precise:

* `Comb.Steps t u ↔ Nonempty (LSteps t u)` (mere existence of labeled paths),
* and, classically, `Comb.Steps t u → Trunc (LSteps t u)` as a Type-valued “mere existence”.

We keep the direction `Trunc (LSteps t u) → Comb.Steps t u` constructive, since elimination out of
`Trunc` into `Prop` is valid and does not require choice.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

namespace PathTruncation

/-! ## One-step bridge: propositional `Step` ⇒ existence of a labeled `LStep` -/

theorem nonempty_lstep_of_step {t u : Comb} (h : Comb.Step t u) : Nonempty (LStep t u) := by
  rcases Comb.stepEdges_complete (t := t) (u := u) h with ⟨ed, hmem⟩
  exact ⟨{ ed := ed, mem := hmem }⟩

/-! ## Multi-step bridge: thin reachability ⇔ mere existence of labeled paths -/

theorem nonempty_lsteps_of_steps {t u : Comb} (h : Comb.Steps t u) : Nonempty (LSteps t u) := by
  induction h with
  | refl t =>
      exact ⟨.refl t⟩
  | trans hstep hsteps ih =>
      rename_i t u v
      rcases nonempty_lstep_of_step (t := t) (u := u) hstep with ⟨s⟩
      rcases ih with ⟨p⟩
      exact ⟨.trans s p⟩

theorem steps_of_nonempty_lsteps {t u : Comb} : Nonempty (LSteps t u) → Comb.Steps t u := by
  rintro ⟨p⟩
  exact LSteps.toSteps p

theorem steps_iff_nonempty_lsteps {t u : Comb} : Comb.Steps t u ↔ Nonempty (LSteps t u) :=
  ⟨nonempty_lsteps_of_steps (t := t) (u := u), steps_of_nonempty_lsteps (t := t) (u := u)⟩

/-! ## `Trunc` bridge (Type-valued “mere existence”) -/

theorem steps_of_trunc_lsteps {t u : Comb} : Trunc (LSteps t u) → Comb.Steps t u := by
  intro q
  refine Trunc.induction_on q ?_
  intro p
  exact LSteps.toSteps p

noncomputable def trunc_lsteps_of_steps {t u : Comb} (h : Comb.Steps t u) : Trunc (LSteps t u) := by
  classical
  have hNE : Nonempty (LSteps t u) := nonempty_lsteps_of_steps (t := t) (u := u) h
  exact Trunc.mk (Classical.choice hNE)

end PathTruncation

end Category
end Combinators
end LoF
end HeytingLean

