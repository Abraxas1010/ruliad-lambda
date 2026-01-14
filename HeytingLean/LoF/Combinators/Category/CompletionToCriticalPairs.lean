import HeytingLean.LoF.Combinators.Category.CompletionCells
import HeytingLean.LoF.Combinators.Rewriting.CriticalPairs

/-!
# CompletionToCriticalPairs — extracting a `StepAt` peak from a completion cell

`CompletionFromCriticalPairs.lean` bridges *from* the rewriting-level `Comb.StepAt.Peak t`
to the multiway category layer (labeled edges and completion cells).

For the “paper-faithful generator” story in Phase A.2 it is also useful to go the other way:
any completion cell already carries two labeled one-step edges out of the same source, hence it
determines an underlying positioned peak.

This module provides that reverse map:

- `LStep.toStepAt` turns a labeled one-step edge back into a `Comb.StepAt` witness, and
- `Completion.toPeak` forgets a completion cell to its underlying one-step `StepAt` peak.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-- Convert a labeled multiway one-step edge back into a positioned `StepAt` witness. -/
def LStep.toStepAt {t u : Comb} (s : LStep t u) : Comb.StepAt t s.ed.rule s.ed.path u :=
  Comb.StepAt.stepAt_of_stepEdges (t := t) (ed := s.ed) (u := u) s.mem

namespace Completion

/-- The one-step `StepAt` peak underlying a completion cell: its two boundary one-step reductions. -/
def toPeak {t : Comb} (c : Completion t) : Comb.StepAt.Peak t :=
  { u := c.u
    v := c.v
    r₁ := c.left.ed.rule
    p₁ := c.left.ed.path
    r₂ := c.right.ed.rule
    p₂ := c.right.ed.path
    left := c.left.toStepAt
    right := c.right.toStepAt }

end Completion

end Category
end Combinators
end LoF
end HeytingLean

