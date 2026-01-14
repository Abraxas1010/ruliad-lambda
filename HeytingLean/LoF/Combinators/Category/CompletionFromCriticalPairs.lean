import HeytingLean.LoF.Combinators.Category.Completion2Cell
import HeytingLean.LoF.Combinators.Rewriting.CriticalPairs

/-!
# CompletionFromCriticalPairs — turning `StepAt` peaks into completion cells/2-cells

`Comb.StepAt` is a position-aware one-step reduction for SKY.  A one-step peak

```
    t
  ↙   ↘
 u     v
```

is packaged as `Comb.StepAt.Peak t`.

This file connects that rewriting-level object back to the multiway category layer by:

- converting a positioned step `StepAt t r p u` into a labeled multiway edge `LStep t u` with label
  `⟨r, p⟩`, and
- extracting (existentially) a `CompletionCells.Completion t` (and hence a `Completion2Cell`) using
  the already-proved local confluence/completion theorems.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-- Convert a positioned one-step reduction to a labeled multiway step with the matching label. -/
def lStepOfStepAt {t u : Comb} {r : RuleTag} {p : RedexPath} (h : Comb.StepAt t r p u) : LStep t u :=
  { ed := { rule := r, path := p }
    mem := (Comb.StepAt.stepAt_iff_mem_stepEdges (t := t) (r := r) (p := p) (u := u)).1 h }

namespace StepAtPeak

/-- The left labeled edge of a one-step peak. -/
def leftLStep {t : Comb} (pk : Comb.StepAt.Peak t) : LStep t pk.u :=
  lStepOfStepAt pk.left

/-- The right labeled edge of a one-step peak. -/
def rightLStep {t : Comb} (pk : Comb.StepAt.Peak t) : LStep t pk.v :=
  lStepOfStepAt pk.right

/-- Any one-step peak yields a completion cell whose join legs have length ≤ 2. -/
theorem exists_completion_len_le2 {t : Comb} (pk : Comb.StepAt.Peak t) :
    ∃ c : Completion t, c.joinLeft.length ≤ 2 ∧ c.joinRight.length ≤ 2 := by
  simpa [leftLStep, rightLStep] using
    (Completion.exists_of_fork_len_le2 (t := t) (leftLStep pk) (rightLStep pk))

/-- Any one-step peak yields a completion 2-cell (as witness data) between its completed boundaries. -/
theorem exists_completion2Cell {t : Comb} (pk : Comb.StepAt.Peak t) :
    ∃ c : Completion t, Nonempty (Completion2Cell (Completion.leftPath c) (Completion.rightPath c)) := by
  have h := Completion.nonempty_of_fork (t := t) (leftLStep pk) (rightLStep pk)
  rcases h with ⟨c⟩
  refine ⟨c, ?_⟩
  exact ⟨Completion2Cell.of_completion c⟩

end StepAtPeak

end Category
end Combinators
end LoF
end HeytingLean

