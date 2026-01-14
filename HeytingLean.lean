/-!
# HeytingLean — Ruliad Lambda

Machine-verified proofs for the foundations of λ-calculus ruliology.

## Key Results

- **Church-Rosser Theorem**: `Lambda.Steps.churchRosser`
- **λ ↔ SK Bridge**: `Lambda.Bridge.ofComb_simulates_step_joinable`
- **Multiway Enumeration**: `Lambda.stepEdgesList`

## Reference

Stephen Wolfram, "The Ruliology of Lambdas" (2025)
https://writings.stephenwolfram.com/2025/09/the-ruliology-of-lambdas/
-/

import HeytingLean.LoF.Combinators.Lambda.Syntax
import HeytingLean.LoF.Combinators.Lambda.ShiftSubst
import HeytingLean.LoF.Combinators.Lambda.Beta
import HeytingLean.LoF.Combinators.Lambda.Confluence
import HeytingLean.LoF.Combinators.Lambda.SKYBridge
import HeytingLean.LoF.Combinators.Lambda.Enumeration
import HeytingLean.LoF.Combinators.Lambda.Ruliology
