import HeytingLean.LoF.Combinators.Rewriting.StepAt

/-!
# StepAtCompute — executable application of labeled redex events (and cube enumeration)

`Comb.StepAt` is a propositional “step at a position” relation. For demos and bounded exploration
we also want a **computable** operation:

* `applyEvent? t ed` tries to apply the labeled event `ed : EventData` to `t`.

Using this we provide a small bounded enumerator of “commuting cubes” coming from **three pairwise
disjoint** one-step events out of a term.

Objectivity boundary:
* This is a *local* computation layer. It does not claim global confluence or termination.
-/

namespace HeytingLean
namespace LoF

namespace Comb

open Dir RuleTag

/-! ## Executing a labeled event -/

private def applyAtRoot? (t : Comb) (r : RuleTag) : Option Comb :=
  match rootStep? t with
  | some (r', u) => if r' = r then some u else none
  | none => none

private def applyAtPath? : Comb → RuleTag → RedexPath → Option Comb
  | t, r, [] => applyAtRoot? t r
  | Comb.app f a, r, Dir.L :: p => (applyAtPath? f r p).map (fun f' => Comb.app f' a)
  | Comb.app f a, r, Dir.R :: p => (applyAtPath? a r p).map (fun a' => Comb.app f a')
  | _t, _r, _p => none

/-- Try to apply the labeled one-step event `ed` to a term `t`.

Returns `none` if:
* the redex path is invalid (walks past a non-`app` node), or
* the rule-tag does not match the root redex at that position, or
* there is no root redex at that position. -/
def applyEvent? (t : Comb) (ed : EventData) : Option Comb :=
  applyAtPath? t ed.rule ed.path

/-! ## Disjointness of paths (computable) -/

/-- Boolean test: `p` is a prefix of `q`. -/
def prefixB (p q : RedexPath) : Bool :=
  p.isPrefixOf q

/-- Boolean test: redexes at `p` and `q` are disjoint (neither is a prefix of the other). -/
def disjointB (p q : RedexPath) : Bool :=
  (!prefixB p q) && (!prefixB q p)

/-! ## Cube enumeration from disjoint events -/

private def pairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => (xs.map (fun y => (x, y))) ++ pairs xs

private def triples {α : Type} : List α → List (α × α × α)
  | [] => []
  | x :: xs =>
      ((pairs xs).map (fun yz => (x, yz.1, yz.2))) ++ triples xs

/-- Data for a “commuting cube” formed by three pairwise disjoint events.

Vertices:
* `v000 = t`
* `v100 = apply e₁`
* `v010 = apply e₂`
* `v001 = apply e₃`
* `v110 = apply e₁ then e₂`
* `v101 = apply e₁ then e₃`
* `v011 = apply e₂ then e₃`
* `v111 = apply e₁ then e₂ then e₃` -/
structure CubeData where
  e₁ : EventData
  e₂ : EventData
  e₃ : EventData
  v100 : Comb
  v010 : Comb
  v001 : Comb
  v110 : Comb
  v101 : Comb
  v011 : Comb
  v111 : Comb
  deriving Repr

private def cubeDataOf? (t : Comb) (e₁ e₂ e₃ : EventData) : Option CubeData := do
  let v100 ← applyEvent? t e₁
  let v010 ← applyEvent? t e₂
  let v001 ← applyEvent? t e₃
  let v110 ← applyEvent? v100 e₂
  let v101 ← applyEvent? v100 e₃
  let v011 ← applyEvent? v010 e₃
  let v111 ← applyEvent? v110 e₃
  pure { e₁, e₂, e₃, v100, v010, v001, v110, v101, v011, v111 }

/-- Enumerate all computable cubes out of a term by picking three pairwise-disjoint events from
`stepEdgesList t` and executing them. -/
def cubesList (t : Comb) : List CubeData :=
  let events : List EventData := (stepEdgesList t).map Prod.fst
  (triples events).filterMap fun (e₁, e₂, e₃) =>
    if disjointB e₁.path e₂.path && disjointB e₁.path e₃.path && disjointB e₂.path e₃.path then
      cubeDataOf? t e₁ e₂ e₃
    else
      none

end Comb

end LoF
end HeytingLean
