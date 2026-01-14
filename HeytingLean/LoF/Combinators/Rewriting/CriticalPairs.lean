import HeytingLean.LoF.Combinators.Rewriting.LocalConfluenceBounded

/-!
# CriticalPairs — packaging one-step peaks as “critical”/completion-rule objects

This file is a small, paper-shaped wrapper around the already-proved `StepAt` local confluence API.

In term rewriting, “critical pairs” are classically used to describe overlaps of redexes and the
completion rules needed to resolve those overlaps. For SKY rewriting we work with the explicit
redex-position predicate `Comb.StepAt`.

This module:

- packages a one-step peak `t ↦ u` and `t ↦ v` as a `StepAt.Peak t`;
- defines the overlap/disjoint predicates on the two redex paths; and
- exposes joinability results (including the uniform `≤ 2` join bound) as “completion-rule witnesses”.
- provides a deterministic enumeration of all one-step peaks out of a term `t`
  (by pairing the multiway edge enumerator `stepEdgesList t` with itself).

Objective boundary:
- The joinability results are proved in `LocalConfluence.lean` / `LocalConfluenceBounded.lean`.
- This file does not attempt to derive a finite critical-pair set or a Knuth–Bendix completion
  procedure; it only packages the already-proved primitives.
-/

namespace HeytingLean
namespace LoF

namespace Comb

open Dir RuleTag

namespace StepAt

open RedexPath

/-- A one-step peak (fork) of positioned reductions out of a common source `t`. -/
structure Peak (t : Comb) where
  u : Comb
  v : Comb
  r₁ : RuleTag
  p₁ : RedexPath
  r₂ : RuleTag
  p₂ : RedexPath
  left : StepAt t r₁ p₁ u
  right : StepAt t r₂ p₂ v

namespace Peak

/-- The redex paths are disjoint (the two one-step reductions are independent). -/
def Disjoint {t : Comb} (pk : Peak t) : Prop :=
  RedexPath.Disjoint pk.p₁ pk.p₂

/-- The redex paths overlap (one is a prefix of the other). -/
def Overlaps {t : Comb} (pk : Peak t) : Prop :=
  RedexPath.Prefix pk.p₁ pk.p₂ ∨ RedexPath.Prefix pk.p₂ pk.p₁

/-- Any one-step `StepAt` peak is joinable (local confluence). -/
theorem joinable {t : Comb} (pk : Peak t) :
    ∃ w : Comb, Comb.Steps pk.u w ∧ Comb.Steps pk.v w := by
  exact StepAt.local_confluence (t := t) (u := pk.u) (v := pk.v) pk.left pk.right

/-- Any one-step `StepAt` peak is joinable with a uniform bound of at most two steps on each side. -/
theorem joinable_upTo2 {t : Comb} (pk : Peak t) :
    ∃ w : Comb, Comb.StepsUpTo2 pk.u w ∧ Comb.StepsUpTo2 pk.v w := by
  exact StepAt.local_confluence_upTo2 (t := t) (u := pk.u) (v := pk.v) pk.left pk.right

/-- In the disjoint (independent redex) case, the peak commutes at the `StepAt` level. -/
theorem commute_of_disjoint {t : Comb} (pk : Peak t) (hdisj : pk.Disjoint) :
    ∃ w : Comb, StepAt pk.u pk.r₂ pk.p₂ w ∧ StepAt pk.v pk.r₁ pk.p₁ w := by
  exact StepAt.commute_of_disjoint (t := t) (u := pk.u) (v := pk.v) pk.left pk.right hdisj

end Peak

/-- Enumerated one-step edges out of `t`, bundled with membership proofs. -/
abbrev Edge (t : Comb) : Type :=
  {e : (EventData × Comb) // e ∈ stepEdgesList t}

namespace Edge

def ed {t : Comb} (e : Edge t) : EventData := e.1.1
def dst {t : Comb} (e : Edge t) : Comb := e.1.2

/-- Any enumerated edge yields a positioned one-step reduction. -/
def stepAt {t : Comb} (e : Edge t) : StepAt t (ed e).rule (ed e).path (dst e) :=
  match e with
  | ⟨(ed0, u0), hmem⟩ =>
      StepAt.stepAt_of_stepEdgesList (t := t) (ed := ed0) (u := u0) hmem

end Edge

/-- Deterministic list of all one-step edges out of `t`, carrying membership proofs. -/
def edgeList (t : Comb) : List (Edge t) :=
  (stepEdgesList t).attach

namespace Peak

/-- Build a `Peak` from a pair of enumerated edges out of the same source. -/
def ofEdges {t : Comb} (e₁ e₂ : Edge t) : Peak t :=
  { u := Edge.dst e₁
    v := Edge.dst e₂
    r₁ := (Edge.ed e₁).rule
    p₁ := (Edge.ed e₁).path
    r₂ := (Edge.ed e₂).rule
    p₂ := (Edge.ed e₂).path
    left := Edge.stepAt e₁
    right := Edge.stepAt e₂ }

end Peak

/-- Enumerate all ordered edge-pairs from a fixed edge list `es`. -/
private def peaksListFrom {t : Comb} (es : List (Edge t)) : List (Peak t) :=
  let rec go : List (Edge t) → List (Peak t)
    | [] => []
    | e₁ :: es' => (es.map (fun e₂ => Peak.ofEdges e₁ e₂)) ++ go es'
  go es

/-- Enumerate all **ordered** one-step peaks out of `t`. -/
def peaksList (t : Comb) : List (Peak t) :=
  peaksListFrom (edgeList t)

namespace Peak

/-- Any explicit `StepAt` peak can be realized by two enumerated edges with matching labels. -/
theorem exists_edges {t : Comb} (pk : Peak t) :
    ∃ e₁ e₂ : Edge t,
      Edge.ed e₁ = { rule := pk.r₁, path := pk.p₁ } ∧ Edge.dst e₁ = pk.u ∧
      Edge.ed e₂ = { rule := pk.r₂, path := pk.p₂ } ∧ Edge.dst e₂ = pk.v := by
  let e₁ : Edge t :=
    ⟨({ rule := pk.r₁, path := pk.p₁ }, pk.u), StepAt.mem_stepEdgesList_of_stepAt pk.left⟩
  let e₂ : Edge t :=
    ⟨({ rule := pk.r₂, path := pk.p₂ }, pk.v), StepAt.mem_stepEdgesList_of_stepAt pk.right⟩
  refine ⟨e₁, e₂, ?_, ?_, ?_, ?_⟩ <;> rfl

end Peak

end StepAt

end Comb
end LoF
end HeytingLean
