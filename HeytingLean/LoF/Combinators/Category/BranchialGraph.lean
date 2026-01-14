import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finset.Union
import HeytingLean.LoF.Combinators.Category.BranchialSpan

/-!
# BranchialGraph — branchial graphs (siblings share a predecessor) for SKY multiway exploration

The Wolfram-model “branchial graph” is a graph on states in a fixed time-slice of a multiway system.
For bounded explorations, a standard adjacency rule is:

> connect two states at depth `n+1` if they share a common predecessor at depth `n`.

This file formalizes that rule for SKY terms using the finite one-step enumerator `Comb.stepEdges`.

This is a *computability-friendly* notion:
- each one-step successor set is a `Finset`,
- hence slices `statesAtDepth start n` are `Finset`s,
- and branchial edges are `Finset (Sym2 Comb)` (unordered pairs).

Objectivity boundary:
- This is “branchial adjacency by shared immediate predecessor”, not a full branchial metric/geometry story.
  It is the minimal combinatorial core used by the demos and is the most portable starting point for later refinements.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

namespace Branchial

/-! ## One-step successor sets -/

/-- Unlabeled one-step successors of `s` (forget the event data). -/
def stepStates (s : Comb) : Finset Comb :=
  (Comb.stepEdges s).image Prod.snd

theorem mem_stepStates_of_mem_stepEdges {s t : Comb} {ed : Comb.EventData} :
    (ed, t) ∈ Comb.stepEdges s → t ∈ stepStates s := by
  intro h
  refine Finset.mem_image.mpr ?_
  exact ⟨(ed, t), h, rfl⟩

theorem mem_stepStates_iff {s t : Comb} :
    t ∈ stepStates s ↔ ∃ ed : Comb.EventData, (ed, t) ∈ Comb.stepEdges s := by
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨e, he, rfl⟩
    rcases e with ⟨ed, u⟩
    exact ⟨ed, by simpa using he⟩
  · rintro ⟨ed, hed⟩
    exact mem_stepStates_of_mem_stepEdges (s := s) (t := t) (ed := ed) hed

/-! ## Branchial edges among siblings -/

/-- Unordered sibling-pairs among the children of a state (self-pairs removed). -/
def siblingEdges (s : Comb) : Finset (Sym2 Comb) :=
  ((stepStates s).sym2).filter (fun z => ¬ z.IsDiag)

theorem mem_siblingEdges_iff {parent t u : Comb} :
    s(t, u) ∈ siblingEdges parent ↔
      t ∈ stepStates parent ∧ u ∈ stepStates parent ∧ t ≠ u := by
  classical
  constructor
  · intro h
    have h0 := h
    -- `simp` normalizes membership in `sym2` to endpoint membership.
    simp [siblingEdges] at h0
    rcases h0 with ⟨htu, hne⟩
    rcases htu with ⟨ht, hu⟩
    exact ⟨ht, hu, hne⟩
  · rintro ⟨ht, hu, hne⟩
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, ?_⟩
    · exact (Finset.mk_mem_sym2_iff (s := stepStates parent) (a := t) (b := u)).2 ⟨ht, hu⟩
    · -- Not on the diagonal: `s(t,u)` is diagonal iff `t = u`.
      intro hdiag
      have : t = u := (Sym2.mk_isDiag_iff (x := t) (y := u)).1 hdiag
      exact hne this

theorem branchialAt_one_of_mem_siblingEdges {parent t u : Comb} :
    s(t, u) ∈ siblingEdges parent → BranchialAt 1 t u := by
  intro h
  rcases (mem_siblingEdges_iff (parent := parent) (t := t) (u := u)).1 h with ⟨ht, hu, _hne⟩
  rcases (mem_stepStates_iff (s := parent) (t := t)).1 ht with ⟨edL, hedL⟩
  rcases (mem_stepStates_iff (s := parent) (t := u)).1 hu with ⟨edR, hedR⟩
  refine ⟨parent, ?_, ?_⟩
  · refine ⟨LSteps.trans { ed := edL, mem := hedL } (.refl t), ?_⟩
    simp [LSteps.length]
  · refine ⟨LSteps.trans { ed := edR, mem := hedR } (.refl u), ?_⟩
    simp [LSteps.length]

noncomputable def branchialSpanOfMemSiblingEdges {parent t u : Comb}
    (h : s(t, u) ∈ siblingEdges parent) : BranchialSpan t u := by
  rcases (mem_siblingEdges_iff (parent := parent) (t := t) (u := u)).1 h with ⟨ht, hu, _hne⟩
  -- `t ∈ stepStates parent` only gives existence of a label in `Prop`, so we use classical choice.
  have ht' : ∃ ed : Comb.EventData, (ed, t) ∈ Comb.stepEdges parent :=
    (mem_stepStates_iff (s := parent) (t := t)).1 ht
  have hu' : ∃ ed : Comb.EventData, (ed, u) ∈ Comb.stepEdges parent :=
    (mem_stepStates_iff (s := parent) (t := u)).1 hu
  let edL : Comb.EventData := Classical.choose ht'
  have hedL : (edL, t) ∈ Comb.stepEdges parent := Classical.choose_spec ht'
  let edR : Comb.EventData := Classical.choose hu'
  have hedR : (edR, u) ∈ Comb.stepEdges parent := Classical.choose_spec hu'
  exact
    { ancestor := parent
      pathToLeft := LSteps.trans { ed := edL, mem := hedL } (.refl t)
      pathToRight := LSteps.trans { ed := edR, mem := hedR } (.refl u) }

/-! ## Time slices and branchial graphs at depth -/

/-- The (bounded) time slice: states reachable in exactly `n` steps from `start`. -/
def statesAtDepth (start : Comb) : Nat → Finset Comb
  | 0 => {start}
  | n + 1 => (statesAtDepth start n).biUnion (fun s => stepStates s)

theorem mem_statesAtDepth_succ_iff {start : Comb} {n : Nat} {t : Comb} :
    t ∈ statesAtDepth start (n + 1) ↔ ∃ s ∈ statesAtDepth start n, t ∈ stepStates s := by
  classical
  simp [statesAtDepth]

/-- Branchial edges among depth-`n` states: siblings share a predecessor at depth `n-1`. -/
def branchialEdgesAtDepth (start : Comb) : Nat → Finset (Sym2 Comb)
  | 0 => ∅
  | n + 1 => (statesAtDepth start n).biUnion (fun s => siblingEdges s)

theorem mem_branchialEdgesAtDepth_succ_iff {start : Comb} {n : Nat} {z : Sym2 Comb} :
    z ∈ branchialEdgesAtDepth start (n + 1) ↔
      ∃ s ∈ statesAtDepth start n, z ∈ siblingEdges s := by
  classical
  simp [branchialEdgesAtDepth]

end Branchial

end Category
end Combinators
end LoF
end HeytingLean
