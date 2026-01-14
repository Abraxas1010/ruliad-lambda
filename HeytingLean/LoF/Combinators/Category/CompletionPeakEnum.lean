import Mathlib.Data.List.Basic
import HeytingLean.LoF.Combinators.Category.CompletionFromCriticalPairs

/-!
# CompletionPeakEnum — computed completion generators from enumerated one-step peaks

Phase A.2 needs a “paper-faithful” *generator set* of completion 2-cells:

- enumerate one-step peaks (“critical pairs”) deterministically, and
- attach bounded join witnesses as explicit labeled paths.

This module implements that boundary for SKY by:

1. using `Comb.StepAt.peaksList t` to enumerate all ordered one-step peaks out of `t`;
2. searching for common descendants by enumerating `reachableUpTo` paths on each side; and
3. producing a list of `CompletionCells.Completion t` cells whose join legs are explicitly bounded.

The result is computation-friendly (finite, bounded) and serves as a canonical source of “completion rules”
for demos and higher-cell experiments.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

namespace CompletionPeakEnum

/-! ## Join witness enumeration (bounded) -/

/-- A “raw” bounded join witness: reachable paths from each side plus an equality of destinations. -/
structure RawJoin (u v : Comb) where
  ru : Reachable u
  rv : Reachable v
  joinEq : ru.dst = rv.dst

/-- Enumerate all raw join witnesses by searching `reachableUpTo` on each side. -/
def rawJoinsUpTo (u v : Comb) (k : Nat) : List (RawJoin u v) :=
  (reachableUpTo u k).flatMap fun ru =>
    (reachableUpTo v k).filterMap fun rv =>
      if h : ru.dst = rv.dst then
        some { ru := ru, rv := rv, joinEq := h }
      else
        none

/-- Turn a raw join witness into a `JoinWitness` by casting the right leg along `joinEq`. -/
def joinWitnessOfRaw {u v : Comb} (rj : RawJoin u v) : JoinWitness u v :=
  { w := rj.ru.dst
    left := rj.ru.path
    right := cast (congrArg (fun w => LSteps v w) rj.joinEq.symm) rj.rv.path }

/-- Enumerate all join witnesses found by searching reachability up to depth `k` from each side. -/
def joinWitnessesUpTo (u v : Comb) (k : Nat) : List (JoinWitness u v) :=
  (rawJoinsUpTo u v k).map joinWitnessOfRaw

theorem length_le_of_mem_joinWitnessesUpTo {u v : Comb} {k : Nat} {j : JoinWitness u v}
    (h : j ∈ joinWitnessesUpTo u v k) :
    j.left.length ≤ k ∧ j.right.length ≤ k := by
  classical
  rcases List.mem_map.1 h with ⟨rj, hrj, rfl⟩
  -- Unpack the raw witness: `rj` comes from some `(ru, rv)` pair in the bounded reachability lists.
  rcases (List.mem_flatMap.1 hrj) with ⟨ru, hru, hrj'⟩
  rcases (List.mem_filterMap.1 hrj') with ⟨rv, hrv, hEq⟩
  by_cases hdst : ru.dst = rv.dst
  · -- `filterMap` must have taken the `some` branch, hence `rj = ⟨ru, rv, hdst⟩`.
    have hSome : some { ru := ru, rv := rv, joinEq := hdst } = some rj := by
      simpa [hdst] using hEq
    have hrjEq : rj = { ru := ru, rv := rv, joinEq := hdst } := by
      cases hSome
      rfl
    -- Transfer the bounded-length facts from `ru` and `rv`.
    have hL : ru.path.length ≤ k := length_le_of_mem_reachableUpTo (t := u) (k := k) hru
    have hR : rv.path.length ≤ k := length_le_of_mem_reachableUpTo (t := v) (k := k) hrv
    -- Rewrite `rj` to the packed record so `joinWitnessOfRaw` exposes the correct legs.
    cases hrjEq
    constructor
    · simpa [joinWitnessOfRaw] using hL
    ·
      have hlen :
          (joinWitnessOfRaw { ru := ru, rv := rv, joinEq := hdst }).right.length = rv.path.length := by
        -- `right` is `rv.path` cast along `hdst.symm`; length is invariant under endpoint casts.
        simpa [joinWitnessOfRaw] using
          (LSteps.length_cast_congr (t := v) (h := hdst.symm) (p := rv.path))
      simpa [hlen] using hR
  · -- If the destinations differ, `filterMap` returns `none`, contradiction.
    simp [hdst] at hEq

/-! ## Completion-cell enumeration from peaks -/

/-- All bounded completion cells generated from a single one-step peak. -/
def completionsOfPeakUpTo {t : Comb} (pk : Comb.StepAt.Peak t) (k : Nat) : List (Completion t) :=
  (joinWitnessesUpTo pk.u pk.v k).map fun j =>
    { u := pk.u
      v := pk.v
      w := j.w
      left := StepAtPeak.leftLStep pk
      right := StepAtPeak.rightLStep pk
      joinLeft := j.left
      joinRight := j.right }

theorem length_le_of_mem_completionsOfPeakUpTo {t : Comb} {pk : Comb.StepAt.Peak t} {k : Nat}
    {c : Completion t} (h : c ∈ completionsOfPeakUpTo pk k) :
    c.joinLeft.length ≤ k ∧ c.joinRight.length ≤ k := by
  rcases List.mem_map.1 h with ⟨j, hj, rfl⟩
  simpa using length_le_of_mem_joinWitnessesUpTo (u := pk.u) (v := pk.v) (k := k) (j := j) hj

/-- Enumerate all bounded completion cells generated from all ordered one-step peaks out of `t`. -/
def completionsFromPeaksUpTo (t : Comb) (k : Nat) : List (Completion t) :=
  (Comb.StepAt.peaksList t).flatMap fun pk => completionsOfPeakUpTo pk k

/-- The “paper boundary” generator set: all peak completions with uniform join bound `≤ 2`. -/
abbrev completionsFromPeaksUpTo2 (t : Comb) : List (Completion t) :=
  completionsFromPeaksUpTo t 2

end CompletionPeakEnum

end Category
end Combinators
end LoF
end HeytingLean
