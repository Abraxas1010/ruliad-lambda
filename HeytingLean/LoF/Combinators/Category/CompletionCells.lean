import HeytingLean.LoF.Combinators.Category.MultiwayCategory
import HeytingLean.LoF.Combinators.Category.PathTruncation
import HeytingLean.LoF.Combinators.Rewriting.LocalConfluence
import HeytingLean.LoF.Combinators.Rewriting.LocalConfluenceBounded

/-!
# CompletionCells — local “diamond” completion witnesses (2-cells, bounded)

The Arsiwalla et al. multiway-homotopy program generates 2-cells from *completion rules*:
when two rewrite paths diverge, a completion rule witnesses that they can be joined.

SKY with `Y` is non-terminating, and this module focuses on **computable, bounded** completion
witnesses (rather than assuming any global confluence theorem).  In particular, it is still useful
to search for small diamonds and bounded joins even when one-step peaks are joinable by proof
(see `LoF/Combinators/Rewriting/LocalConfluence.lean`).  Concretely, we:

1. define a **local diamond witness** `Diamond t` (a 1-step fork followed by a 1-step join),
2. provide a **bounded search** `findDiamond1? t` that finds any such diamond using the
   enumerator `Comb.stepEdges`.

This is a minimal, computation-friendly notion of “completion 2-cell” that can be iterated later
to build larger homotopies.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-! ## Diamonds -/

/-- A local completion square (“diamond”) from a term `t`:

```
      t
    ↙   ↘
   u     v
    ↘   ↙
      w
```

All edges are **one-step labeled reductions** (`LStep`). -/
structure Diamond (t : Comb) where
  (u v w₁ w₂ : Comb)
  left : LStep t u
  right : LStep t v
  joinLeft : LStep u w₁
  joinRight : LStep v w₂
  joinEq : w₁ = w₂

namespace Diamond

/-- The left 2-step path `t ⟶ u ⟶ w`. -/
def leftPath {t : Comb} (d : Diamond t) : LSteps t d.w₁ :=
  .trans d.left (.trans d.joinLeft (.refl d.w₁))

/-- The right 2-step path `t ⟶ v ⟶ w`. -/
def rightPath {t : Comb} (d : Diamond t) : LSteps t d.w₂ :=
  .trans d.right (.trans d.joinRight (.refl d.w₂))

structure Summary where
  (t u v w₁ w₂ : Comb)
  (left right joinLeft joinRight : EventData)
  joinEq : Bool
  deriving Repr

def summary {t : Comb} (d : Diamond t) : Summary :=
  { t := t
    u := d.u
    v := d.v
    w₁ := d.w₁
    w₂ := d.w₂
    left := d.left.ed
    right := d.right.ed
    joinLeft := d.joinLeft.ed
    joinRight := d.joinRight.ed
    joinEq := decide (d.w₁ = d.w₂) }

end Diamond

/-! ## Bounded search for 1-step diamonds -/

abbrev Edge (t : Comb) : Type :=
  {e : (EventData × Comb) // e ∈ stepEdgesList t}

namespace Edge

def ed {t : Comb} (e : Edge t) : EventData := e.1.1
def dst {t : Comb} (e : Edge t) : Comb := e.1.2

def toLStep {t : Comb} (e : Edge t) : LStep t (dst e) :=
  match e with
  | ⟨(ed0, u0), hmem⟩ =>
      { ed := ed0
        mem := (mem_stepEdges_iff (t := t) (e := (ed0, u0))).2 hmem }

end Edge

private def firstSome {α β : Type} (xs : List α) (f : α → Option β) : Option β :=
  match xs with
  | [] => none
  | x :: xs =>
      match f x with
      | some y => some y
      | none => firstSome xs f

/-- Enumerate one-step edges out of `t` as a list carrying membership proofs. -/
def edgeList (t : Comb) : List (Edge t) :=
  (stepEdgesList t).attach

/-- Find any 1-step diamond out of `t` (if one exists). -/
def findDiamond1? (t : Comb) : Option (Diamond t) :=
  let es := edgeList t
  firstSome es fun e₁ =>
    firstSome es fun e₂ =>
      let u := Edge.dst e₁
      let v := Edge.dst e₂
      if u = v then
        none
      else
        let eus := edgeList u
        let evs := edgeList v
        firstSome eus fun f₁ =>
          firstSome evs fun f₂ =>
            let w₁ := Edge.dst f₁
            let w₂ := Edge.dst f₂
            if h : w₁ = w₂ then
              some
                { u := u
                  v := v
                  w₁ := w₁
                  w₂ := w₂
                  left := Edge.toLStep e₁
                  right := Edge.toLStep e₂
                  joinLeft := Edge.toLStep f₁
                  joinRight := Edge.toLStep f₂
                  joinEq := h }
            else
              none

/-! ## Bounded join search (multi-step) -/

/-!
`findDiamond1?` only searches for **1-step** joins.  For building “completion cells” beyond the
local diamond, it is useful to search for a common descendant within a bounded number of steps.

The functions below are purely computational/constructive (they return explicit labeled paths),
and are intended as an incremental bridge toward a “completion-rule 2-cell generator” API.
-/

/-- A reachable state together with a concrete labeled path witnessing reachability. -/
structure Reachable (start : Comb) where
  dst : Comb
  path : LSteps start dst

namespace Reachable

@[simp] def refl (t : Comb) : Reachable t :=
  { dst := t
    path := .refl t }

private def oneStep {t u : Comb} (s : LStep t u) : LSteps t u :=
  .trans s (.refl u)

/-- Expand a reachable witness by one more labeled step. -/
def extend {start : Comb} (r : Reachable start) : List (Reachable start) :=
  (edgeList r.dst).map fun e =>
    let u := Edge.dst e
    let s : LStep r.dst u := Edge.toLStep e
    { dst := u
      path := LSteps.comp r.path (oneStep s) }

/-- Any element of `extend r` increases the path length by exactly one. -/
theorem length_of_mem_extend {start : Comb} (r : Reachable start) {r' : Reachable start}
    (h : r' ∈ extend r) :
    r'.path.length = r.path.length + 1 := by
  unfold extend at h
  rcases List.mem_map.1 h with ⟨e, _he, rfl⟩
  simp [oneStep, LSteps.length_comp, LSteps.length]

end Reachable

/-- Frontier at exact depth `k`, represented as a list of `Reachable` witnesses. -/
private def concatMap {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

private theorem mem_concatMap {α β : Type} {xs : List α} {f : α → List β} {y : β} :
    y ∈ concatMap xs f ↔ ∃ x ∈ xs, y ∈ f x := by
  induction xs with
  | nil =>
      simp [concatMap]
  | cons x xs ih =>
      constructor
      · intro hy
        have : y ∈ f x ∨ y ∈ concatMap xs f := by
          simpa [concatMap, List.mem_append] using hy
        rcases this with hyx | hyxs
        · exact ⟨x, by simp, hyx⟩
        · rcases (ih.1 hyxs) with ⟨x', hx', hy'⟩
          exact ⟨x', by simp [hx'], hy'⟩
      · rintro ⟨x', hx', hy'⟩
        have : x' = x ∨ x' ∈ xs := by
          simpa [List.mem_cons] using hx'
        rcases this with rfl | hx''
        · simp [concatMap, List.mem_append, hy']
        · have : y ∈ concatMap xs f := (ih.2 ⟨x', hx'', hy'⟩)
          have : y ∈ f x ∨ y ∈ concatMap xs f := Or.inr this
          simpa [concatMap, List.mem_append] using this

def frontier (t : Comb) : Nat → List (Reachable t)
  | 0 => [Reachable.refl t]
  | k + 1 => concatMap (frontier t k) (Reachable.extend (start := t))

/-- All reachable witnesses up to depth `k` (including depth 0). -/
def reachableUpTo (t : Comb) : Nat → List (Reachable t)
  | 0 => frontier t 0
  | k + 1 => reachableUpTo t k ++ frontier t (k + 1)

theorem length_of_mem_frontier {t : Comb} {k : Nat} {r : Reachable t} (h : r ∈ frontier t k) :
    r.path.length = k := by
  induction k generalizing r with
  | zero =>
      simp [frontier] at h
      subst h
      simp [LSteps.length]
  | succ k ih =>
      have h' : ∃ r0 ∈ frontier t k, r ∈ Reachable.extend (start := t) r0 := by
        simpa [frontier] using (mem_concatMap (xs := frontier t k) (f := Reachable.extend (start := t)) (y := r)).1 h
      rcases h' with ⟨r0, hr0, hr⟩
      have hk : r0.path.length = k := ih hr0
      have hlen : r.path.length = r0.path.length + 1 := Reachable.length_of_mem_extend r0 hr
      calc
        r.path.length = r0.path.length + 1 := hlen
        _ = k + 1 := by simp [hk]

theorem length_le_of_mem_reachableUpTo {t : Comb} {k : Nat} {r : Reachable t} (h : r ∈ reachableUpTo t k) :
    r.path.length ≤ k := by
  induction k generalizing r with
  | zero =>
      have hk : r.path.length = 0 := length_of_mem_frontier (t := t) (k := 0) h
      simp [hk]
  | succ k ih =>
      have h' : r ∈ reachableUpTo t k ∨ r ∈ frontier t (k + 1) := by
        simpa [reachableUpTo, List.mem_append] using h
      rcases h' with h₁ | h₂
      · exact Nat.le_trans (ih h₁) (Nat.le_succ k)
      · have hk : r.path.length = k + 1 := length_of_mem_frontier (t := t) (k := k + 1) h₂
        simp [hk]

/-- A witness that `u` and `v` have a common descendant `w` with explicit paths. -/
structure JoinWitness (u v : Comb) where
  w : Comb
  left : LSteps u w
  right : LSteps v w

namespace JoinWitness

structure Summary where
  (u v w : Comb)
  (leftLen rightLen : Nat)
  deriving Repr

def summary {u v : Comb} (j : JoinWitness u v) : Summary :=
  { u := u
    v := v
    w := j.w
    leftLen := j.left.length
    rightLen := j.right.length }

end JoinWitness

/-- Find a common descendant of `u` and `v` by searching all paths up to depth `k` from each side. -/
def findJoinUpTo? (u v : Comb) (k : Nat) : Option (JoinWitness u v) :=
  let us := reachableUpTo u k
  let vs := reachableUpTo v k
  firstSome us fun ru =>
    firstSome vs fun rv =>
      if h : ru.dst = rv.dst then
        some
          { w := ru.dst
            left := ru.path
            right := by
              simpa [h.symm] using rv.path }
      else
        none

/-! ## Completion cells (fork + bounded join) -/

/-- A “completion cell” out of a term `t`: a 1-step fork `t ⟶ u`, `t ⟶ v` and a bounded join
`u ⟶* w`, `v ⟶* w`. -/
structure Completion (t : Comb) where
  (u v w : Comb)
  left : LStep t u
  right : LStep t v
  joinLeft : LSteps u w
  joinRight : LSteps v w

namespace Completion

/-- The left boundary path of a completion cell: `t ⟶ u ⟶* w`. -/
def leftPath {t : Comb} (c : Completion t) : LSteps t c.w :=
  .trans c.left c.joinLeft

/-- The right boundary path of a completion cell: `t ⟶ v ⟶* w`. -/
def rightPath {t : Comb} (c : Completion t) : LSteps t c.w :=
  .trans c.right c.joinRight

structure Summary where
  (t u v w : Comb)
  (left right : EventData)
  (joinLeftLen joinRightLen : Nat)
  deriving Repr

def summary {t : Comb} (c : Completion t) : Summary :=
  { t := t
    u := c.u
    v := c.v
    w := c.w
    left := c.left.ed
    right := c.right.ed
    joinLeftLen := c.joinLeft.length
    joinRightLen := c.joinRight.length }

end Completion

/-- Search for a completion cell out of `t`, joining divergent 1-step reductions within `k` steps. -/
def findCompletion? (t : Comb) (k : Nat) : Option (Completion t) :=
  let es := edgeList t
  firstSome es fun e₁ =>
    firstSome es fun e₂ =>
      let u := Edge.dst e₁
      let v := Edge.dst e₂
      if u = v then
        none
      else
        match findJoinUpTo? u v k with
        | none => none
        | some j =>
            some
              { u := u
                v := v
                w := j.w
                left := Edge.toLStep e₁
                right := Edge.toLStep e₂
                joinLeft := j.left
                joinRight := j.right }

/-! ## Proof-based completion (non-search) -/

namespace Completion

open HeytingLean.LoF.Combinators.Category.PathTruncation

/-- Any 1-step fork in the multiway graph admits a (possibly multi-step) completion cell, by
`Comb.Step.local_confluence` plus the thin↔labeled path bridge. -/
theorem nonempty_of_fork {t u v : Comb} (left : LStep t u) (right : LStep t v) :
    Nonempty (Completion t) := by
  rcases Comb.Step.local_confluence (t := t) (u := u) (v := v) left.toStep right.toStep with ⟨w, huw, hvw⟩
  rcases PathTruncation.nonempty_lsteps_of_steps (t := u) (u := w) huw with ⟨p⟩
  rcases PathTruncation.nonempty_lsteps_of_steps (t := v) (u := w) hvw with ⟨q⟩
  exact
    ⟨{ u := u
       v := v
       w := w
       left := left
       right := right
       joinLeft := p
       joinRight := q }⟩

/-- Any 1-step fork admits a completion cell whose join legs have length ≤ 2. -/
theorem exists_of_fork_len_le2 {t u v : Comb} (left : LStep t u) (right : LStep t v) :
    ∃ c : Completion t, c.joinLeft.length ≤ 2 ∧ c.joinRight.length ≤ 2 := by
  rcases Comb.Step.local_confluence_upTo2 (t := t) (u := u) (v := v) left.toStep right.toStep with
    ⟨w, huw, hvw⟩
  -- Convert the bounded thin witnesses into bounded labeled paths.
  have hL : ∃ p : LSteps u w, p.length ≤ 2 := by
    cases huw with
    | refl =>
        refine ⟨.refl u, ?_⟩
        simp [LSteps.length]
    | step h =>
        rcases PathTruncation.nonempty_lstep_of_step (t := u) (u := w) h with ⟨s⟩
        refine ⟨.trans s (.refl w), ?_⟩
        simp [LSteps.length]
    | step2 h1 h2 =>
        rename_i m
        rcases PathTruncation.nonempty_lstep_of_step (t := u) (u := m) h1 with ⟨s1⟩
        rcases PathTruncation.nonempty_lstep_of_step (t := m) (u := w) h2 with ⟨s2⟩
        refine ⟨.trans s1 (.trans s2 (.refl w)), ?_⟩
        simp [LSteps.length]
  have hR : ∃ q : LSteps v w, q.length ≤ 2 := by
    cases hvw with
    | refl =>
        refine ⟨.refl v, ?_⟩
        simp [LSteps.length]
    | step h =>
        rcases PathTruncation.nonempty_lstep_of_step (t := v) (u := w) h with ⟨s⟩
        refine ⟨.trans s (.refl w), ?_⟩
        simp [LSteps.length]
    | step2 h1 h2 =>
        rename_i m
        rcases PathTruncation.nonempty_lstep_of_step (t := v) (u := m) h1 with ⟨s1⟩
        rcases PathTruncation.nonempty_lstep_of_step (t := m) (u := w) h2 with ⟨s2⟩
        refine ⟨.trans s1 (.trans s2 (.refl w)), ?_⟩
        simp [LSteps.length]
  rcases hL with ⟨p, hp⟩
  rcases hR with ⟨q, hq⟩
  refine ⟨{ u := u, v := v, w := w, left := left, right := right, joinLeft := p, joinRight := q }, ?_, ?_⟩
  · exact hp
  · exact hq

end Completion

end Category
end Combinators
end LoF
end HeytingLean
