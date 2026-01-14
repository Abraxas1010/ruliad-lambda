import Mathlib.Combinatorics.SimpleGraph.Metric
import HeytingLean.LoF.Combinators.Category.BranchialGraph

/-!
# BranchialMetric — graph distance on bounded branchial slices

`BranchialGraph.lean` defines a computability-friendly **branchial adjacency** relation on a bounded
time-slice of SKY multiway exploration:

> connect two states at depth `n+1` if they share a common predecessor at depth `n`.

This file upgrades that adjacency to a (generally disconnected) **graph extended metric** by reusing
Mathlib's `SimpleGraph.edist` / `SimpleGraph.dist`.

Objectivity boundary:
- This is a metric structure on the **finite slice graph** (bounded exploration).
- It is not a claim about continuum branchial geometry or an `n\to\infty` limit.
- We use `edist : ℕ∞` because branchial slice graphs are typically disconnected.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open scoped Classical

open HeytingLean.LoF
open HeytingLean.LoF.Comb

namespace Branchial

/-! ## Slice graphs -/

/-- The (bounded) slice type: states reachable in exactly `n` steps from `start`. -/
def Slice (start : Comb) (n : Nat) : Type :=
  { t : Comb // t ∈ statesAtDepth start n }

/-- The branchial slice graph at depth `n` (undirected, loopless).

Adjacency is induced by membership in the finite edge set `branchialEdgesAtDepth`.
-/
def sliceGraph (start : Comb) : (n : Nat) → SimpleGraph (Slice start n)
  | 0 =>
      { Adj := fun _ _ => False
        symm := by intro _ _ h; cases h
        loopless := by intro _ h; cases h }
  | n + 1 =>
      { Adj := fun x y => s(x.1, y.1) ∈ branchialEdgesAtDepth start (n + 1)
        symm := by
          intro x y h
          simpa [Sym2.eq_swap] using h
        loopless := by
          intro x hx
          -- `s(x,x)` cannot occur because branchial edges are built from `siblingEdges`,
          -- which filters out diagonals.
          rcases
              (mem_branchialEdgesAtDepth_succ_iff (start := start) (n := n)
                    (z := s(x.1, x.1))).1 hx with
            ⟨parent, _hparent, hmem⟩
          have hne : x.1 ≠ x.1 :=
            (mem_siblingEdges_iff (parent := parent) (t := x.1) (u := x.1)).1 hmem |>.2.2
          exact hne rfl }

/-! ## Distances -/

/-- Extended branchial distance on the depth-`n` slice (value `⊤` if disconnected). -/
noncomputable def sliceEdist (start : Comb) (n : Nat) (x y : Slice start n) : ℕ∞ :=
  (sliceGraph start n).edist x y

/-- `ℕ`-valued branchial distance on the depth-`n` slice.

Warning: this uses the `0` junk value when `x` and `y` are disconnected; prefer `sliceEdist`.
-/
noncomputable def sliceDist (start : Comb) (n : Nat) (x y : Slice start n) : Nat :=
  (sliceGraph start n).dist x y

theorem sliceEdist_comm (start : Comb) (n : Nat) (x y : Slice start n) :
    sliceEdist start n x y = sliceEdist start n y x := by
  simpa [sliceEdist] using (SimpleGraph.edist_comm (G := sliceGraph start n) (u := x) (v := y))

theorem sliceEdist_self (start : Comb) (n : Nat) (x : Slice start n) :
    sliceEdist start n x x = 0 := by
  simp [sliceEdist]

theorem sliceEdist_triangle (start : Comb) (n : Nat) (x y z : Slice start n) :
    sliceEdist start n x z ≤ sliceEdist start n x y + sliceEdist start n y z := by
  simpa [sliceEdist] using (SimpleGraph.edist_triangle (G := sliceGraph start n) (u := x) (v := y) (w := z))

theorem sliceEdist_eq_one_iff_adj (start : Comb) (n : Nat) (x y : Slice start (n + 1)) :
    sliceEdist start (n + 1) x y = 1 ↔ (sliceGraph start (n + 1)).Adj x y := by
  simp [sliceEdist]

/-! ## Convenience: adjacency in terms of the underlying edge finset -/

theorem sliceAdj_iff_mem_edges (start : Comb) (n : Nat) (x y : Slice start (n + 1)) :
    (sliceGraph start (n + 1)).Adj x y ↔
      s(x.1, y.1) ∈ branchialEdgesAtDepth start (n + 1) := by
  rfl

end Branchial

end Category
end Combinators
end LoF
end HeytingLean
