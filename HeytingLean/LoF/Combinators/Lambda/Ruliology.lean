import Lean
import Std.Data.HashMap
import HeytingLean.LoF.Combinators.Lambda.Beta

/-!
# Lambda.Ruliology — bounded multiway exploration utilities

This is a reusable (non-CLI) library layer that builds a bounded-depth multiway graph for
untyped de Bruijn λ-terms under β-reduction (`Lambda.stepEdgesList`).

It mirrors the data model used by `HeytingLean.CLI.SkyMultiwayMain` so downstream tooling
(docs/visualizers) can consume a consistent JSON schema.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Lambda

open Lean

/-! ## Multiway graph payload (structured) -/

structure Edge where
  src : Nat
  dst : Nat
  label : EventData
  deriving Repr

structure MultiwayGraph where
  nodes : Array Term
  edges : Array Edge
  levels : Array (Array Nat)
  branchial : Array (Nat × Nat)
  pathCounts : Array (Array (Nat × Nat))
  deriving Repr

/-! ## JSON encodings -/

def termToJson : Term → Json
  | .var i => Json.arr #[Json.num 0, Json.num i]
  | .app f a => Json.arr #[Json.num 1, termToJson f, termToJson a]
  | .lam body => Json.arr #[Json.num 2, termToJson body]

def pathToJson (p : RedexPath) : Json :=
  Json.arr ((p.map (fun d => Json.num d.toNat)).toArray)

def eventToJson (ed : EventData) : Json :=
  Json.mkObj
    [ ("ruleIdx", Json.num ed.rule.toNat)
    , ("path", pathToJson ed.path) ]

def edgeToJson (e : Edge) : Json :=
  Json.mkObj
    [ ("src", Json.num e.src)
    , ("dst", Json.num e.dst)
    , ("label", eventToJson e.label) ]

def branchialToJson (p : Nat × Nat) : Json :=
  Json.mkObj [("i", Json.num p.1), ("j", Json.num p.2)]

def levelToJson (lvl : Array Nat) : Json :=
  Json.arr (lvl.map (fun (i : Nat) => Json.num i))

def pathCountRowToJson (row : Array (Nat × Nat)) : Json :=
  Json.arr <|
    row.map (fun (p : Nat × Nat) => Json.mkObj [("id", Json.num p.1), ("count", Json.num p.2)])

namespace MultiwayGraph

def toJson (g : MultiwayGraph) (sysName : String) (maxDepth : Nat) (init : Term) : Json :=
  Json.mkObj
    [ ("system", Json.str sysName)
    , ("maxDepth", Json.num maxDepth)
    , ("initNodeCount", Json.num init.nodeCount)
    , ("initLeafCount", Json.num init.leafCount)
    , ("nodes", Json.arr (g.nodes.map termToJson))
    , ("edges", Json.arr (g.edges.map edgeToJson))
    , ("levels", Json.arr (g.levels.map levelToJson))
    , ("branchial", Json.arr (g.branchial.map branchialToJson))
    , ("pathCounts", Json.arr (g.pathCounts.map pathCountRowToJson)) ]

end MultiwayGraph

/-! ## Core builder (bounded BFS with path counting) -/

private def findIdxFuel {α : Type} [DecidableEq α] (arr : Array α) (x : α) (fuel i : Nat) :
    Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : i < arr.size then
        if arr[i] = x then some i else findIdxFuel arr x fuel (i + 1)
      else
        none

private def findIdx {α : Type} [DecidableEq α] (arr : Array α) (x : α) : Option Nat :=
  findIdxFuel arr x (arr.size + 1) 0

private def getIdx {α : Type} [DecidableEq α] (nodes : Array α) (x : α) : (Array α × Nat) :=
  match findIdx nodes x with
  | some i => (nodes, i)
  | none => (nodes.push x, nodes.size)

private def dedupArray {α : Type} [DecidableEq α] (xs : Array α) : Array α :=
  xs.foldl (init := (#[] : Array α)) (fun acc x => if acc.contains x then acc else acc.push x)

private def pairEdges (idxs : Array Nat) : Array (Nat × Nat) :=
  let n := idxs.size
  let rec outer (i : Nat) (acc : Array (Nat × Nat)) : Array (Nat × Nat) :=
    if i < n then
      let ii := idxs[i]!
      let rec inner (j : Nat) (acc2 : Array (Nat × Nat)) : Array (Nat × Nat) :=
        if j < n then
          let jj := idxs[j]!
          inner (j + 1) (acc2.push (ii, jj))
        else acc2
      outer (i + 1) (inner (i + 1) acc)
    else acc
  outer 0 #[]

private def getD (m : Std.HashMap Nat Nat) (k : Nat) (default : Nat) : Nat :=
  match m.get? k with
  | some v => v
  | none => default

private def incrCount (m : Std.HashMap Nat Nat) (k : Nat) (inc : Nat) : Std.HashMap Nat Nat :=
  let curr := getD m k 0
  m.insert k (curr + inc)

/-- Build a bounded-depth multiway graph payload, starting at `init`. -/
def buildMultiway (init : Term) (maxDepth : Nat) : MultiwayGraph := Id.run do
  let mut nodes : Array Term := #[init]
  let mut edges : Array Edge := #[]
  let mut branchial : Array (Nat × Nat) := #[]
  let mut levels : Array (Array Nat) := #[#[0]]

  let mut curr : Array Term := #[init]
  let mut countsCurr : Std.HashMap Nat Nat := (Std.HashMap.emptyWithCapacity 8).insert 0 1
  let mut pathCounts : Array (Array (Nat × Nat)) := #[#[(0, 1)]]

  for _step in [0:maxDepth] do
    let mut nextRaw : Array Term := #[]
    let mut countsNext : Std.HashMap Nat Nat := Std.HashMap.emptyWithCapacity 8
    for s in curr do
      let (nodes1, srcIdx) := getIdx nodes s
      nodes := nodes1
      let srcCount := getD countsCurr srcIdx 0
      let mut childIdxs : Array Nat := #[]
      for (ed, t) in (stepEdgesList s) do
        let (nodes2, dstIdx) := getIdx nodes t
        nodes := nodes2
        edges := edges.push { src := srcIdx, dst := dstIdx, label := ed }
        childIdxs := childIdxs.push dstIdx
        nextRaw := nextRaw.push t
        countsNext := incrCount countsNext dstIdx srcCount
      let childIdxsDedup := dedupArray childIdxs
      for (i, j) in pairEdges childIdxsDedup do
        branchial := branchial.push (i, j)

    let next := dedupArray nextRaw
    let nextIdxs : Array Nat :=
      next.map (fun s =>
        let (_, i) := getIdx nodes s
        i)
    levels := levels.push nextIdxs
    let countsRow : Array (Nat × Nat) :=
      nextIdxs.map (fun (i : Nat) => (i, getD countsNext i 0))
    pathCounts := pathCounts.push countsRow
    curr := next
    countsCurr := countsNext

  return { nodes, edges, levels, branchial, pathCounts }

def buildMultiwayJson (sysName : String) (init : Term) (maxDepth : Nat) : Json :=
  (buildMultiway init maxDepth).toJson sysName maxDepth init

end Lambda
end Combinators
end LoF
end HeytingLean
