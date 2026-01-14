import HeytingLean.LoF.Combinators.Lambda.Syntax

/-!
# Lambda.Enumeration — bounded enumeration of well-scoped terms

This module provides a simple bounded enumerator for untyped de Bruijn λ-terms.

`Term.enumAt depth size` enumerates all terms of exact `nodeCount = size` whose variables
are in range `[0, depth)` (i.e. well-scoped at binder depth `depth`).

Closed terms at size `n` are `Term.enumClosed n := Term.enumAt 0 n`.

This is meant for small “ruliology”-style experiments (sizes grow exponentially).
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Lambda

namespace Term

/-- Internal DP table: index `k` stores `enumAt depth k`. -/
def enumTable (depth : Nat) : Nat → Array (List Term)
  | 0 => #[[]]
  | n + 1 =>
      let prev := enumTable depth n
      let size := n + 1
      let curr : List Term :=
        match size with
        | 0 => []
        | 1 => (List.range depth).map Term.var
        | _ =>
            let lams : List Term :=
              ((enumTable (depth + 1) n)[n]!).map Term.lam
            let apps : List Term :=
              (List.range (n - 1)).bind (fun i =>
                let k := i + 1
                let l := n - k
                (prev[k]!).bind (fun f =>
                  (prev[l]!).map (fun a => Term.app f a)))
            lams ++ apps
      prev.push curr

/-- Enumerate all terms with `nodeCount = size` well-scoped at binder depth `depth`. -/
def enumAt (depth size : Nat) : List Term :=
  (enumTable depth size)[size]!

def enumClosed (size : Nat) : List Term :=
  enumAt 0 size

end Term

end Lambda
end Combinators
end LoF
end HeytingLean

