import HeytingLean.LoF.Combinators.Category.MultiwayCategory

/-!
# HigherCells — a minimal 2-cell interface for SKY multiway paths

SKY with `Y` is non-terminating, and this development does not assume (or need) a global
confluence theorem for the **labeled** path category. Instead, we provide a conservative notion
of a 2-cell as a *commuting square*: two paths are 2-related if they can be extended to literally
the same labeled path.

This is enough to:
- state local confluence-style hypotheses,
- compute/record explicit “diamonds” for small bounded explorations,
- serve as a growth point for completion-rule encodings.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-- A 2-cell witness between two paths `p q : t ⟶ u` given by a commuting square:
there exists a common target `v` and extensions `r₁ r₂ : u ⟶ v` such that
`p ⋙ r₁ = q ⋙ r₂` as labeled paths. -/
structure PathHomotopy (t u : Comb) (p q : LSteps t u) where
  v : Comb
  r₁ : LSteps u v
  r₂ : LSteps u v
  comm : LSteps.comp p r₁ = LSteps.comp q r₂

namespace PathHomotopy

def refl {t u : Comb} (p : LSteps t u) : PathHomotopy t u p p :=
  { v := u
    r₁ := .refl u
    r₂ := .refl u
    comm := by
      simp }

def symm {t u : Comb} {p q : LSteps t u} :
    PathHomotopy t u p q → PathHomotopy t u q p := by
  intro h
  refine
    { v := h.v
      r₁ := h.r₂
      r₂ := h.r₁
      comm := ?_ }
  simpa using h.comm.symm

end PathHomotopy

end Category
end Combinators
end LoF
end HeytingLean
