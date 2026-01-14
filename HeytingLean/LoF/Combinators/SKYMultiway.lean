import Mathlib.Data.Finset.Basic
import HeytingLean.LoF.Combinators.SKY

/-!
# SKYMultiway — enumerating labeled one-step reductions

This module refines the propositional small-step relation `Comb.Step` into an *enumerator*
that lists all possible one-step reductions together with an **event label**:

- `rule`  : which rewrite schema fired (`K`, `S`, `Y`)
- `path`  : where the redex occurs (left/right descent in the term tree)

We provide a list enumerator (deterministic order) and a finset view, and prove
soundness/completeness against `Comb.Step`.
-/

namespace HeytingLean
namespace LoF

namespace Comb

/-! ## Event labels -/

inductive RuleTag
  | K
  | S
  | Y
  deriving DecidableEq, Repr

def RuleTag.toNat : RuleTag → Nat
  | .K => 0
  | .S => 1
  | .Y => 2

inductive Dir
  | L
  | R
  deriving DecidableEq, Repr

def Dir.toNat : Dir → Nat
  | .L => 0
  | .R => 1

abbrev RedexPath := List Dir

structure EventData where
  rule : RuleTag
  path : RedexPath
  deriving DecidableEq, Repr

/-! ## Root step recognition -/

def rootStep? : Comb → Option (RuleTag × Comb)
  | Comb.app (Comb.app .K x) _y =>
      some (RuleTag.K, x)
  | Comb.app (Comb.app (Comb.app .S x) y) z =>
      some (RuleTag.S, Comb.app (Comb.app x z) (Comb.app y z))
  | Comb.app .Y f =>
      some (RuleTag.Y, Comb.app f (Comb.app .Y f))
  | _ =>
      none

theorem rootStep?_sound {t : Comb} {r : RuleTag} {u : Comb} :
    rootStep? t = some (r, u) → Step t u := by
  intro h
  cases t with
  | K =>
      simp [rootStep?] at h
  | S =>
      simp [rootStep?] at h
  | Y =>
      simp [rootStep?] at h
  | app f a =>
      cases f with
      | K =>
          simp [rootStep?] at h
      | S =>
          simp [rootStep?] at h
      | Y =>
          -- `t = Y · a`
          have : some (RuleTag.Y, Comb.app a (Comb.app .Y a)) = some (r, u) := by
            simpa [rootStep?] using h
          cases this
          simpa using Step.Y_rule a
      | app f₁ f₂ =>
          -- Potentially `K`- or `S`-rule when `f` has enough arguments.
          cases f₁ with
          | K =>
              -- `t = (K · f₂) · a`
              have : some (RuleTag.K, f₂) = some (r, u) := by
                simpa [rootStep?] using h
              cases this
              simpa using Step.K_rule (x := u) (y := a)
          | S =>
              -- `t = (S · f₂) · a` is not a root redex.
              simp [rootStep?] at h
          | Y =>
              simp [rootStep?] at h
          | app f₁₁ f₁₂ =>
              cases f₁₁ with
              | S =>
                  -- `t = ((S · f₁₂) · f₂) · a`
                  have :
                      some (RuleTag.S, Comb.app (Comb.app f₁₂ a) (Comb.app f₂ a)) =
                        some (r, u) := by
                    simpa [rootStep?] using h
                  cases this
                  simpa using Step.S_rule f₁₂ f₂ a
              | _ =>
                  simp [rootStep?] at h

/-! ## Enumerating all one-step edges (list + finset) -/

def rootEdgesList (t : Comb) : List (EventData × Comb) :=
  match rootStep? t with
  | some (r, u) => [({ rule := r, path := [] }, u)]
  | none => []

def liftLeft (a : Comb) : (EventData × Comb) → (EventData × Comb)
  | (ed, u) => ({ ed with path := Dir.L :: ed.path }, Comb.app u a)

def liftRight (f : Comb) : (EventData × Comb) → (EventData × Comb)
  | (ed, u) => ({ ed with path := Dir.R :: ed.path }, Comb.app f u)

/-- Deterministic enumeration of all one-step reductions from `t`,
including rule tag + redex path. -/
def stepEdgesList : Comb → List (EventData × Comb)
  | Comb.app f a =>
      let t := Comb.app f a
      rootEdgesList t ++
        ((stepEdgesList f).map (liftLeft a) ++
          (stepEdgesList a).map (liftRight f))
  | t =>
      rootEdgesList t

/-- Finite set view of `stepEdgesList`. This is the API used by the multiway explorer. -/
def stepEdges (t : Comb) : Finset (EventData × Comb) :=
  (stepEdgesList t).toFinset

theorem mem_stepEdges_iff {t : Comb} {e : EventData × Comb} :
    e ∈ stepEdges t ↔ e ∈ stepEdgesList t := by
  simp [stepEdges]

/-! ## Soundness: enumerated edges are valid `Step`s -/

theorem stepEdgesList_sound :
    ∀ {t : Comb} {ed : EventData} {u : Comb},
      (ed, u) ∈ stepEdgesList t → Step t u := by
  intro t
  induction t with
  | K =>
      intro ed u h
      cases h
  | S =>
      intro ed u h
      cases h
  | Y =>
      intro ed u h
      cases h
  | app f a ihf iha =>
      intro ed u hmem
      -- Split membership across `root ++ (left ++ right)`.
      have hrootOrRest :
          (ed, u) ∈ rootEdgesList (Comb.app f a) ∨
          (ed, u) ∈ (stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f) := by
        simpa [stepEdgesList] using (List.mem_append.1 hmem)
      rcases hrootOrRest with hroot | hrest
      · -- Root redex case: recover the `rootStep?` equality from membership.
        cases h0 : rootStep? (Comb.app f a) with
        | none =>
            simp [rootEdgesList, h0] at hroot
        | some ru =>
            rcases ru with ⟨r0, u0⟩
            have hEq : (ed, u) = ({ rule := r0, path := [] }, u0) := by
              simpa [rootEdgesList, h0] using hroot
            cases hEq
            exact rootStep?_sound (t := Comb.app f a) (r := r0) (u := u) h0
      ·
        have hleftOrRight :
            (ed, u) ∈ (stepEdgesList f).map (liftLeft a) ∨
            (ed, u) ∈ (stepEdgesList a).map (liftRight f) := by
          simpa [List.mem_append] using hrest
        rcases hleftOrRight with hleft | hright
        · -- Left subtree step, lifted by `app_left`.
          rcases (List.mem_map.1 hleft) with ⟨p, hp, hpEq⟩
          rcases p with ⟨ed0, u0⟩
          cases hpEq
          exact Step.app_left (ihf (ed := ed0) (u := u0) hp)
        · -- Right subtree step, lifted by `app_right`.
          rcases (List.mem_map.1 hright) with ⟨p, hp, hpEq⟩
          rcases p with ⟨ed0, u0⟩
          cases hpEq
          exact Step.app_right (iha (ed := ed0) (u := u0) hp)

theorem stepEdges_sound {t : Comb} {ed : EventData} {u : Comb} :
    (ed, u) ∈ stepEdges t → Step t u := by
  intro h
  have h' : (ed, u) ∈ stepEdgesList t := (mem_stepEdges_iff (t := t)).1 h
  exact stepEdgesList_sound (t := t) (ed := ed) (u := u) h'

/-! ## Completeness: any `Step` appears in the enumerator -/

theorem stepEdgesList_complete :
    ∀ {t u : Comb}, Step t u → ∃ ed : EventData, (ed, u) ∈ stepEdgesList t := by
  intro t u h
  induction h with
  | K_rule x y =>
      refine ⟨{ rule := RuleTag.K, path := [] }, ?_⟩
      -- The root edge is present at the head of the list.
      have hroot :
          ({ rule := RuleTag.K, path := [] }, x) ∈ rootEdgesList (Comb.app (Comb.app .K x) y) := by
        simp [rootEdgesList, rootStep?]
      have : ({ rule := RuleTag.K, path := [] }, x) ∈
          rootEdgesList (Comb.app (Comb.app .K x) y) ++
            ((stepEdgesList (Comb.app .K x)).map (liftLeft y) ++
              (stepEdgesList y).map (liftRight (Comb.app .K x))) :=
        List.mem_append_left _ hroot
      simpa [stepEdgesList] using this
  | S_rule x y z =>
      refine ⟨{ rule := RuleTag.S, path := [] }, ?_⟩
      have hroot :
          ({ rule := RuleTag.S, path := [] }, Comb.app (Comb.app x z) (Comb.app y z)) ∈
            rootEdgesList (Comb.app (Comb.app (Comb.app .S x) y) z) := by
        simp [rootEdgesList, rootStep?]
      have :
          ({ rule := RuleTag.S, path := [] }, Comb.app (Comb.app x z) (Comb.app y z)) ∈
            rootEdgesList (Comb.app (Comb.app (Comb.app .S x) y) z) ++
              ((stepEdgesList (Comb.app (Comb.app .S x) y)).map (liftLeft z) ++
                (stepEdgesList z).map (liftRight (Comb.app (Comb.app .S x) y))) :=
        List.mem_append_left _ hroot
      simpa [stepEdgesList] using this
  | Y_rule f =>
      refine ⟨{ rule := RuleTag.Y, path := [] }, ?_⟩
      have hroot :
          ({ rule := RuleTag.Y, path := [] }, Comb.app f (Comb.app .Y f)) ∈
            rootEdgesList (Comb.app .Y f) := by
        simp [rootEdgesList, rootStep?]
      have :
          ({ rule := RuleTag.Y, path := [] }, Comb.app f (Comb.app .Y f)) ∈
            rootEdgesList (Comb.app .Y f) ++
              ((stepEdgesList .Y).map (liftLeft f) ++ (stepEdgesList f).map (liftRight .Y)) :=
        List.mem_append_left _ hroot
      simpa [stepEdgesList] using this
  | app_left hstep ih =>
      rename_i f f' a
      rcases ih with ⟨ed0, hmem⟩
      refine ⟨{ ed0 with path := Dir.L :: ed0.path }, ?_⟩
      -- Show membership in the left-map part.
      have hmap :
          ({ ed0 with path := Dir.L :: ed0.path }, Comb.app f' a) ∈
            (stepEdgesList f).map (liftLeft a) := by
        refine (List.mem_map.2 ?_)
        refine ⟨(ed0, f'), hmem, ?_⟩
        rfl
      have hrest :
          ({ ed0 with path := Dir.L :: ed0.path }, Comb.app f' a) ∈
            (stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f) :=
        List.mem_append_left _ hmap
      have hAll :
          ({ ed0 with path := Dir.L :: ed0.path }, Comb.app f' a) ∈
            rootEdgesList (Comb.app f a) ++
              ((stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f)) :=
        List.mem_append_right _ hrest
      simpa [stepEdgesList] using hAll
  | app_right hstep ih =>
      rename_i f a a'
      rcases ih with ⟨ed0, hmem⟩
      refine ⟨{ ed0 with path := Dir.R :: ed0.path }, ?_⟩
      have hmap :
          ({ ed0 with path := Dir.R :: ed0.path }, Comb.app f a') ∈
            (stepEdgesList a).map (liftRight f) := by
        refine (List.mem_map.2 ?_)
        refine ⟨(ed0, a'), hmem, ?_⟩
        rfl
      have hrest :
          ({ ed0 with path := Dir.R :: ed0.path }, Comb.app f a') ∈
            (stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f) :=
        List.mem_append_right _ hmap
      have hAll :
          ({ ed0 with path := Dir.R :: ed0.path }, Comb.app f a') ∈
            rootEdgesList (Comb.app f a) ++
              ((stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f)) :=
        List.mem_append_right _ hrest
      simpa [stepEdgesList] using hAll

theorem stepEdges_complete {t u : Comb} :
    Step t u → ∃ ed : EventData, (ed, u) ∈ stepEdges t := by
  intro h
  rcases stepEdgesList_complete (t := t) (u := u) h with ⟨ed, hmem⟩
  refine ⟨ed, (mem_stepEdges_iff (t := t)).2 hmem⟩

end Comb

end LoF
end HeytingLean
