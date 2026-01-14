import Mathlib.Data.Finset.Basic
import HeytingLean.LoF.Combinators.Lambda.Syntax

/-!
# Lambda.Beta — β-reduction and multiway edge enumeration

This module defines:

* `Step`  : one-step β-reduction anywhere in a term (multiway relation)
* `Steps` : reflexive-transitive closure of `Step`
* `stepEdgesList` : deterministic enumeration of all one-step successors, labeled by:
  - `rule` = `beta`
  - `path` = location of the redex (left/right/body descent)

The API mirrors `HeytingLean.LoF.Combinators.SKYMultiway`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Lambda

open Term

/-! ## Small-step / multi-step β-reduction -/

inductive Step : Term → Term → Prop where
  | beta (body arg : Term) :
      Step (.app (.lam body) arg) (Term.substTop arg body)
  | app_left {f f' a : Term} :
      Step f f' → Step (.app f a) (.app f' a)
  | app_right {f a a' : Term} :
      Step a a' → Step (.app f a) (.app f a')
  | lam_body {body body' : Term} :
      Step body body' → Step (.lam body) (.lam body')

inductive Steps : Term → Term → Prop where
  | refl (t : Term) : Steps t t
  | trans {t u v : Term} : Step t u → Steps u v → Steps t v

theorem Steps.of_eq {t u : Term} (h : t = u) : Steps t u := by
  subst h
  exact Steps.refl _

def Normal (t : Term) : Prop :=
  ∀ u : Term, ¬ Step t u

/-! ## Event labels (rule tag + redex path) -/

inductive RuleTag
  | beta
  deriving DecidableEq, Repr

def RuleTag.toNat : RuleTag → Nat
  | .beta => 0

inductive Dir
  | L
  | R
  | B
  deriving DecidableEq, Repr

def Dir.toNat : Dir → Nat
  | .L => 0
  | .R => 1
  | .B => 2

abbrev RedexPath := List Dir

structure EventData where
  rule : RuleTag
  path : RedexPath
  deriving DecidableEq, Repr

/-! ## Root step recognition -/

def rootStep? : Term → Option (RuleTag × Term)
  | .app (.lam body) arg => some (.beta, Term.substTop arg body)
  | _ => none

theorem rootStep?_sound {t : Term} {r : RuleTag} {u : Term} :
    rootStep? t = some (r, u) → Step t u := by
  intro h
  cases t with
  | var =>
      simp [rootStep?] at h
  | lam =>
      simp [rootStep?] at h
  | app f a =>
      cases f with
      | lam body =>
          have : some (RuleTag.beta, Term.substTop a body) = some (r, u) := by
            simpa [rootStep?] using h
          cases this
          simpa using Step.beta (body := body) (arg := a)
      | _ =>
          simp [rootStep?] at h

/-! ## Enumerating one-step edges (list + finset) -/

def rootEdgesList (t : Term) : List (EventData × Term) :=
  match rootStep? t with
  | some (r, u) => [({ rule := r, path := [] }, u)]
  | none => []

def liftLeft (a : Term) : (EventData × Term) → (EventData × Term)
  | (ed, u) => ({ ed with path := Dir.L :: ed.path }, Term.app u a)

def liftRight (f : Term) : (EventData × Term) → (EventData × Term)
  | (ed, u) => ({ ed with path := Dir.R :: ed.path }, Term.app f u)

def liftBody : (EventData × Term) → (EventData × Term)
  | (ed, u) => ({ ed with path := Dir.B :: ed.path }, Term.lam u)

/-- Deterministic enumeration of all one-step β-reductions from `t`. -/
def stepEdgesList : Term → List (EventData × Term)
  | .app f a =>
      let t := Term.app f a
      rootEdgesList t ++
        ((stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f))
  | .lam body =>
      rootEdgesList (.lam body) ++ (stepEdgesList body).map liftBody
  | t =>
      rootEdgesList t

def stepEdges (t : Term) : Finset (EventData × Term) :=
  (stepEdgesList t).toFinset

theorem mem_stepEdges_iff {t : Term} {e : EventData × Term} :
    e ∈ stepEdges t ↔ e ∈ stepEdgesList t := by
  simp [stepEdges]

/-! ## Soundness: enumerated edges are valid `Step`s -/

theorem stepEdgesList_sound :
    ∀ {t : Term} {ed : EventData} {u : Term},
      (ed, u) ∈ stepEdgesList t → Step t u := by
  intro t
  induction t with
  | var =>
      intro ed u h
      cases h
  | lam body ih =>
      intro ed u hmem
      have hrootOrBody :
          (ed, u) ∈ rootEdgesList (Term.lam body) ∨ (ed, u) ∈ (stepEdgesList body).map liftBody := by
        simpa [stepEdgesList] using (List.mem_append.1 hmem)
      rcases hrootOrBody with hroot | hbody
      ·
        cases h0 : rootStep? (Term.lam body) with
        | none =>
            simp [rootEdgesList, h0] at hroot
        | some ru =>
            rcases ru with ⟨r0, u0⟩
            have hEq : (ed, u) = ({ rule := r0, path := [] }, u0) := by
              simpa [rootEdgesList, h0] using hroot
            cases hEq
            exact rootStep?_sound (t := Term.lam body) (r := r0) (u := u) h0
      ·
        rcases (List.mem_map.1 hbody) with ⟨p, hp, hpEq⟩
        rcases p with ⟨ed0, u0⟩
        cases hpEq
        exact Step.lam_body (ih (ed := ed0) (u := u0) hp)
  | app f a ihf iha =>
      intro ed u hmem
      have hrootOrRest :
          (ed, u) ∈ rootEdgesList (Term.app f a) ∨
            (ed, u) ∈ (stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f) := by
        simpa [stepEdgesList] using (List.mem_append.1 hmem)
      rcases hrootOrRest with hroot | hrest
      ·
        cases h0 : rootStep? (Term.app f a) with
        | none =>
            simp [rootEdgesList, h0] at hroot
        | some ru =>
            rcases ru with ⟨r0, u0⟩
            have hEq : (ed, u) = ({ rule := r0, path := [] }, u0) := by
              simpa [rootEdgesList, h0] using hroot
            cases hEq
            exact rootStep?_sound (t := Term.app f a) (r := r0) (u := u) h0
      ·
        have hleftOrRight :
            (ed, u) ∈ (stepEdgesList f).map (liftLeft a) ∨
              (ed, u) ∈ (stepEdgesList a).map (liftRight f) := by
          simpa [List.mem_append] using hrest
        rcases hleftOrRight with hleft | hright
        ·
          rcases (List.mem_map.1 hleft) with ⟨p, hp, hpEq⟩
          rcases p with ⟨ed0, u0⟩
          cases hpEq
          exact Step.app_left (ihf (ed := ed0) (u := u0) hp)
        ·
          rcases (List.mem_map.1 hright) with ⟨p, hp, hpEq⟩
          rcases p with ⟨ed0, u0⟩
          cases hpEq
          exact Step.app_right (iha (ed := ed0) (u := u0) hp)

theorem stepEdges_sound {t : Term} {ed : EventData} {u : Term} :
    (ed, u) ∈ stepEdges t → Step t u := by
  intro h
  have h' : (ed, u) ∈ stepEdgesList t := (mem_stepEdges_iff (t := t)).1 h
  exact stepEdgesList_sound (t := t) (ed := ed) (u := u) h'

/-! ## Completeness: any `Step` appears in the enumerator -/

theorem stepEdgesList_complete :
    ∀ {t u : Term}, Step t u → ∃ ed : EventData, (ed, u) ∈ stepEdgesList t := by
  intro t u h
  induction h with
  | beta body arg =>
      refine ⟨{ rule := RuleTag.beta, path := [] }, ?_⟩
      have hroot :
          ({ rule := RuleTag.beta, path := [] }, Term.substTop arg body) ∈
            rootEdgesList (Term.app (Term.lam body) arg) := by
        simp [rootEdgesList, rootStep?]
      have :
          ({ rule := RuleTag.beta, path := [] }, Term.substTop arg body) ∈
            rootEdgesList (Term.app (Term.lam body) arg) ++
              ((stepEdgesList (Term.lam body)).map (liftLeft arg) ++
                (stepEdgesList arg).map (liftRight (Term.lam body))) :=
        List.mem_append_left _ hroot
      simpa [stepEdgesList] using this
  | app_left hstep ih =>
      rename_i f f' a
      rcases ih with ⟨ed0, hmem⟩
      refine ⟨{ ed0 with path := Dir.L :: ed0.path }, ?_⟩
      have hmap :
          ({ ed0 with path := Dir.L :: ed0.path }, Term.app f' a) ∈
            (stepEdgesList f).map (liftLeft a) := by
        refine (List.mem_map.2 ?_)
        refine ⟨(ed0, f'), hmem, ?_⟩
        rfl
      have hrest :
          ({ ed0 with path := Dir.L :: ed0.path }, Term.app f' a) ∈
            (stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f) :=
        List.mem_append_left _ hmap
      have hAll :
          ({ ed0 with path := Dir.L :: ed0.path }, Term.app f' a) ∈
            rootEdgesList (Term.app f a) ++
              ((stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f)) :=
        List.mem_append_right _ hrest
      simpa [stepEdgesList] using hAll
  | app_right hstep ih =>
      rename_i f a a'
      rcases ih with ⟨ed0, hmem⟩
      refine ⟨{ ed0 with path := Dir.R :: ed0.path }, ?_⟩
      have hmap :
          ({ ed0 with path := Dir.R :: ed0.path }, Term.app f a') ∈
            (stepEdgesList a).map (liftRight f) := by
        refine (List.mem_map.2 ?_)
        refine ⟨(ed0, a'), hmem, ?_⟩
        rfl
      have hrest :
          ({ ed0 with path := Dir.R :: ed0.path }, Term.app f a') ∈
            (stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f) :=
        List.mem_append_right _ hmap
      have hAll :
          ({ ed0 with path := Dir.R :: ed0.path }, Term.app f a') ∈
            rootEdgesList (Term.app f a) ++
              ((stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f)) :=
        List.mem_append_right _ hrest
      simpa [stepEdgesList] using hAll
  | lam_body hstep ih =>
      rename_i body body'
      rcases ih with ⟨ed0, hmem⟩
      refine ⟨{ ed0 with path := Dir.B :: ed0.path }, ?_⟩
      have hmap :
          ({ ed0 with path := Dir.B :: ed0.path }, Term.lam body') ∈
            (stepEdgesList body).map liftBody := by
        refine (List.mem_map.2 ?_)
        refine ⟨(ed0, body'), hmem, ?_⟩
        rfl
      have hAll :
          ({ ed0 with path := Dir.B :: ed0.path }, Term.lam body') ∈
            rootEdgesList (Term.lam body) ++ (stepEdgesList body).map liftBody :=
        List.mem_append_right _ hmap
      simpa [stepEdgesList] using hAll

theorem stepEdges_complete :
    ∀ {t u : Term}, Step t u → ∃ ed : EventData, (ed, u) ∈ stepEdges t := by
  intro t u h
  rcases stepEdgesList_complete (t := t) (u := u) h with ⟨ed, hed⟩
  refine ⟨ed, ?_⟩
  exact (mem_stepEdges_iff (t := t) (e := (ed, u))).2 hed

end Lambda
end Combinators
end LoF
end HeytingLean
