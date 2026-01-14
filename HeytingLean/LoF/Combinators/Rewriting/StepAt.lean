import HeytingLean.LoF.Combinators.SKYMultiway

/-!
# StepAt — explicit-position one-step reductions for SKY

`Comb.Step` is a propositional small-step relation; it does not record *where* in the term tree
the redex occurs.

For higher-dimensional rewriting / completion-cells work it is useful to make the *position*
explicit.  This file defines:

* `Comb.StepAt t r p u` — “`t` reduces to `u` by firing rule `r` at redex-path `p`”
  where `p : RedexPath = List Dir`;
* an erasure lemma `StepAt.toStep`;
* an existence theorem `Comb.Step.exists_stepAt`.

This is a conservative bridge: it does not assert uniqueness of `(r,p)` for a given `Step`,
only existence (which is enough for many local confluence / commutation arguments).
-/

namespace HeytingLean
namespace LoF

namespace Comb

open Dir RuleTag

variable {t u v : Comb}

/-! ## Position-aware one-step reduction -/

inductive StepAt : Comb → RuleTag → RedexPath → Comb → Prop where
  | K_root (x y : Comb) :
      StepAt (Comb.app (Comb.app .K x) y) RuleTag.K [] x
  | S_root (x y z : Comb) :
      StepAt (Comb.app (Comb.app (Comb.app .S x) y) z)
        RuleTag.S
        []
        (Comb.app (Comb.app x z) (Comb.app y z))
  | Y_root (f : Comb) :
      StepAt (Comb.app .Y f) RuleTag.Y [] (Comb.app f (Comb.app .Y f))
  | left {f a f' : Comb} {r : RuleTag} {p : RedexPath} :
      StepAt f r p f' → StepAt (Comb.app f a) r (Dir.L :: p) (Comb.app f' a)
  | right {f a a' : Comb} {r : RuleTag} {p : RedexPath} :
      StepAt a r p a' → StepAt (Comb.app f a) r (Dir.R :: p) (Comb.app f a')

namespace StepAt

theorem toStep {t u : Comb} {r : RuleTag} {p : RedexPath} :
    StepAt t r p u → Comb.Step t u := by
  intro h
  induction h with
  | K_root x y =>
      simpa using (Comb.Step.K_rule (x := x) (y := y))
  | S_root x y z =>
      simpa using (Comb.Step.S_rule (x := x) (y := y) (z := z))
  | Y_root f =>
      simpa using (Comb.Step.Y_rule (f := f))
  | left _ ih =>
      exact Comb.Step.app_left ih
  | right _ ih =>
      exact Comb.Step.app_right ih

end StepAt

/-! ## Enumerated edges carry correct position data -/

namespace StepAt

open RuleTag

theorem rootStep?_stepAt {t : Comb} {r : RuleTag} {u : Comb} :
    rootStep? t = some (r, u) → StepAt t r [] u := by
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
          have : some (RuleTag.Y, Comb.app a (Comb.app .Y a)) = some (r, u) := by
            simpa [rootStep?] using h
          cases this
          exact StepAt.Y_root a
      | app f1 arg =>
          cases f1 with
          | K =>
              have : some (RuleTag.K, arg) = some (r, u) := by
                simpa [rootStep?] using h
              cases this
              exact StepAt.K_root u a
          | S =>
              simp [rootStep?] at h
          | Y =>
              simp [rootStep?] at h
          | app f11 f12 =>
              cases f11 with
              | S =>
                  have :
                      some (RuleTag.S, Comb.app (Comb.app f12 a) (Comb.app arg a)) =
                        some (r, u) := by
                    simpa [rootStep?] using h
                  cases this
                  exact StepAt.S_root f12 arg a
              | _ =>
                  simp [rootStep?] at h

theorem stepAt_of_stepEdgesList :
    ∀ {t : Comb} {ed : EventData} {u : Comb},
      (ed, u) ∈ stepEdgesList t → StepAt t ed.rule ed.path u := by
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
      have hrootOrRest :
          (ed, u) ∈ rootEdgesList (Comb.app f a) ∨
            (ed, u) ∈ (stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f) := by
        simpa [stepEdgesList] using (List.mem_append.1 hmem)
      rcases hrootOrRest with hroot | hrest
      ·
        cases h0 : rootStep? (Comb.app f a) with
        | none =>
            simp [rootEdgesList, h0] at hroot
        | some ru =>
            rcases ru with ⟨r0, u0⟩
            have hEq : (ed, u) = ({ rule := r0, path := [] }, u0) := by
              simpa [rootEdgesList, h0] using hroot
            cases hEq
            exact rootStep?_stepAt (t := Comb.app f a) (r := r0) (u := u) h0
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
          have hat : StepAt f ed0.rule ed0.path u0 := ihf (ed := ed0) (u := u0) hp
          exact StepAt.left hat
        ·
          rcases (List.mem_map.1 hright) with ⟨p, hp, hpEq⟩
          rcases p with ⟨ed0, u0⟩
          cases hpEq
          have hat : StepAt a ed0.rule ed0.path u0 := iha (ed := ed0) (u := u0) hp
          exact StepAt.right hat

theorem stepAt_of_stepEdges {t : Comb} {ed : EventData} {u : Comb} :
    (ed, u) ∈ stepEdges t → StepAt t ed.rule ed.path u := by
  intro h
  have h' : (ed, u) ∈ stepEdgesList t := (mem_stepEdges_iff (t := t) (e := (ed, u))).1 h
  exact stepAt_of_stepEdgesList (t := t) (ed := ed) (u := u) h'

/-- Any positioned one-step reduction appears in the edge enumerator with the matching label. -/
theorem mem_stepEdgesList_of_stepAt :
    ∀ {t : Comb} {r : RuleTag} {p : RedexPath} {u : Comb},
      StepAt t r p u → ({ rule := r, path := p }, u) ∈ stepEdgesList t := by
  intro t r p u h
  induction h with
  | K_root x y =>
      simp [stepEdgesList, rootEdgesList, rootStep?]
  | S_root x y z =>
      simp [stepEdgesList, rootEdgesList, rootStep?]
  | Y_root f =>
      simp [stepEdgesList, rootEdgesList, rootStep?]
  | left h ih =>
      rename_i f a f' r p
      have hmap :
          ({ rule := r, path := Dir.L :: p }, Comb.app f' a) ∈
            (stepEdgesList f).map (liftLeft a) := by
        refine List.mem_map.2 ?_
        refine ⟨({ rule := r, path := p }, f'), ih, ?_⟩
        rfl
      have hrest :
          ({ rule := r, path := Dir.L :: p }, Comb.app f' a) ∈
            (stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f) :=
        List.mem_append_left _ hmap
      have hAll :
          ({ rule := r, path := Dir.L :: p }, Comb.app f' a) ∈
            rootEdgesList (Comb.app f a) ++
              ((stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f)) :=
        List.mem_append_right _ hrest
      simpa [stepEdgesList] using hAll
  | right h ih =>
      rename_i f a a' r p
      have hmap :
          ({ rule := r, path := Dir.R :: p }, Comb.app f a') ∈
            (stepEdgesList a).map (liftRight f) := by
        refine List.mem_map.2 ?_
        refine ⟨({ rule := r, path := p }, a'), ih, ?_⟩
        rfl
      have hrest :
          ({ rule := r, path := Dir.R :: p }, Comb.app f a') ∈
            (stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f) :=
        List.mem_append_right _ hmap
      have hAll :
          ({ rule := r, path := Dir.R :: p }, Comb.app f a') ∈
            rootEdgesList (Comb.app f a) ++
              ((stepEdgesList f).map (liftLeft a) ++ (stepEdgesList a).map (liftRight f)) :=
        List.mem_append_right _ hrest
      simpa [stepEdgesList] using hAll

/-- Positioned reduction ↔ edge-list membership (exact label). -/
theorem stepAt_iff_mem_stepEdgesList {t : Comb} {r : RuleTag} {p : RedexPath} {u : Comb} :
    StepAt t r p u ↔ ({ rule := r, path := p }, u) ∈ stepEdgesList t := by
  constructor
  · intro h
    exact mem_stepEdgesList_of_stepAt (t := t) (r := r) (p := p) (u := u) h
  · intro h
    exact StepAt.stepAt_of_stepEdgesList (t := t) (ed := { rule := r, path := p }) (u := u) h

/-- Positioned reduction ↔ edge-set membership (exact label). -/
theorem stepAt_iff_mem_stepEdges {t : Comb} {r : RuleTag} {p : RedexPath} {u : Comb} :
    StepAt t r p u ↔ ({ rule := r, path := p }, u) ∈ stepEdges t := by
  constructor
  · intro h
    exact (mem_stepEdges_iff (t := t) (e := ({ rule := r, path := p }, u))).2 (mem_stepEdgesList_of_stepAt h)
  · intro h
    exact StepAt.stepAt_of_stepEdges (t := t) (ed := { rule := r, path := p }) (u := u) h

end StepAt

/-! ## Any `Step` has a position -/

namespace Step

theorem exists_stepAt {t u : Comb} (h : Comb.Step t u) :
    ∃ r : RuleTag, ∃ p : RedexPath, StepAt t r p u := by
  induction h with
  | K_rule x y =>
      exact ⟨RuleTag.K, [], StepAt.K_root x y⟩
  | S_rule x y z =>
      exact ⟨RuleTag.S, [], StepAt.S_root x y z⟩
  | Y_rule f =>
      exact ⟨RuleTag.Y, [], StepAt.Y_root f⟩
  | app_left h ih =>
      rcases ih with ⟨r, p, hp⟩
      exact ⟨r, Dir.L :: p, StepAt.left hp⟩
  | app_right h ih =>
      rcases ih with ⟨r, p, hp⟩
      exact ⟨r, Dir.R :: p, StepAt.right hp⟩

end Step

/-! ## Prefix/disjointness of redex paths -/

namespace RedexPath

/-- `Prefix p q` means `p` is a prefix of `q` (i.e. `q = p ++ r` for some suffix `r`). -/
def Prefix (p q : RedexPath) : Prop :=
  ∃ r : RedexPath, q = p ++ r

theorem prefix_nil_left (p : RedexPath) : Prefix [] p :=
  ⟨p, by simp⟩

theorem prefix_cons_same {d : Dir} {p q : RedexPath} (h : Prefix p q) : Prefix (d :: p) (d :: q) := by
  rcases h with ⟨r, rfl⟩
  refine ⟨r, ?_⟩
  simp

theorem prefix_of_cons_same {d : Dir} {p q : RedexPath} : Prefix (d :: p) (d :: q) → Prefix p q := by
  rintro ⟨r, hr⟩
  -- Cancel the common head `d`.
  have : q = p ++ r := by
    simpa using congrArg List.tail hr
  exact ⟨r, this⟩

/-- Two paths are *disjoint* if neither is a prefix of the other (i.e. the corresponding redexes are non-overlapping). -/
def Disjoint (p q : RedexPath) : Prop :=
  ¬ Prefix p q ∧ ¬ Prefix q p

theorem disjoint_of_cons_same_left {d : Dir} {p q : RedexPath} :
    Disjoint (d :: p) (d :: q) → Disjoint p q := by
  intro h
  refine ⟨?_, ?_⟩
  · intro hpq
    exact h.1 (prefix_cons_same (d := d) hpq)
  · intro hqp
    exact h.2 (prefix_cons_same (d := d) hqp)

end RedexPath

/-! ## Commutation of disjoint one-step reductions -/

namespace StepAt

open RedexPath

theorem commute_of_disjoint {t u v : Comb} {r₁ r₂ : RuleTag} {p₁ p₂ : RedexPath}
    (h₁ : StepAt t r₁ p₁ u) (h₂ : StepAt t r₂ p₂ v) (hdisj : Disjoint p₁ p₂) :
    ∃ w : Comb, StepAt u r₂ p₂ w ∧ StepAt v r₁ p₁ w := by
  induction h₁ generalizing v r₂ p₂ with
  | K_root x y =>
      exfalso
      exact hdisj.1 (prefix_nil_left p₂)
  | S_root x y z =>
      exfalso
      exact hdisj.1 (prefix_nil_left p₂)
  | Y_root f =>
      exfalso
      exact hdisj.1 (prefix_nil_left p₂)
  | left h₁f ih =>
      rename_i f a f' r₁ p₁'
      cases h₂ with
      | K_root x y =>
          exfalso
          exact hdisj.2 (prefix_nil_left (Dir.L :: p₁'))
      | S_root x y z =>
          exfalso
          exact hdisj.2 (prefix_nil_left (Dir.L :: p₁'))
      | Y_root f0 =>
          exfalso
          exact hdisj.2 (prefix_nil_left (Dir.L :: p₁'))
      | left h₂f =>
          rename_i f'' p₂'
          have hdisj' : Disjoint p₁' p₂' :=
            disjoint_of_cons_same_left (d := Dir.L) hdisj
          rcases ih (v := f'') (r₂ := r₂) (p₂ := p₂') h₂f hdisj' with ⟨w, hw1, hw2⟩
          refine ⟨Comb.app w a, StepAt.left hw1, StepAt.left hw2⟩
      | right h₂a =>
          rename_i a₂ p₂'
          refine ⟨Comb.app f' a₂, StepAt.right h₂a, StepAt.left h₁f⟩
  | right h₁a ih =>
      rename_i f a a' r₁ p₁'
      cases h₂ with
      | K_root x y =>
          exfalso
          exact hdisj.2 (prefix_nil_left (Dir.R :: p₁'))
      | S_root x y z =>
          exfalso
          exact hdisj.2 (prefix_nil_left (Dir.R :: p₁'))
      | Y_root f0 =>
          exfalso
          exact hdisj.2 (prefix_nil_left (Dir.R :: p₁'))
      | left h₂f =>
          rename_i f₂ p₂'
          refine ⟨Comb.app f₂ a', StepAt.left h₂f, StepAt.right h₁a⟩
      | right h₂a =>
          rename_i a₂ p₂'
          have hdisj' : Disjoint p₁' p₂' :=
            disjoint_of_cons_same_left (d := Dir.R) hdisj
          rcases ih (v := a₂) (r₂ := r₂) (p₂ := p₂') h₂a hdisj' with ⟨w, hw1, hw2⟩
          refine ⟨Comb.app f w, StepAt.right hw1, StepAt.right hw2⟩

end StepAt

end Comb

end LoF
end HeytingLean
