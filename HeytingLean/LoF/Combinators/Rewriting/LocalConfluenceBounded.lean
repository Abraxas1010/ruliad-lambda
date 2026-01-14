import HeytingLean.LoF.Combinators.Rewriting.LocalConfluence

/-!
# LocalConfluenceBounded — local confluence with a uniform small join bound

`LocalConfluence.lean` proves that any one-step peak in SKY is joinable:

```
    t
  ↙   ↘
 u     v
```

This file strengthens that result by proving that the join can always be found within **at most two**
further one-step reductions on each side.  This is the first “paper-shaped” computability boundary
needed for a completion-rule / critical-pair calculus:

- join witnesses exist **without any search**, and
- the join depth is **uniformly bounded** for one-step peaks.

We keep the statement in the thin (`Prop`) world (`Comb.Step` / `Comb.Steps`) by introducing
`Comb.StepsUpTo2`, a tiny bounded closure that records only 0/1/2-step paths.
-/

namespace HeytingLean
namespace LoF

namespace Comb

open Dir RuleTag

/-! ## Bounded multi-step relation (≤ 2) -/

/-- A bounded version of `Comb.Steps` that records only 0/1/2-step reachability. -/
inductive StepsUpTo2 : Comb → Comb → Prop where
  | refl (t : Comb) : StepsUpTo2 t t
  | step {t u : Comb} : Step t u → StepsUpTo2 t u
  | step2 {t u v : Comb} : Step t u → Step u v → StepsUpTo2 t v

namespace StepsUpTo2

theorem toSteps {t u : Comb} : StepsUpTo2 t u → Steps t u := by
  intro h
  cases h with
  | refl =>
      exact Steps.refl t
  | step htu =>
      exact Steps.trans htu (Steps.refl _)
  | step2 htu huv =>
      exact Steps.trans htu (Steps.trans huv (Steps.refl _))

theorem app_left {f f' a : Comb} :
    StepsUpTo2 f f' → StepsUpTo2 (Comb.app f a) (Comb.app f' a) := by
  intro h
  cases h with
  | refl =>
      exact StepsUpTo2.refl (Comb.app f a)
  | step hff' =>
      exact StepsUpTo2.step (Step.app_left hff')
  | step2 h1 h2 =>
      exact StepsUpTo2.step2 (Step.app_left h1) (Step.app_left h2)

theorem app_right {f a a' : Comb} :
    StepsUpTo2 a a' → StepsUpTo2 (Comb.app f a) (Comb.app f a') := by
  intro h
  cases h with
  | refl =>
      exact StepsUpTo2.refl (Comb.app f a)
  | step haa' =>
      exact StepsUpTo2.step (Step.app_right haa')
  | step2 h1 h2 =>
      exact StepsUpTo2.step2 (Step.app_right h1) (Step.app_right h2)

end StepsUpTo2

/-! ## Local confluence with ≤2 join depth -/

namespace StepAt

open RedexPath
open StepsUpTo2

variable {t u v : Comb}

/-- Prefix-overlap peaks have a join with at most two steps on each side. -/
theorem join_of_prefix_upTo2
    {r₁ r₂ : RuleTag} {p₁ p₂ : RedexPath}
    (h₁ : StepAt t r₁ p₁ u) (h₂ : StepAt t r₂ p₂ v) (hp : Prefix p₁ p₂) :
    ∃ w : Comb, StepsUpTo2 u w ∧ StepsUpTo2 v w := by
  induction h₁ generalizing v r₂ p₂ with
  | K_root x y =>
      cases h₂ with
      | K_root _ _ =>
          refine ⟨x, StepsUpTo2.refl x, StepsUpTo2.refl x⟩
      | left h₂f =>
          cases h₂f with
          | left h₂K =>
              cases h₂K
          | right h₂x =>
              rename_i x' p₂'
              refine ⟨x', StepsUpTo2.step (StepAt.toStep h₂x), ?_⟩
              have hK : StepAt (Comb.app (Comb.app .K x') y) .K [] x' :=
                StepAt.K_root x' y
              exact StepsUpTo2.step (StepAt.toStep hK)
      | right h₂y =>
          rename_i y' p₂'
          refine ⟨x, StepsUpTo2.refl x, ?_⟩
          have hK : StepAt (Comb.app (Comb.app .K x) y') .K [] x :=
            StepAt.K_root x y'
          exact StepsUpTo2.step (StepAt.toStep hK)
  | S_root x y z =>
      cases h₂ with
      | S_root _ _ _ =>
          refine ⟨Comb.app (Comb.app x z) (Comb.app y z), StepsUpTo2.refl _, StepsUpTo2.refl _⟩
      | right h₂z =>
          rename_i z' p₂'
          have hz : Step z z' := StepAt.toStep h₂z
          let w : Comb := Comb.app (Comb.app x z') (Comb.app y z')
          refine ⟨w, ?_, ?_⟩
          ·
            have h1 :
                Step (Comb.app (Comb.app x z) (Comb.app y z))
                  (Comb.app (Comb.app x z') (Comb.app y z)) := by
              exact Step.app_left (Step.app_right hz)
            have h2 :
                Step (Comb.app (Comb.app x z') (Comb.app y z))
                  (Comb.app (Comb.app x z') (Comb.app y z')) := by
              exact Step.app_right (Step.app_right hz)
            exact StepsUpTo2.step2 h1 h2
          ·
            have hS : StepAt (Comb.app (Comb.app (Comb.app .S x) y) z') .S [] w :=
              StepAt.S_root x y z'
            exact StepsUpTo2.step (StepAt.toStep hS)
      | left h₂f =>
          cases h₂f with
          | right h₂y =>
              rename_i y' p₂'
              have hy : Step y y' := StepAt.toStep h₂y
              let w : Comb := Comb.app (Comb.app x z) (Comb.app y' z)
              refine ⟨w, ?_, ?_⟩
              ·
                have hstep :
                    Step (Comb.app (Comb.app x z) (Comb.app y z))
                      (Comb.app (Comb.app x z) (Comb.app y' z)) := by
                  exact Step.app_right (Step.app_left hy)
                exact StepsUpTo2.step hstep
              ·
                have hS : StepAt (Comb.app (Comb.app (Comb.app .S x) y') z) .S [] w :=
                  StepAt.S_root x y' z
                exact StepsUpTo2.step (StepAt.toStep hS)
          | left h₂Sx =>
              cases h₂Sx with
              | left h₂S =>
                  cases h₂S
              | right h₂x =>
                  rename_i x' p₂'
                  have hx : Step x x' := StepAt.toStep h₂x
                  let w : Comb := Comb.app (Comb.app x' z) (Comb.app y z)
                  refine ⟨w, ?_, ?_⟩
                  ·
                    have hstep :
                        Step (Comb.app (Comb.app x z) (Comb.app y z))
                          (Comb.app (Comb.app x' z) (Comb.app y z)) := by
                      exact Step.app_left (Step.app_left hx)
                    exact StepsUpTo2.step hstep
                  ·
                    have hS : StepAt (Comb.app (Comb.app (Comb.app .S x') y) z) .S [] w :=
                      StepAt.S_root x' y z
                    exact StepsUpTo2.step (StepAt.toStep hS)
  | Y_root f =>
      cases h₂ with
      | Y_root _ =>
          refine ⟨Comb.app f (Comb.app .Y f), StepsUpTo2.refl _, StepsUpTo2.refl _⟩
      | left h₂Y =>
          cases h₂Y
      | right h₂f =>
          rename_i f' p₂'
          have hf : Step f f' := StepAt.toStep h₂f
          let w : Comb := Comb.app f' (Comb.app .Y f')
          refine ⟨w, ?_, ?_⟩
          ·
            have h1 :
                Step (Comb.app f (Comb.app .Y f))
                  (Comb.app f' (Comb.app .Y f)) := by
              exact Step.app_left hf
            have h2 :
                Step (Comb.app f' (Comb.app .Y f))
                  (Comb.app f' (Comb.app .Y f')) := by
              exact Step.app_right (Step.app_right hf)
            exact StepsUpTo2.step2 h1 h2
          ·
            have hY : StepAt (Comb.app .Y f') .Y [] w :=
              StepAt.Y_root f'
            exact StepsUpTo2.step (StepAt.toStep hY)
  | left h₁f ih =>
      rename_i f a f' r₁ p₁'
      rcases hp with ⟨suffix, rfl⟩
      cases h₂ with
      | left h₂f =>
          rename_i f₂
          have hp' : Prefix p₁' (p₁' ++ suffix) := ⟨suffix, by simp⟩
          rcases ih (v := f₂) (r₂ := r₂) (p₂ := p₁' ++ suffix) h₂f hp' with ⟨w, hw₁, hw₂⟩
          refine ⟨Comb.app w a, ?_, ?_⟩
          · exact StepsUpTo2.app_left (a := a) hw₁
          · exact StepsUpTo2.app_left (a := a) hw₂
  | right h₁a ih =>
      rename_i f a a' r₁ p₁'
      rcases hp with ⟨suffix, rfl⟩
      cases h₂ with
      | right h₂a =>
          rename_i a₂
          have hp' : Prefix p₁' (p₁' ++ suffix) := ⟨suffix, by simp⟩
          rcases ih (v := a₂) (r₂ := r₂) (p₂ := p₁' ++ suffix) h₂a hp' with ⟨w, hw₁, hw₂⟩
          refine ⟨Comb.app f w, ?_, ?_⟩
          · exact StepsUpTo2.app_right (f := f) hw₁
          · exact StepsUpTo2.app_right (f := f) hw₂

/-- Any one-step peak of positioned reductions is joinable within 2 further steps on each side. -/
theorem local_confluence_upTo2
    {r₁ r₂ : RuleTag} {p₁ p₂ : RedexPath}
    (h₁ : StepAt t r₁ p₁ u) (h₂ : StepAt t r₂ p₂ v) :
    ∃ w : Comb, StepsUpTo2 u w ∧ StepsUpTo2 v w := by
  classical
  by_cases hEq : p₁ = p₂
  · subst hEq
    have huv : u = v := target_eq_of_same_path (h₁ := h₁) (h₂ := h₂)
    refine ⟨u, StepsUpTo2.refl u, ?_⟩
    subst huv
    exact StepsUpTo2.refl u
  · by_cases hdisj : Disjoint p₁ p₂
    ·
      rcases StepAt.commute_of_disjoint (h₁ := h₁) (h₂ := h₂) hdisj with ⟨w, hw1, hw2⟩
      refine ⟨w, StepsUpTo2.step (StepAt.toStep hw1), StepsUpTo2.step (StepAt.toStep hw2)⟩
    ·
      have hprefix : Prefix p₁ p₂ ∨ Prefix p₂ p₁ := by
        by_contra hno
        apply hdisj
        refine ⟨?_, ?_⟩
        · intro hp12; exact hno (Or.inl hp12)
        · intro hp21; exact hno (Or.inr hp21)
      rcases hprefix with hp12 | hp21
      · exact join_of_prefix_upTo2 (h₁ := h₁) (h₂ := h₂) hp12
      ·
        rcases join_of_prefix_upTo2 (h₁ := h₂) (h₂ := h₁) hp21 with ⟨w, hvw, huw⟩
        exact ⟨w, huw, hvw⟩

end StepAt

namespace Step

theorem local_confluence_upTo2 {t u v : Comb} (h₁ : Comb.Step t u) (h₂ : Comb.Step t v) :
    ∃ w : Comb, Comb.StepsUpTo2 u w ∧ Comb.StepsUpTo2 v w := by
  rcases Comb.Step.exists_stepAt (t := t) (u := u) h₁ with ⟨r₁, p₁, h₁at⟩
  rcases Comb.Step.exists_stepAt (t := t) (u := v) h₂ with ⟨r₂, p₂, h₂at⟩
  exact StepAt.local_confluence_upTo2 (t := t) (u := u) (v := v) h₁at h₂at

end Step

end Comb

end LoF
end HeytingLean
