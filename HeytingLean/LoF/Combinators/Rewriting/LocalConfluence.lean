import HeytingLean.LoF.Combinators.Rewriting.StepAt

/-!
# LocalConfluence — principled joinability of one-step peaks in SKY

`Comb.StepAt` makes the redex position explicit.  This file proves that any *one-step peak*

```
    t
  ↙   ↘
 u     v
```

is **joinable** (there exists `w` with `u ↦* w` and `v ↦* w`) by a direct, rule-by-rule
analysis of:

- disjoint redexes (already handled by `StepAt.commute_of_disjoint`), and
- prefix-overlap redexes (the inner step lies inside a variable position of the outer redex).

This is a principled “completion rule” calculus for 2-cells at depth 1 (local confluence),
without any bounded search.
-/

namespace HeytingLean
namespace LoF

namespace Comb

open Dir RuleTag

/-! ## Small helper lemmas for `Comb.Steps` -/

namespace StepsLemmas

theorem trans {t u v : Comb} : Comb.Steps t u → Comb.Steps u v → Comb.Steps t v := by
  intro htu huv
  induction htu with
  | refl _ =>
      simpa using huv
  | trans hstep hsteps ih =>
      exact Comb.Steps.trans hstep (ih huv)

theorem app_left {f f' a : Comb} :
    Comb.Steps f f' → Comb.Steps (Comb.app f a) (Comb.app f' a) := by
  intro h
  induction h with
  | refl f =>
      exact Comb.Steps.refl (Comb.app f a)
  | trans hstep hsteps ih =>
      exact Comb.Steps.trans (Comb.Step.app_left hstep) ih

theorem app_right {f a a' : Comb} :
    Comb.Steps a a' → Comb.Steps (Comb.app f a) (Comb.app f a') := by
  intro h
  induction h with
  | refl a =>
      exact Comb.Steps.refl (Comb.app f a)
  | trans hstep hsteps ih =>
      exact Comb.Steps.trans (Comb.Step.app_right hstep) ih

end StepsLemmas

/-! ## Joinability for prefix-overlap peaks -/

namespace StepAt

open RedexPath
open StepsLemmas

variable {t u v : Comb}

/-- If two positioned one-step reductions start at the same redex position (one position is a
prefix of the other), then the resulting peak is joinable. -/
theorem join_of_prefix
    {r₁ r₂ : RuleTag} {p₁ p₂ : RedexPath}
    (h₁ : StepAt t r₁ p₁ u) (h₂ : StepAt t r₂ p₂ v) (hp : Prefix p₁ p₂) :
    ∃ w : Comb, Comb.Steps u w ∧ Comb.Steps v w := by
  induction h₁ generalizing v r₂ p₂ with
  | K_root x y =>
      -- `t = (K · x) · y`, `u = x`.
      cases h₂ with
      | K_root x2 y2 =>
          refine ⟨x, Comb.Steps.refl x, Comb.Steps.refl x⟩
      | left h₂f =>
          -- The only possible step inside `(K · x)` is inside `x` (right child).
          cases h₂f with
          | left h₂K =>
              cases h₂K
          | right h₂x =>
              rename_i x' p₂'
              -- Peak:
              --   x  <-  (K x y)
              --   (K x' y)  -> x'  (after K-root)
              refine ⟨x', ?_, ?_⟩
              · exact Comb.Steps.trans (StepAt.toStep h₂x) (Comb.Steps.refl x')
              ·
                have hK : StepAt (Comb.app (Comb.app .K x') y) .K [] x' :=
                  StepAt.K_root x' y
                exact Comb.Steps.trans (StepAt.toStep hK) (Comb.Steps.refl x')
      | right h₂y =>
          -- Step inside the discarded argument `y`: K-root still joins back to `x`.
          rename_i y' p₂'
          refine ⟨x, Comb.Steps.refl x, ?_⟩
          have hK : StepAt (Comb.app (Comb.app .K x) y') .K [] x :=
            StepAt.K_root x y'
          exact Comb.Steps.trans (StepAt.toStep hK) (Comb.Steps.refl x)
  | S_root x y z =>
      -- `t = (((S · x) · y) · z)`, `u = (x · z) · (y · z)`.
      cases h₂ with
      | S_root x2 y2 z2 =>
          refine ⟨Comb.app (Comb.app x z) (Comb.app y z), Comb.Steps.refl _, Comb.Steps.refl _⟩
      | right h₂z =>
          -- Step inside duplicated argument `z`: need two post-steps on the root-first branch.
          rename_i z' p₂'
          have hz : Comb.Step z z' := StepAt.toStep h₂z
          let w : Comb := Comb.app (Comb.app x z') (Comb.app y z')
          refine ⟨w, ?_, ?_⟩
          · -- Reduce `z` in both copies inside `u`.
            have h1 :
                Comb.Step (Comb.app (Comb.app x z) (Comb.app y z))
                  (Comb.app (Comb.app x z') (Comb.app y z)) := by
              exact Comb.Step.app_left (Comb.Step.app_right hz)
            have h2 :
                Comb.Step (Comb.app (Comb.app x z') (Comb.app y z))
                  (Comb.app (Comb.app x z') (Comb.app y z')) := by
              exact Comb.Step.app_right (Comb.Step.app_right hz)
            refine Comb.Steps.trans h1 (Comb.Steps.trans h2 (Comb.Steps.refl w))
          · -- Root `S` step after stepping `z`.
            have hS : StepAt (Comb.app (Comb.app (Comb.app .S x) y) z') .S [] w :=
              StepAt.S_root x y z'
            exact Comb.Steps.trans (StepAt.toStep hS) (Comb.Steps.refl w)
      | left h₂f =>
          -- Step inside the function part `((S · x) · y)`: it must be inside `x` or `y`.
          cases h₂f with
          | right h₂y =>
              -- Step inside `y` (right argument).
              rename_i y' p₂'
              have hy : Comb.Step y y' := StepAt.toStep h₂y
              let w : Comb := Comb.app (Comb.app x z) (Comb.app y' z)
              refine ⟨w, ?_, ?_⟩
              ·
                have hstep :
                    Comb.Step (Comb.app (Comb.app x z) (Comb.app y z))
                      (Comb.app (Comb.app x z) (Comb.app y' z)) := by
                  exact Comb.Step.app_right (Comb.Step.app_left hy)
                exact Comb.Steps.trans hstep (Comb.Steps.refl w)
              ·
                have hS : StepAt (Comb.app (Comb.app (Comb.app .S x) y') z) .S [] w :=
                  StepAt.S_root x y' z
                exact Comb.Steps.trans (StepAt.toStep hS) (Comb.Steps.refl w)
          | left h₂Sx =>
              -- Step inside `(S · x)`: it must be inside `x` (right argument).
              cases h₂Sx with
              | left h₂S =>
                  cases h₂S
              | right h₂x =>
                  rename_i x' p₂'
                  have hx : Comb.Step x x' := StepAt.toStep h₂x
                  let w : Comb := Comb.app (Comb.app x' z) (Comb.app y z)
                  refine ⟨w, ?_, ?_⟩
                  ·
                    have hstep :
                        Comb.Step (Comb.app (Comb.app x z) (Comb.app y z))
                          (Comb.app (Comb.app x' z) (Comb.app y z)) := by
                      exact Comb.Step.app_left (Comb.Step.app_left hx)
                    exact Comb.Steps.trans hstep (Comb.Steps.refl w)
                  ·
                    have hS : StepAt (Comb.app (Comb.app (Comb.app .S x') y) z) .S [] w :=
                      StepAt.S_root x' y z
                    exact Comb.Steps.trans (StepAt.toStep hS) (Comb.Steps.refl w)
  | Y_root f =>
      -- `t = Y · f`, `u = f · (Y · f)`; overlap duplicates `f`.
      cases h₂ with
      | Y_root f2 =>
          refine ⟨Comb.app f (Comb.app .Y f), Comb.Steps.refl _, Comb.Steps.refl _⟩
      | left h₂Y =>
          cases h₂Y
      | right h₂f =>
          rename_i f' p₂'
          have hf : Comb.Step f f' := StepAt.toStep h₂f
          let w : Comb := Comb.app f' (Comb.app .Y f')
          refine ⟨w, ?_, ?_⟩
          ·
            -- Reduce both copies of `f` appearing in `u`.
            have h1 :
                Comb.Step (Comb.app f (Comb.app .Y f))
                  (Comb.app f' (Comb.app .Y f)) := by
              exact Comb.Step.app_left hf
            have h2 :
                Comb.Step (Comb.app f' (Comb.app .Y f))
                  (Comb.app f' (Comb.app .Y f')) := by
              exact Comb.Step.app_right (Comb.Step.app_right hf)
            refine Comb.Steps.trans h1 (Comb.Steps.trans h2 (Comb.Steps.refl w))
          ·
            have hY : StepAt (Comb.app .Y f') .Y [] w :=
              StepAt.Y_root f'
            exact Comb.Steps.trans (StepAt.toStep hY) (Comb.Steps.refl w)
  | left h₁f ih =>
      -- Peel the common `L` prefix.
      rename_i f a f' r₁ p₁'
      rcases hp with ⟨suffix, rfl⟩
      cases h₂ with
      | left h₂f =>
          rename_i f₂
          have hp' : Prefix p₁' (p₁' ++ suffix) := ⟨suffix, by simp⟩
          rcases ih (v := f₂) (r₂ := r₂) (p₂ := p₁' ++ suffix) h₂f hp' with ⟨w, hw₁, hw₂⟩
          refine ⟨Comb.app w a, ?_, ?_⟩
          · exact StepsLemmas.app_left (a := a) hw₁
          · exact StepsLemmas.app_left (a := a) hw₂
  | right h₁a ih =>
      -- Peel the common `R` prefix.
      rename_i f a a' r₁ p₁'
      rcases hp with ⟨suffix, rfl⟩
      cases h₂ with
      | right h₂a =>
          rename_i a₂
          have hp' : Prefix p₁' (p₁' ++ suffix) := ⟨suffix, by simp⟩
          rcases ih (v := a₂) (r₂ := r₂) (p₂ := p₁' ++ suffix) h₂a hp' with ⟨w, hw₁, hw₂⟩
          refine ⟨Comb.app f w, ?_, ?_⟩
          · exact StepsLemmas.app_right (f := f) hw₁
          · exact StepsLemmas.app_right (f := f) hw₂

/-- Determinism of `StepAt` at a fixed position: the target term is unique. -/
theorem target_eq_of_same_path
    {t u v : Comb} {r₁ r₂ : RuleTag} {p : RedexPath}
    (h₁ : StepAt t r₁ p u) (h₂ : StepAt t r₂ p v) :
    u = v := by
  induction h₁ generalizing v r₂ with
  | K_root x y =>
      cases h₂ with
      | K_root _ _ =>
          rfl
  | S_root x y z =>
      cases h₂ with
      | S_root _ _ _ =>
          rfl
  | Y_root f =>
      cases h₂ with
      | Y_root _ =>
          rfl
  | left h₁f ih =>
      rename_i f a f' r p
      cases h₂ with
      | left h₂f =>
          rename_i f₂
          have hf : f' = f₂ := ih (v := f₂) (r₂ := r₂) h₂f
          simp [hf]
  | right h₁a ih =>
      rename_i f a a' r p
      cases h₂ with
      | right h₂a =>
          rename_i a₂
          have ha : a' = a₂ := ih (v := a₂) (r₂ := r₂) h₂a
          simp [ha]

/-- Any one-step peak of positioned reductions is joinable (local confluence at `StepAt`). -/
theorem local_confluence
    {r₁ r₂ : RuleTag} {p₁ p₂ : RedexPath}
    (h₁ : StepAt t r₁ p₁ u) (h₂ : StepAt t r₂ p₂ v) :
    ∃ w : Comb, Comb.Steps u w ∧ Comb.Steps v w := by
  classical
  by_cases hEq : p₁ = p₂
  · subst hEq
    have huv : u = v := target_eq_of_same_path (h₁ := h₁) (h₂ := h₂)
    refine ⟨u, Comb.Steps.refl u, ?_⟩
    exact Comb.Steps.of_eq huv.symm
  · by_cases hdisj : Disjoint p₁ p₂
    · rcases StepAt.commute_of_disjoint (h₁ := h₁) (h₂ := h₂) hdisj with ⟨w, hw1, hw2⟩
      refine ⟨w, ?_, ?_⟩
      · exact Comb.Steps.trans (StepAt.toStep hw1) (Comb.Steps.refl w)
      · exact Comb.Steps.trans (StepAt.toStep hw2) (Comb.Steps.refl w)
    · -- Overlap case: one path is a prefix of the other.
      have hprefix : Prefix p₁ p₂ ∨ Prefix p₂ p₁ := by
        by_contra hno
        apply hdisj
        refine ⟨?_, ?_⟩
        · intro hp12; exact hno (Or.inl hp12)
        · intro hp21; exact hno (Or.inr hp21)
      rcases hprefix with hp12 | hp21
      · exact join_of_prefix (h₁ := h₁) (h₂ := h₂) hp12
      ·
        rcases join_of_prefix (h₁ := h₂) (h₂ := h₁) hp21 with ⟨w, hvw, huw⟩
        exact ⟨w, huw, hvw⟩

end StepAt

/-! ## Corollary: `Comb.Step` is locally confluent -/

namespace Step

open RedexPath

theorem local_confluence {t u v : Comb} (h₁ : Comb.Step t u) (h₂ : Comb.Step t v) :
    ∃ w : Comb, Comb.Steps u w ∧ Comb.Steps v w := by
  rcases Comb.Step.exists_stepAt (t := t) (u := u) h₁ with ⟨r₁, p₁, h₁at⟩
  rcases Comb.Step.exists_stepAt (t := t) (u := v) h₂ with ⟨r₂, p₂, h₂at⟩
  exact StepAt.local_confluence (t := t) (u := u) (v := v) h₁at h₂at

end Step

end Comb

end LoF
end HeytingLean
