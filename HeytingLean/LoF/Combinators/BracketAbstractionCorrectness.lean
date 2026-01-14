import HeytingLean.LoF.Combinators.BracketAbstraction

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Bracket abstraction correctness (Phase 2)

This file proves a β-simulation theorem for the bracket abstraction compiler
`HeytingLean.LoF.Combinators.Bracket.CExp.bracket`, including the two Turner-style
optimizations implemented in `CExp.opt`.

The main result is a **joinability** statement: for any expression `e`,
the application `([x]e) v` and the substituted denotation `e[v/x]` reduce to a
common SKY term.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

open HeytingLean.LoF

namespace Bracket
namespace CExp

variable {Var : Type} [DecidableEq Var]

def update (ρ : Var → Comb) (x : Var) (v : Comb) : Var → Comb :=
  fun y => if y = x then v else ρ y

/-! ## `Comb.Steps` helpers -/

private theorem steps_transitive {t u v : Comb} :
    Comb.Steps t u → Comb.Steps u v → Comb.Steps t v := by
  intro htu huv
  induction htu with
  | refl _ => simpa using huv
  | trans hstep hsteps ih => exact Comb.Steps.trans hstep (ih huv)

private theorem steps_app_left {f f' a : Comb} :
    Comb.Steps f f' → Comb.Steps (Comb.app f a) (Comb.app f' a) := by
  intro h
  induction h with
  | refl t => exact Comb.Steps.refl (Comb.app t a)
  | trans hstep hsteps ih =>
      exact Comb.Steps.trans (Comb.Step.app_left hstep) ih

private theorem steps_app_right {f a a' : Comb} :
    Comb.Steps a a' → Comb.Steps (Comb.app f a) (Comb.app f a') := by
  intro h
  induction h with
  | refl t => exact Comb.Steps.refl (Comb.app f t)
  | trans hstep hsteps ih =>
      exact Comb.Steps.trans (Comb.Step.app_right hstep) ih

/-! ## Basic lemmas used in the main proof -/

theorem bracket_eq_appK_of_occurs_false (x : Var) :
    ∀ e : CExp Var, occurs x e = false → bracket x e = CExp.app CExp.K e := by
  intro e
  induction e with
  | var y =>
      intro h
      by_cases hy : y = x
      · subst hy
        simp [occurs] at h
      · simp [bracket, hy]
  | K =>
      intro _
      simp [bracket]
  | S =>
      intro _
      simp [bracket]
  | Y =>
      intro _
      simp [bracket]
  | app f a ihf iha =>
      intro h
      have hfa : occurs x f = false ∧ occurs x a = false := by
        simpa [occurs] using h
      simp [bracket, hfa.1, hfa.2]

theorem denote_update_eq_of_occurs_false (ρ : Var → Comb) (x : Var) (v : Comb) :
    ∀ e : CExp Var, occurs x e = false → denote (update ρ x v) e = denote ρ e := by
  intro e
  induction e with
  | var y =>
      intro h
      by_cases hy : y = x
      · subst hy
        simp [occurs] at h
      · simp [denote, update, hy]
  | K =>
      intro _
      simp [denote]
  | S =>
      intro _
      simp [denote]
  | Y =>
      intro _
      simp [denote]
  | app f a ihf iha =>
      intro h
      have hfa : occurs x f = false ∧ occurs x a = false := by
        simpa [occurs] using h
      have hf : denote (update ρ x v) f = denote ρ f := ihf hfa.1
      have ha : denote (update ρ x v) a = denote ρ a := iha hfa.2
      simp [denote, hf, ha]

theorem bracket_beta_join_of_occurs_false (ρ : Var → Comb) (x : Var) (e : CExp Var) (v : Comb)
    (hocc : occurs x e = false) :
    ∃ r : Comb, Comb.Steps (Comb.app (denote ρ (bracket x e)) v) r ∧
      Comb.Steps (denote (update ρ x v) e) r := by
  refine ⟨denote ρ e, ?_, ?_⟩
  · have hb : bracket x e = CExp.app CExp.K e :=
      bracket_eq_appK_of_occurs_false (x := x) (e := e) hocc
    refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
    simpa [denote, hb] using (Comb.Step.K_rule (x := denote ρ e) (y := v))
  · have hden : denote (update ρ x v) e = denote ρ e :=
      denote_update_eq_of_occurs_false (ρ := ρ) (x := x) (v := v) e hocc
    exact Comb.Steps.of_eq hden

/-! ## Turner-optimization specialized lemmas -/

/-- If `[x]e = K t`, then `e[v/x] →* ⟦t⟧` (denotation under the original environment). -/
theorem denote_update_steps_of_bracket_eq_appK (ρ : Var → Comb) (x : Var) (v : Comb) :
    ∀ e t : CExp Var,
      bracket x e = CExp.app CExp.K t → Comb.Steps (denote (update ρ x v) e) (denote ρ t) := by
  intro e
  induction e with
  | var y =>
      intro t hK
      by_cases hy : y = x
      · subst hy
        simp [CExp.bracket, CExp.I] at hK
      ·
        -- `[x]y = K y` for `y ≠ x`.
        have ht : t = CExp.var y := by
          have hEq : CExp.app CExp.K (CExp.var y) = CExp.app CExp.K t := by
            simpa [CExp.bracket, hy] using hK
          cases hEq
          rfl
        subst ht
        simpa [denote, update, hy] using (Comb.Steps.refl (ρ y))
  | K =>
      intro t hK
      have ht : t = CExp.K := by
        have hEq : CExp.app CExp.K CExp.K = CExp.app CExp.K t := by
          simpa [CExp.bracket] using hK
        cases hEq
        rfl
      subst ht
      exact Comb.Steps.refl _
  | S =>
      intro t hK
      have ht : t = CExp.S := by
        have hEq : CExp.app CExp.K CExp.S = CExp.app CExp.K t := by
          simpa [CExp.bracket] using hK
        cases hEq
        rfl
      subst ht
      exact Comb.Steps.refl _
  | Y =>
      intro t hK
      have ht : t = CExp.Y := by
        have hEq : CExp.app CExp.K CExp.Y = CExp.app CExp.K t := by
          simpa [CExp.bracket] using hK
        cases hEq
        rfl
      subst ht
      exact Comb.Steps.refl _
  | app f a ihf iha =>
      intro t hK
      cases hOcc : (occurs x f || occurs x a) with
      | false =>
          -- `[x](f a) = K (f a)` definitionally.
          have ht : t = CExp.app f a := by
            have hEq : CExp.app CExp.K (CExp.app f a) = CExp.app CExp.K t := by
              simpa [CExp.bracket, hOcc] using hK
            cases hEq
            rfl
          subst ht
          have hfa : occurs x f = false ∧ occurs x a = false := by
            simpa [occurs] using hOcc
          have hf : denote (update ρ x v) f = denote ρ f :=
            denote_update_eq_of_occurs_false (ρ := ρ) (x := x) (v := v) f hfa.1
          have ha : denote (update ρ x v) a = denote ρ a :=
            denote_update_eq_of_occurs_false (ρ := ρ) (x := x) (v := v) a hfa.2
          exact Comb.Steps.of_eq (by simp [denote, hf, ha])
      | true =>
          -- `hK` implies `opt u = K t` where `u := S ([x]f) ([x]a)`.
          have hOpt :
              opt (CExp.app (CExp.app CExp.S (bracket x f)) (bracket x a)) =
                CExp.app CExp.K t := by
            simpa [CExp.bracket, hOcc] using hK
          -- For `opt` to produce `K _`, we must have `[x]f = K _`.
          cases hbf : bracket x f with
          | app bfL bfR =>
              cases bfL with
              | K =>
                -- Now `opt` inspects `[x]a`.
                cases hba : bracket x a with
                | app baL baR =>
                    by_cases hbaK : baL = CExp.K
                    · subst hbaK
                      -- Opt1: `S (K e) (K f) ↦ K (e f)`.
                      have ht : t = CExp.app bfR baR := by
                        have hEq :
                            CExp.app CExp.K (CExp.app bfR baR) = CExp.app CExp.K t := by
                          simpa [opt, hbf, hba] using hOpt
                        cases hEq
                        rfl
                      subst ht
                      have hf : Comb.Steps (denote (update ρ x v) f) (denote ρ bfR) :=
                        ihf (t := bfR) (by simpa [hbf])
                      have ha : Comb.Steps (denote (update ρ x v) a) (denote ρ baR) :=
                        iha (t := baR) (by simpa [hba])
                      have hfa :
                          Comb.Steps
                            (Comb.app (denote (update ρ x v) f) (denote (update ρ x v) a))
                            (Comb.app (denote ρ bfR) (denote ρ baR)) :=
                        steps_transitive (steps_app_left (a := denote (update ρ x v) a) hf)
                          (steps_app_right (f := denote ρ bfR) ha)
                      simpa [denote] using hfa
                    ·
                      -- Opt2 can return `bfR`; for `opt u = K t`, `bfR` itself must be `K t`.
                      by_cases hI : CExp.app baL baR = I
                      · have hbfR : bfR = CExp.app CExp.K t := by
                          simpa [opt, hbf, hba, hbaK, hI] using hOpt
                        have hf : Comb.Steps (denote (update ρ x v) f) (denote ρ bfR) :=
                          ihf (t := bfR) (by simpa [hbf])
                        have hf' :
                            Comb.Steps (denote (update ρ x v) f)
                              (Comb.app Comb.K (denote ρ t)) := by
                          simpa [denote, hbfR] using hf
                        have hApp :
                            Comb.Steps
                              (Comb.app (denote (update ρ x v) f) (denote (update ρ x v) a))
                              (Comb.app (Comb.app Comb.K (denote ρ t)) (denote (update ρ x v) a)) :=
                          steps_app_left (a := denote (update ρ x v) a) hf'
                        exact steps_transitive hApp
                          (Comb.Steps.trans
                            (Comb.Step.K_rule (x := denote ρ t) (y := denote (update ρ x v) a))
                            (Comb.Steps.refl _))
                      ·
                        -- Otherwise `opt` is identity, and the head is not `K`.
                        have hBad :
                            CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (CExp.app baL baR) =
                              CExp.app CExp.K t := by
                          simpa [opt, hbf, hba, hbaK, hI] using hOpt
                        injection hBad with hContra _
                        cases hContra
                | var z =>
                    have hBad :
                        CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (CExp.var z) =
                          CExp.app CExp.K t := by
                      -- `CExp.var z ≠ I`, so `opt` is identity here.
                      simpa [opt, CExp.I, hbf, hba] using hOpt
                    injection hBad with hContra _
                    cases hContra
                | K =>
                    have hBad :
                        CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.K =
                          CExp.app CExp.K t := by
                      simpa [opt, CExp.I, hbf, hba] using hOpt
                    injection hBad with hContra _
                    cases hContra
                | S =>
                    have hBad :
                        CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.S =
                          CExp.app CExp.K t := by
                      simpa [opt, CExp.I, hbf, hba] using hOpt
                    injection hBad with hContra _
                    cases hContra
                | Y =>
                    have hBad :
                        CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.Y =
                          CExp.app CExp.K t := by
                      simpa [opt, CExp.I, hbf, hba] using hOpt
                    injection hBad with hContra _
                    cases hContra
              | var z =>
                  have hBad :
                      CExp.app (CExp.app CExp.S (CExp.app (CExp.var z) bfR)) (bracket x a) =
                        CExp.app CExp.K t := by
                    simpa [opt, hbf] using hOpt
                  injection hBad with hContra _
                  cases hContra
              | app bfL' bfR' =>
                  have hBad :
                      CExp.app (CExp.app CExp.S (CExp.app (CExp.app bfL' bfR') bfR)) (bracket x a) =
                        CExp.app CExp.K t := by
                    simpa [opt, hbf] using hOpt
                  injection hBad with hContra _
                  cases hContra
              | S =>
                  have hBad :
                      CExp.app (CExp.app CExp.S (CExp.app CExp.S bfR)) (bracket x a) =
                        CExp.app CExp.K t := by
                    simpa [opt, hbf] using hOpt
                  injection hBad with hContra _
                  cases hContra
              | Y =>
                  have hBad :
                      CExp.app (CExp.app CExp.S (CExp.app CExp.Y bfR)) (bracket x a) =
                        CExp.app CExp.K t := by
                    simpa [opt, hbf] using hOpt
                  injection hBad with hContra _
                  cases hContra
          | var z =>
              have hBad :
                  CExp.app (CExp.app CExp.S (CExp.var z)) (bracket x a) = CExp.app CExp.K t := by
                simpa [opt, hbf] using hOpt
              injection hBad with hContra _
              cases hContra
          | K =>
              have hBad :
                  CExp.app (CExp.app CExp.S CExp.K) (bracket x a) = CExp.app CExp.K t := by
                simpa [opt, hbf] using hOpt
              injection hBad with hContra _
              cases hContra
          | S =>
              have hBad :
                  CExp.app (CExp.app CExp.S CExp.S) (bracket x a) = CExp.app CExp.K t := by
                simpa [opt, hbf] using hOpt
              injection hBad with hContra _
              cases hContra
          | Y =>
              have hBad :
                  CExp.app (CExp.app CExp.S CExp.Y) (bracket x a) = CExp.app CExp.K t := by
                simpa [opt, hbf] using hOpt
              injection hBad with hContra _
              cases hContra

/-- A combined helper: if `[x]e = I`, then `e[v/x] →* v`, and if `[x]e = K`, then `e[v/x] →* (K v)`. -/
theorem denote_update_steps_of_bracket_eq_IK (ρ : Var → Comb) (x : Var) (v : Comb) :
    ∀ e : CExp Var,
      (bracket x e = I → Comb.Steps (denote (update ρ x v) e) v) ∧
      (bracket x e = CExp.K → Comb.Steps (denote (update ρ x v) e) (Comb.app Comb.K v)) := by
  intro e
  induction e with
  | var y =>
      refine ⟨?_, ?_⟩
      · intro hI
        by_cases hy : y = x
        · subst hy
          simpa [CExp.bracket, denote, update, CExp.I, Comb.I] using (Comb.Steps.refl v)
        ·
          have : False := by
            simpa [CExp.bracket, hy, CExp.I] using hI
          cases this
      · intro hK
        by_cases hy : y = x
        · subst hy
          have hBad : (CExp.I : CExp Var) = CExp.K := by
            simpa [CExp.bracket, CExp.I] using hK
          cases hBad
        ·
          have hBad : CExp.app CExp.K (CExp.var y) = CExp.K := by
            simpa [CExp.bracket, hy] using hK
          cases hBad
  | K =>
      refine ⟨?_, ?_⟩
      · intro hI
        have : False := by
          simpa [CExp.bracket, CExp.I] using hI
        cases this
      · intro hK
        have : False := by
          simpa [CExp.bracket] using hK
        cases this
  | S =>
      refine ⟨?_, ?_⟩
      · intro hI
        have : False := by
          simpa [CExp.bracket, CExp.I] using hI
        cases this
      · intro hK
        have : False := by
          simpa [CExp.bracket] using hK
        cases this
  | Y =>
      refine ⟨?_, ?_⟩
      · intro hI
        have : False := by
          simpa [CExp.bracket, CExp.I] using hI
        cases this
      · intro hK
        have : False := by
          simpa [CExp.bracket] using hK
        cases this
  | app f a ihf iha =>
      refine ⟨?_, ?_⟩
      · intro hI
        cases hOcc : (occurs x f || occurs x a) with
        | false =>
            have : False := by
              simpa [CExp.bracket, hOcc, CExp.I] using hI
            cases this
        | true =>
            have hOpt :
                opt (CExp.app (CExp.app CExp.S (bracket x f)) (bracket x a)) = I := by
              simpa [CExp.bracket, hOcc] using hI
            cases hbf : bracket x f with
            | app bfL bfR =>
                cases bfL with
                | K =>
                    by_cases hIarg : bracket x a = I
                    ·
                      have hbfR : bfR = I := by
                        simpa [opt, hbf, hIarg] using hOpt
                      have hfI : Comb.Steps (denote (update ρ x v) f) (denote ρ I) :=
                        denote_update_steps_of_bracket_eq_appK (ρ := ρ) (x := x) (v := v)
                          (e := f) (t := I) (by simpa [hbf, hbfR])
                      have haV : Comb.Steps (denote (update ρ x v) a) v :=
                        (iha.1 hIarg)
                      have h1 :
                          Comb.Steps (Comb.app (denote (update ρ x v) f) (denote (update ρ x v) a))
                            (Comb.app (denote ρ I) (denote (update ρ x v) a)) :=
                        steps_app_left (a := denote (update ρ x v) a) hfI
                      have h2 :
                          Comb.Steps (Comb.app (denote ρ I) (denote (update ρ x v) a))
                            (Comb.app (denote ρ I) v) :=
                        steps_app_right (f := denote ρ I) haV
                      have h3 : Comb.Steps (Comb.app (denote ρ I) v) v := by
                        simpa [denote, CExp.I, Comb.I] using (Comb.I_reduces v)
                      exact steps_transitive (steps_transitive h1 h2) h3
                    ·
                      have hBad :
                          opt (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (bracket x a)) = I := by
                        simpa [hbf] using hOpt
                      have : False := by
                        cases harg : bracket x a with
                        | app aL aR =>
                            cases aL with
                            | K =>
                                have hEq : CExp.app CExp.K (CExp.app bfR aR) = I := by
                                  have :
                                      opt
                                          (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                            (CExp.app CExp.K aR)) =
                                        I := by
                                    simpa [harg] using hBad
                                  simpa [opt] using this
                                cases hEq
                            | var z =>
                                have hNot : ¬CExp.app (CExp.var z) aR = I := by
                                  intro hEqI
                                  apply hIarg
                                  simpa [harg] using hEqI
                                have hEq :
                                    CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                        (CExp.app (CExp.var z) aR) =
                                      I := by
                                  have :
                                      opt
                                          (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                            (CExp.app (CExp.var z) aR)) =
                                        I := by
                                    simpa [harg] using hBad
                                  simpa [opt, hNot] using this
                                injection hEq with h1 _
                                injection h1 with _ h1b
                                cases h1b
                            | S =>
                                have hNot : ¬CExp.app CExp.S aR = I := by
                                  intro hEqI
                                  apply hIarg
                                  simpa [harg] using hEqI
                                have hEq :
                                    CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (CExp.app CExp.S aR) = I := by
                                  have :
                                      opt
                                          (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                            (CExp.app CExp.S aR)) =
                                        I := by
                                    simpa [harg] using hBad
                                  simpa [opt, hNot] using this
                                injection hEq with h1 _
                                injection h1 with _ h1b
                                cases h1b
                            | Y =>
                                have hNot : ¬CExp.app CExp.Y aR = I := by
                                  intro hEqI
                                  apply hIarg
                                  simpa [harg] using hEqI
                                have hEq :
                                    CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (CExp.app CExp.Y aR) = I := by
                                  have :
                                      opt
                                          (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                            (CExp.app CExp.Y aR)) =
                                        I := by
                                    simpa [harg] using hBad
                                  simpa [opt, hNot] using this
                                injection hEq with h1 _
                                injection h1 with _ h1b
                                cases h1b
                            | app aLL aLR =>
                                have hNot : ¬CExp.app (CExp.app aLL aLR) aR = I := by
                                  intro hEqI
                                  apply hIarg
                                  simpa [harg] using hEqI
                                have hEq :
                                    CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                        (CExp.app (CExp.app aLL aLR) aR) =
                                      I := by
                                  have :
                                      opt
                                          (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                            (CExp.app (CExp.app aLL aLR) aR)) =
                                        I := by
                                    simpa [harg] using hBad
                                  simpa [opt, hNot] using this
                                injection hEq with h1 _
                                injection h1 with _ h1b
                                cases h1b
                        | var z =>
                            have hNot : ¬CExp.var z = I := by
                              intro hEqI
                              apply hIarg
                              simpa [harg] using hEqI
                            have hEq :
                                CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (CExp.var z) = I := by
                              have :
                                  opt (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (CExp.var z)) = I := by
                                simpa [harg] using hBad
                              simpa [opt, hNot] using this
                            injection hEq with h1 _
                            injection h1 with _ h1b
                            cases h1b
                        | K =>
                            have hNot : ¬(CExp.K : CExp Var) = I := by
                              intro hEqI
                              apply hIarg
                              simpa [harg] using hEqI
                            have hEq :
                                CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.K = I := by
                              have :
                                  opt (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.K) = I := by
                                simpa [harg] using hBad
                              simpa [opt, hNot] using this
                            injection hEq with h1 _
                            injection h1 with _ h1b
                            cases h1b
                        | S =>
                            have hNot : ¬(CExp.S : CExp Var) = I := by
                              intro hEqI
                              apply hIarg
                              simpa [harg] using hEqI
                            have hEq :
                                CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.S = I := by
                              have :
                                  opt (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.S) = I := by
                                simpa [harg] using hBad
                              simpa [opt, hNot] using this
                            injection hEq with h1 _
                            injection h1 with _ h1b
                            cases h1b
                        | Y =>
                            have hNot : ¬(CExp.Y : CExp Var) = I := by
                              intro hEqI
                              apply hIarg
                              simpa [harg] using hEqI
                            have hEq :
                                CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.Y = I := by
                              have :
                                  opt (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.Y) = I := by
                                simpa [harg] using hBad
                              simpa [opt, hNot] using this
                            injection hEq with h1 _
                            injection h1 with _ h1b
                            cases h1b
                      cases this
                | var z =>
                    have hEq :
                        CExp.app (CExp.app CExp.S (CExp.app (CExp.var z) bfR)) (bracket x a) = I := by
                      simpa [opt, hbf] using hOpt
                    injection hEq with h1 _
                    injection h1 with _ h1b
                    cases h1b
                | S =>
                    have hEq :
                        CExp.app (CExp.app CExp.S (CExp.app CExp.S bfR)) (bracket x a) = I := by
                      simpa [opt, hbf] using hOpt
                    injection hEq with h1 _
                    injection h1 with _ h1b
                    cases h1b
                | Y =>
                    have hEq :
                        CExp.app (CExp.app CExp.S (CExp.app CExp.Y bfR)) (bracket x a) = I := by
                      simpa [opt, hbf] using hOpt
                    injection hEq with h1 _
                    injection h1 with _ h1b
                    cases h1b
                | app bfL' bfR' =>
                    have hEq :
                        CExp.app (CExp.app CExp.S (CExp.app (CExp.app bfL' bfR') bfR)) (bracket x a) = I := by
                      simpa [opt, hbf] using hOpt
                    injection hEq with h1 _
                    injection h1 with _ h1b
                    cases h1b
            | K =>
                have hEq : CExp.app (CExp.app CExp.S CExp.K) (bracket x a) = I := by
                  simpa [opt, hbf] using hOpt
                have hba : bracket x a = CExp.K := by
                  have hEq' :
                      CExp.app (CExp.app CExp.S CExp.K) (bracket x a) =
                        CExp.app (CExp.app CExp.S CExp.K) CExp.K := by
                    simpa [CExp.I] using hEq
                  injection hEq' with _ hba
                have hfKv : Comb.Steps (denote (update ρ x v) f) (Comb.app Comb.K v) :=
                  (ihf.2 hbf)
                have haKv : Comb.Steps (denote (update ρ x v) a) (Comb.app Comb.K v) :=
                  (iha.2 hba)
                have h1 :
                    Comb.Steps (Comb.app (denote (update ρ x v) f) (denote (update ρ x v) a))
                      (Comb.app (Comb.app Comb.K v) (denote (update ρ x v) a)) :=
                  steps_app_left (a := denote (update ρ x v) a) hfKv
                have h2 :
                    Comb.Steps (Comb.app (Comb.app Comb.K v) (denote (update ρ x v) a))
                      (Comb.app (Comb.app Comb.K v) (Comb.app Comb.K v)) :=
                  steps_app_right (f := Comb.app Comb.K v) haKv
                have h3 : Comb.Steps (Comb.app (Comb.app Comb.K v) (Comb.app Comb.K v)) v :=
                  Comb.Steps.trans (Comb.Step.K_rule (x := v) (y := Comb.app Comb.K v)) (Comb.Steps.refl _)
                exact steps_transitive (steps_transitive h1 h2) h3
            | var z =>
                have hEq : CExp.app (CExp.app CExp.S (CExp.var z)) (bracket x a) = I := by
                  simpa [opt, hbf] using hOpt
                injection hEq with h1 _
                injection h1 with _ hBad
                cases hBad
            | S =>
                have hEq : CExp.app (CExp.app CExp.S CExp.S) (bracket x a) = I := by
                  simpa [opt, hbf] using hOpt
                injection hEq with h1 _
                injection h1 with _ hBad
                cases hBad
            | Y =>
                have hEq : CExp.app (CExp.app CExp.S CExp.Y) (bracket x a) = I := by
                  simpa [opt, hbf] using hOpt
                injection hEq with h1 _
                injection h1 with _ hBad
                cases hBad
      · intro hK
        cases hOcc : (occurs x f || occurs x a) with
        | false =>
            have : False := by
              simpa [CExp.bracket, hOcc] using hK
            cases this
        | true =>
            have hOpt :
                opt (CExp.app (CExp.app CExp.S (bracket x f)) (bracket x a)) = CExp.K := by
              simpa [CExp.bracket, hOcc] using hK
            cases hbf : bracket x f with
            | app bfL bfR =>
                cases bfL with
                | K =>
                    by_cases hIarg : bracket x a = I
                    ·
                      have hbfR : bfR = CExp.K := by
                        simpa [opt, hbf, hIarg] using hOpt
                      have hfK : Comb.Steps (denote (update ρ x v) f) (denote ρ CExp.K) :=
                        denote_update_steps_of_bracket_eq_appK (ρ := ρ) (x := x) (v := v)
                          (e := f) (t := CExp.K) (by simpa [hbf, hbfR])
                      have haV : Comb.Steps (denote (update ρ x v) a) v :=
                        (iha.1 hIarg)
                      have h1 :
                          Comb.Steps (Comb.app (denote (update ρ x v) f) (denote (update ρ x v) a))
                            (Comb.app (denote ρ CExp.K) (denote (update ρ x v) a)) :=
                        steps_app_left (a := denote (update ρ x v) a) hfK
                      have h2 :
                          Comb.Steps (Comb.app (denote ρ CExp.K) (denote (update ρ x v) a))
                            (Comb.app (denote ρ CExp.K) v) :=
                        steps_app_right (f := denote ρ CExp.K) haV
                      simpa [denote] using steps_transitive h1 h2
                    ·
                      have hBad :
                          opt (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (bracket x a)) = CExp.K := by
                        simpa [hbf] using hOpt
                      have : False := by
                        cases harg : bracket x a with
                        | app aL aR =>
                            cases aL with
                            | K =>
                                have hEq : CExp.app CExp.K (CExp.app bfR aR) = CExp.K := by
                                  have :
                                      opt
                                          (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                            (CExp.app CExp.K aR)) =
                                        CExp.K := by
                                    simpa [harg] using hBad
                                  simpa [opt] using this
                                cases hEq
                            | var z =>
                                have hNot : ¬CExp.app (CExp.var z) aR = I := by
                                  intro hEqI
                                  apply hIarg
                                  simpa [harg] using hEqI
                                have hEq :
                                    CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                        (CExp.app (CExp.var z) aR) =
                                      CExp.K := by
                                  have :
                                      opt
                                          (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                            (CExp.app (CExp.var z) aR)) =
                                        CExp.K := by
                                    simpa [harg] using hBad
                                  simpa [opt, hNot] using this
                                cases hEq
                            | S =>
                                have hNot : ¬CExp.app CExp.S aR = I := by
                                  intro hEqI
                                  apply hIarg
                                  simpa [harg] using hEqI
                                have hEq :
                                    CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (CExp.app CExp.S aR) = CExp.K := by
                                  have :
                                      opt
                                          (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                            (CExp.app CExp.S aR)) =
                                        CExp.K := by
                                    simpa [harg] using hBad
                                  simpa [opt, hNot] using this
                                cases hEq
                            | Y =>
                                have hNot : ¬CExp.app CExp.Y aR = I := by
                                  intro hEqI
                                  apply hIarg
                                  simpa [harg] using hEqI
                                have hEq :
                                    CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (CExp.app CExp.Y aR) = CExp.K := by
                                  have :
                                      opt
                                          (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                            (CExp.app CExp.Y aR)) =
                                        CExp.K := by
                                    simpa [harg] using hBad
                                  simpa [opt, hNot] using this
                                cases hEq
                            | app aLL aLR =>
                                have hNot : ¬CExp.app (CExp.app aLL aLR) aR = I := by
                                  intro hEqI
                                  apply hIarg
                                  simpa [harg] using hEqI
                                have hEq :
                                    CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                        (CExp.app (CExp.app aLL aLR) aR) =
                                      CExp.K := by
                                  have :
                                      opt
                                          (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR))
                                            (CExp.app (CExp.app aLL aLR) aR)) =
                                        CExp.K := by
                                    simpa [harg] using hBad
                                  simpa [opt, hNot] using this
                                cases hEq
                        | var z =>
                            have hNot : ¬CExp.var z = I := by
                              intro hEqI
                              apply hIarg
                              simpa [harg] using hEqI
                            have hEq :
                                CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (CExp.var z) = CExp.K := by
                              have :
                                  opt (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) (CExp.var z)) = CExp.K := by
                                simpa [harg] using hBad
                              simpa [opt, hNot] using this
                            cases hEq
                        | K =>
                            have hNot : ¬(CExp.K : CExp Var) = I := by
                              intro hEqI
                              apply hIarg
                              simpa [harg] using hEqI
                            have hEq :
                                CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.K = CExp.K := by
                              have :
                                  opt (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.K) = CExp.K := by
                                simpa [harg] using hBad
                              simpa [opt, hNot] using this
                            cases hEq
                        | S =>
                            have hNot : ¬(CExp.S : CExp Var) = I := by
                              intro hEqI
                              apply hIarg
                              simpa [harg] using hEqI
                            have hEq :
                                CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.S = CExp.K := by
                              have :
                                  opt (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.S) = CExp.K := by
                                simpa [harg] using hBad
                              simpa [opt, hNot] using this
                            cases hEq
                        | Y =>
                            have hNot : ¬(CExp.Y : CExp Var) = I := by
                              intro hEqI
                              apply hIarg
                              simpa [harg] using hEqI
                            have hEq :
                                CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.Y = CExp.K := by
                              have :
                                  opt (CExp.app (CExp.app CExp.S (CExp.app CExp.K bfR)) CExp.Y) = CExp.K := by
                                simpa [harg] using hBad
                              simpa [opt, hNot] using this
                            cases hEq
                      cases this
                | var z =>
                    have hEq :
                        CExp.app (CExp.app CExp.S (CExp.app (CExp.var z) bfR)) (bracket x a) = CExp.K := by
                      simpa [opt, hbf] using hOpt
                    simpa using hEq
                | S =>
                    have hEq :
                        CExp.app (CExp.app CExp.S (CExp.app CExp.S bfR)) (bracket x a) = CExp.K := by
                      simpa [opt, hbf] using hOpt
                    simpa using hEq
                | Y =>
                    have hEq :
                        CExp.app (CExp.app CExp.S (CExp.app CExp.Y bfR)) (bracket x a) = CExp.K := by
                      simpa [opt, hbf] using hOpt
                    simpa using hEq
                | app bfL' bfR' =>
                    have hEq :
                        CExp.app (CExp.app CExp.S (CExp.app (CExp.app bfL' bfR') bfR)) (bracket x a) = CExp.K := by
                      simpa [opt, hbf] using hOpt
                    simpa using hEq
            | var z =>
                have hEq : CExp.app (CExp.app CExp.S (CExp.var z)) (bracket x a) = CExp.K := by
                  simpa [opt, hbf] using hOpt
                simpa using hEq
            | K =>
                have hEq : CExp.app (CExp.app CExp.S CExp.K) (bracket x a) = CExp.K := by
                  simpa [opt, hbf] using hOpt
                simpa using hEq
            | S =>
                have hEq : CExp.app (CExp.app CExp.S CExp.S) (bracket x a) = CExp.K := by
                  simpa [opt, hbf] using hOpt
                simpa using hEq
            | Y =>
                have hEq : CExp.app (CExp.app CExp.S CExp.Y) (bracket x a) = CExp.K := by
                  simpa [opt, hbf] using hOpt
                simpa using hEq

/-- If `[x]e = I`, then `e[v/x] →* v`. -/
theorem denote_update_steps_of_bracket_eq_I (ρ : Var → Comb) (x : Var) (v : Comb) :
    ∀ e : CExp Var, bracket x e = I → Comb.Steps (denote (update ρ x v) e) v := by
  intro e hI
  exact (denote_update_steps_of_bracket_eq_IK (ρ := ρ) (x := x) (v := v) e).1 hI

/-- If `[x]e = K`, then `e[v/x] →* (K v)`. -/
theorem denote_update_steps_of_bracket_eq_K (ρ : Var → Comb) (x : Var) (v : Comb) :
    ∀ e : CExp Var, bracket x e = CExp.K → Comb.Steps (denote (update ρ x v) e) (Comb.app Comb.K v) := by
  intro e hK
  exact (denote_update_steps_of_bracket_eq_IK (ρ := ρ) (x := x) (v := v) e).2 hK

/-! ## Main theorem -/

/-- β-simulation as joinability: `([x]e) v` and `e[v/x]` reduce to a common reduct. -/
theorem bracket_beta_join (ρ : Var → Comb) (x : Var) :
    ∀ e : CExp Var, ∀ v : Comb,
      ∃ r : Comb, Comb.Steps (Comb.app (denote ρ (bracket x e)) v) r ∧
        Comb.Steps (denote (update ρ x v) e) r := by
  intro e
  induction e with
  | var y =>
      intro v
      by_cases hy : y = x
      · subst hy
        refine ⟨v, ?_, ?_⟩
        · simpa [CExp.bracket, denote, CExp.I, Comb.I] using (Comb.I_reduces v)
        · simpa [denote, update] using (Comb.Steps.refl v)
      ·
        refine ⟨ρ y, ?_, ?_⟩
        · refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
          simpa [CExp.bracket, denote, hy] using (Comb.Step.K_rule (x := ρ y) (y := v))
        · simpa [denote, update, hy] using (Comb.Steps.refl (ρ y))
  | K =>
      intro v
      refine ⟨Comb.K, ?_, ?_⟩
      · refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
        simpa [CExp.bracket, denote] using (Comb.Step.K_rule (x := Comb.K) (y := v))
      · exact Comb.Steps.refl _
  | S =>
      intro v
      refine ⟨Comb.S, ?_, ?_⟩
      · refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
        simpa [CExp.bracket, denote] using (Comb.Step.K_rule (x := Comb.S) (y := v))
      · exact Comb.Steps.refl _
  | Y =>
      intro v
      refine ⟨Comb.Y, ?_, ?_⟩
      · refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
        simpa [CExp.bracket, denote] using (Comb.Step.K_rule (x := Comb.Y) (y := v))
      · exact Comb.Steps.refl _
    | app f a ihf iha =>
        intro v
        cases hOcc : (occurs x f || occurs x a) with
        | false =>
            have hoccApp : occurs x (CExp.app f a) = false := by
              simpa [occurs] using hOcc
            exact bracket_beta_join_of_occurs_false (ρ := ρ) (x := x) (e := CExp.app f a) (v := v) hoccApp
        | true =>
            let bf := bracket x f
            let ba := bracket x a
            let u : CExp Var := CExp.app (CExp.app CExp.S bf) ba
            have hbr : bracket x (CExp.app f a) = opt u := by
              simp [CExp.bracket, hOcc, bf, ba, u]

            have default_case (hId : opt u = u) :
                ∃ r : Comb, Comb.Steps (Comb.app (denote ρ (bracket x (CExp.app f a))) v) r ∧
                  Comb.Steps (denote (update ρ x v) (CExp.app f a)) r := by
              have hb : bracket x (CExp.app f a) = u := by
                simpa [hId] using hbr
              rcases ihf (v := v) with ⟨rf, hLf, hRf⟩
              rcases iha (v := v) with ⟨ra, hLa, hRa⟩
              have hLf' : Comb.Steps (Comb.app (denote ρ bf) v) rf := by
                simpa [bf] using hLf
              have hLa' : Comb.Steps (Comb.app (denote ρ ba) v) ra := by
                simpa [ba] using hLa
              refine ⟨Comb.app rf ra, ?_, ?_⟩
              ·
                have hS :
                    Comb.Step (Comb.app (denote ρ u) v)
                      (Comb.app (Comb.app (denote ρ bf) v) (Comb.app (denote ρ ba) v)) := by
                  simpa [denote, u, bf, ba] using
                    (Comb.Step.S_rule (x := denote ρ bf) (y := denote ρ ba) (z := v))
                have h1 :
                    Comb.Steps (Comb.app (denote ρ u) v)
                      (Comb.app (Comb.app (denote ρ bf) v) (Comb.app (denote ρ ba) v)) :=
                  Comb.Steps.trans hS (Comb.Steps.refl _)
                have h1' :
                    Comb.Steps (Comb.app (denote ρ (bracket x (CExp.app f a))) v)
                      (Comb.app (Comb.app (denote ρ bf) v) (Comb.app (denote ρ ba) v)) := by
                  simpa [hb] using h1
                have h2 :
                    Comb.Steps
                      (Comb.app (Comb.app (denote ρ bf) v) (Comb.app (denote ρ ba) v))
                      (Comb.app rf (Comb.app (denote ρ ba) v)) :=
                  steps_app_left (a := Comb.app (denote ρ ba) v) hLf'
                have h3 :
                    Comb.Steps (Comb.app rf (Comb.app (denote ρ ba) v)) (Comb.app rf ra) :=
                  steps_app_right (f := rf) hLa'
                exact steps_transitive (steps_transitive h1' h2) h3
              ·
                have h2 :
                    Comb.Steps (Comb.app (denote (update ρ x v) f) (denote (update ρ x v) a))
                      (Comb.app rf (denote (update ρ x v) a)) :=
                  steps_app_left (a := denote (update ρ x v) a) hRf
                have h3 :
                    Comb.Steps (Comb.app rf (denote (update ρ x v) a)) (Comb.app rf ra) :=
                  steps_app_right (f := rf) hRa
                simpa [denote] using steps_transitive h2 h3

            -- Now analyze the optimization patterns.
            cases hbf : bf with
            | app bfL bfR =>
                cases bfL with
                | K =>
                    cases hba : ba with
                  | app baL baR =>
                      cases baL with
                      | K =>
                          -- Opt1: `S (K e) (K f) ↦ K (e f)`.
                          let t : CExp Var := CExp.app bfR baR
                          refine ⟨denote ρ t, ?_, ?_⟩
                          ·
                            have hOptVal : opt u = CExp.app CExp.K t := by
                              simp [opt, u, hbf, hba, t]
                            have hb : bracket x (CExp.app f a) = CExp.app CExp.K t := by
                              simpa [hOptVal] using hbr
                            refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
                            simpa [hb, denote] using (Comb.Step.K_rule (x := denote ρ t) (y := v))
                          ·
                            have hbf' : bracket x f = CExp.app CExp.K bfR := by
                              simpa [bf] using hbf
                            have hba' : bracket x a = CExp.app CExp.K baR := by
                              simpa [ba] using hba
                            have hf :
                                Comb.Steps (denote (update ρ x v) f) (denote ρ bfR) :=
                              denote_update_steps_of_bracket_eq_appK (ρ := ρ) (x := x) (v := v)
                                (e := f) (t := bfR) hbf'
                            have ha :
                                Comb.Steps (denote (update ρ x v) a) (denote ρ baR) :=
                              denote_update_steps_of_bracket_eq_appK (ρ := ρ) (x := x) (v := v)
                                (e := a) (t := baR) hba'
                            have h1 :
                                Comb.Steps (Comb.app (denote (update ρ x v) f) (denote (update ρ x v) a))
                                  (Comb.app (denote ρ bfR) (denote (update ρ x v) a)) :=
                              steps_app_left (a := denote (update ρ x v) a) hf
                            have h2 :
                                Comb.Steps (Comb.app (denote ρ bfR) (denote (update ρ x v) a))
                                  (Comb.app (denote ρ bfR) (denote ρ baR)) :=
                              steps_app_right (f := denote ρ bfR) ha
                            simpa [denote, t] using steps_transitive h1 h2
                      | var z =>
                          exact default_case (by simp [opt, u, hbf, hba, CExp.I])
                      | S =>
                          exact default_case (by simp [opt, u, hbf, hba, CExp.I])
                      | Y =>
                          exact default_case (by simp [opt, u, hbf, hba, CExp.I])
                      | app baL' baR' =>
                          -- Possibly η-like if `ba = I`; otherwise identity.
                          by_cases hI : ba = I
                          ·
                            have hOptVal : opt u = bfR := by
                              simp [opt, u, hbf, hI, CExp.I]
                            have hb : bracket x (CExp.app f a) = bfR := by
                              simpa [hOptVal] using hbr
                            refine ⟨Comb.app (denote ρ bfR) v, ?_, ?_⟩
                            · simpa [hb, denote] using (Comb.Steps.refl _)
                            ·
                              have hbf' : bracket x f = CExp.app CExp.K bfR := by
                                simpa [bf] using hbf
                              have hf :
                                  Comb.Steps (denote (update ρ x v) f) (denote ρ bfR) :=
                                denote_update_steps_of_bracket_eq_appK (ρ := ρ) (x := x) (v := v)
                                  (e := f) (t := bfR) hbf'
                              have hbaI : ba = I := hI
                              have hbaI' : bracket x a = I := by
                                simpa [ba] using hbaI
                              have haV :
                                  Comb.Steps (denote (update ρ x v) a) v :=
                                denote_update_steps_of_bracket_eq_I (ρ := ρ) (x := x) (v := v)
                                  (e := a) hbaI'
                              have h1 :
                                  Comb.Steps (Comb.app (denote (update ρ x v) f) (denote (update ρ x v) a))
                                    (Comb.app (denote ρ bfR) (denote (update ρ x v) a)) :=
                                steps_app_left (a := denote (update ρ x v) a) hf
                              have h2 :
                                  Comb.Steps (Comb.app (denote ρ bfR) (denote (update ρ x v) a))
                                    (Comb.app (denote ρ bfR) v) :=
                                steps_app_right (f := denote ρ bfR) haV
                              simpa [denote] using steps_transitive h1 h2
                          ·
                            exact default_case (by
                              have hOptu : opt u = if ba = I then bfR else u := by
                                simp [opt, u, hbf, hba]
                              simpa [hOptu, hI])
                    | var z =>
                        exact default_case (by simp [opt, u, hbf, hba, CExp.I])
                    | K =>
                        exact default_case (by simp [opt, u, hbf, hba, CExp.I])
                    | S =>
                        exact default_case (by simp [opt, u, hbf, hba, CExp.I])
                    | Y =>
                        exact default_case (by simp [opt, u, hbf, hba, CExp.I])
                | var z =>
                    exact default_case (by simp [opt, u, hbf, CExp.I])
                | S =>
                    exact default_case (by simp [opt, u, hbf, CExp.I])
                | Y =>
                    exact default_case (by simp [opt, u, hbf, CExp.I])
                | app bfL' bfR' =>
                    exact default_case (by simp [opt, u, hbf, CExp.I])
            | var z =>
                exact default_case (by simp [opt, u, hbf, CExp.I])
            | K =>
                exact default_case (by simp [opt, u, hbf, CExp.I])
            | S =>
                exact default_case (by simp [opt, u, hbf, CExp.I])
            | Y =>
                exact default_case (by simp [opt, u, hbf, CExp.I])

end CExp
end Bracket

end Combinators
end LoF
end HeytingLean
