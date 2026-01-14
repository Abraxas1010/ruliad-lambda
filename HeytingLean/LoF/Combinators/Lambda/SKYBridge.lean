import HeytingLean.LoF.Combinators.Lambda.Syntax
import HeytingLean.LoF.Combinators.Lambda.Beta
import HeytingLean.LoF.Combinators.BracketAbstractionCorrectness

/-!
# Lambda.SKYBridge — β-simulation bridge via bracket abstraction

The core “λ ↔ SKY” bridge theorem we rely on is already proved in:

* `HeytingLean.LoF.Combinators.BracketAbstractionCorrectness`
  (`HeytingLean.LoF.Combinators.Bracket.CExp.bracket_beta_join`)

That theorem states: for any combinator-expression-with-variables `e` and variable `x`,
the compiled abstraction `[x]e` behaves like a λ-binder at the level of SKY reduction,
in the sense that `([x]e) v` is **joinable** with the denotation of `e` under the
environment update `x ↦ v`.

This file provides small wrappers that make this theorem directly usable from the
de Bruijn `Lambda.Term` layer.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Lambda

open HeytingLean.LoF

namespace Term

open Bracket

/-- Compile a de Bruijn λ-term to a combinator expression-with-variables (`CExp Nat`)
via the existing named-layer `Bracket.Lam` and its compiler. -/
def compileCExp (t : Term) : Bracket.CExp Nat :=
  Bracket.Lam.compile (Var := Nat) (toNamed t)

/-- Denotation of the compiled expression under an environment `ρ : Nat → Comb`. -/
def denoteCExp (ρ : Nat → Comb) (t : Term) : Comb :=
  Bracket.CExp.denote ρ (compileCExp t)

end Term

namespace Bridge

open Bracket
open Bracket.CExp

/-- Direct re-export of the β-simulation/joinability theorem, specialized to `Var = Nat`. -/
theorem bracket_beta_join_nat (ρ : Nat → Comb) (x : Nat) (e : CExp Nat) (v : Comb) :
    ∃ r : Comb,
      Comb.Steps (Comb.app (denote ρ (bracket x e)) v) r ∧
        Comb.Steps (denote (update ρ x v) e) r :=
  Bracket.CExp.bracket_beta_join (ρ := ρ) (x := x) e v

end Bridge

/-! ## SKY → λ simulation (standard encodings) -/

namespace StepsLemmas

theorem trans {t u v : Term} : Steps t u → Steps u v → Steps t v := by
  intro htu huv
  induction htu with
  | refl _ => simpa using huv
  | trans hstep hsteps ih => exact Steps.trans hstep (ih huv)

theorem ofStep {t u : Term} (h : Step t u) : Steps t u :=
  Steps.trans h (Steps.refl _)

theorem app_left {f f' a : Term} : Steps f f' → Steps (.app f a) (.app f' a) := by
  intro h
  induction h with
  | refl f => exact Steps.refl (Term.app f a)
  | trans hstep hsteps ih => exact Steps.trans (Step.app_left hstep) ih

theorem app_right {f a a' : Term} : Steps a a' → Steps (.app f a) (.app f a') := by
  intro h
  induction h with
  | refl a => exact Steps.refl (Term.app f a)
  | trans hstep hsteps ih => exact Steps.trans (Step.app_right hstep) ih

theorem lam_body {body body' : Term} : Steps body body' → Steps (.lam body) (.lam body') := by
  intro h
  induction h with
  | refl t => exact Steps.refl (Term.lam t)
  | trans hstep hsteps ih => exact Steps.trans (Step.lam_body hstep) ih

def Joinable (t u : Term) : Prop :=
  ∃ r : Term, Steps t r ∧ Steps u r

theorem Joinable.refl (t : Term) : Joinable t t :=
  ⟨t, Steps.refl _, Steps.refl _⟩

theorem Joinable.app_left {f f' a : Term} : Joinable f f' → Joinable (.app f a) (.app f' a) := by
  intro h
  rcases h with ⟨r, hf, hf'⟩
  exact ⟨.app r a, app_left (a := a) hf, app_left (a := a) hf'⟩

theorem Joinable.app_right {f a a' : Term} : Joinable a a' → Joinable (.app f a) (.app f a') := by
  intro h
  rcases h with ⟨r, ha, ha'⟩
  exact ⟨.app f r, app_right (f := f) ha, app_right (f := f) ha'⟩

end StepsLemmas

namespace Bridge

open StepsLemmas

private theorem substTop_lam_var_succ_of_closed (arg : Term) (harg : Term.Closed arg) :
    Term.substTop arg (.lam (.var 1)) = .lam arg := by
  have hShift : Term.shift arg 0 1 = arg := Term.shift_eq_of_closedAt (cutoff := 0) (inc := 1) harg
  have hShift' : Term.shift (Term.shift arg 0 1) 0 1 = arg := by simpa [hShift] using hShift
  have hDown : Term.shiftDown arg 1 1 = arg :=
    Term.shiftDown_eq_of_closedAt (t := arg) (cutoff := 1) (dec := 1)
      (Term.closedAt_mono (t := arg) (n := 0) (m := 1) harg (Nat.zero_le 1))
  simp [Term.substTop, Term.subst, Term.shiftDown, Term.shift, hShift, hShift', hDown]

theorem ofComb_K_rule (x y : Comb) :
    Steps (Term.ofComb (Comb.app (Comb.app .K x) y)) (Term.ofComb x) := by
  set xT : Term := Term.ofComb x
  set yT : Term := Term.ofComb y
  have hxT : Term.Closed xT := by simpa [xT] using Term.closed_ofComb x

  -- Step inside the left application: `(KEnc xT)` reduces to `λy. xT`.
  have h1 :
      Steps (Term.app (Term.app Term.KEnc xT) yT)
        (Term.app (Term.substTop xT (.lam (.var 1))) yT) := by
    exact ofStep (Step.app_left (Step.beta (body := .lam (.var 1)) (arg := xT)))
  have h1' :
      Steps (Term.app (Term.substTop xT (.lam (.var 1))) yT) (Term.app (.lam xT) yT) :=
    Steps.of_eq (by simp [substTop_lam_var_succ_of_closed (arg := xT) hxT])

  -- Apply the remaining argument and simplify (substitution into a closed term is a no-op).
  have h2 :
      Steps (Term.app (.lam xT) yT) (Term.substTop yT xT) :=
    ofStep (Step.beta (body := xT) (arg := yT))
  have h3 : Steps (Term.substTop yT xT) xT :=
    Steps.of_eq (by simpa [xT] using Term.substTop_eq_of_closed (t := xT) (arg := yT) hxT)

  exact trans (trans (trans h1 h1') h2) h3

theorem ofComb_S_rule (x y z : Comb) :
    Steps (Term.ofComb (Comb.app (Comb.app (Comb.app .S x) y) z))
      (Term.ofComb (Comb.app (Comb.app x z) (Comb.app y z))) := by
  set xT : Term := Term.ofComb x
  set yT : Term := Term.ofComb y
  set zT : Term := Term.ofComb z
  have hxT : Term.Closed xT := by simpa [xT] using Term.closed_ofComb x
  have hyT : Term.Closed yT := by simpa [yT] using Term.closed_ofComb y

  -- Reduce `(SEnc xT) yT zT` by three β steps.
  have h1 :
      Steps (Term.app (Term.app (Term.app Term.SEnc xT) yT) zT)
        (Term.app (Term.app (Term.substTop xT (.lam (.lam
            (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))) yT) zT) := by
    -- First β step on `SEnc xT`.
    refine app_left (a := zT) (app_left (a := yT) ?_)
    exact ofStep (Step.beta (body := .lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0))))) (arg := xT))

  have h1_simp :
      Steps (Term.app (Term.app (Term.substTop xT (.lam (.lam
            (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))) yT) zT)
        (Term.app (Term.app (.lam (.lam
            (.app (.app xT (.var 0)) (.app (.var 1) (.var 0))))) yT) zT) := by
    have hx2 : Term.closedAt 2 xT :=
      Term.closedAt_mono (t := xT) (n := 0) (m := 2) hxT (Nat.zero_le 2)
    have hdown2 : Term.shiftDown xT 2 1 = xT :=
      Term.shiftDown_eq_of_closedAt (t := xT) (cutoff := 2) (dec := 1) hx2
    have hshift : Term.shift xT 0 1 = xT := Term.shift_eq_of_closedAt (t := xT) (cutoff := 0) (inc := 1) hxT
    have hshift' : Term.shift (Term.shift xT 0 1) 0 1 = xT := by simpa [hshift] using hshift
    refine Steps.of_eq ?_
    simp [Term.substTop, Term.subst, Term.shiftDown, Term.shift, hshift, hshift', hdown2]

  have h2 :
      Steps (Term.app (Term.app (.lam (.lam
            (.app (.app xT (.var 0)) (.app (.var 1) (.var 0))))) yT) zT)
        (Term.app (Term.substTop yT (.lam
            (.app (.app xT (.var 0)) (.app (.var 1) (.var 0))))) zT) := by
    -- Second β step on the resulting `λy. …`.
    refine app_left (a := zT) ?_
    exact ofStep (Step.beta (body := .lam (.app (.app xT (.var 0)) (.app (.var 1) (.var 0)))) (arg := yT))

  have h2_simp :
      Steps (Term.app (Term.substTop yT (.lam
            (.app (.app xT (.var 0)) (.app (.var 1) (.var 0))))) zT)
        (Term.app (.lam (.app (.app xT (.var 0)) (.app yT (.var 0)))) zT) := by
    have hy1 : Term.closedAt 1 yT :=
      Term.closedAt_mono (t := yT) (n := 0) (m := 1) hyT (Nat.zero_le 1)
    have hdown1 : Term.shiftDown yT 1 1 = yT :=
      Term.shiftDown_eq_of_closedAt (t := yT) (cutoff := 1) (dec := 1) hy1
    have hshift : Term.shift yT 0 1 = yT := Term.shift_eq_of_closedAt (t := yT) (cutoff := 0) (inc := 1) hyT
    have hshift' : Term.shift (Term.shift yT 0 1) 0 1 = yT := by simpa [hshift] using hshift
    refine Steps.of_eq ?_
    simp [Term.substTop, Term.subst, Term.shiftDown, Term.shift, hshift, hshift', hdown1]

  have h3 :
      Steps (Term.app (.lam (.app (.app xT (.var 0)) (.app yT (.var 0)))) zT)
        (.app (.app xT zT) (.app yT zT)) :=
    ofStep (Step.beta (body := .app (.app xT (.var 0)) (.app yT (.var 0))) (arg := zT))

  exact trans (trans (trans (trans h1 h1_simp) h2) h2_simp) h3

theorem ofComb_Y_rule_joinable (f : Comb) :
    Joinable (Term.ofComb (Comb.app .Y f)) (Term.ofComb (Comb.app f (Comb.app .Y f))) := by
  set fT : Term := Term.ofComb f
  have hfT : Term.Closed fT := by simpa [fT] using Term.closed_ofComb f

  -- First β step: `YEnc fT` unfolds into two identical lambdas applied.
  have h1 :
      Steps (Term.ofComb (Comb.app .Y f))
        (Term.substTop fT
          (.app (.lam (.app (.var 1) (.app (.var 0) (.var 0))))
                (.lam (.app (.var 1) (.app (.var 0) (.var 0)))))) :=
    ofStep (Step.beta
      (body := (.app (.lam (.app (.var 1) (.app (.var 0) (.var 0))))
                    (.lam (.app (.var 1) (.app (.var 0) (.var 0)))))) (arg := fT))

  have h1_simp :
      Steps (Term.substTop fT
          (.app (.lam (.app (.var 1) (.app (.var 0) (.var 0))))
                (.lam (.app (.var 1) (.app (.var 0) (.var 0))))))
        (.app (.lam (.app fT (.app (.var 0) (.var 0))))
              (.lam (.app fT (.app (.var 0) (.var 0))))) := by
    have hf1 : Term.closedAt 1 fT := Term.closedAt_mono (t := fT) (n := 0) (m := 1) hfT (Nat.zero_le 1)
    have hdown1 : Term.shiftDown fT 1 1 = fT :=
      Term.shiftDown_eq_of_closedAt (t := fT) (cutoff := 1) (dec := 1) hf1
    have hshift : Term.shift fT 0 1 = fT := Term.shift_eq_of_closedAt (t := fT) (cutoff := 0) (inc := 1) hfT
    have hshift' : Term.shift (Term.shift fT 0 1) 0 1 = fT := by simpa [hshift] using hshift
    refine Steps.of_eq ?_
    simp [Term.substTop, Term.subst, Term.shiftDown, Term.shift, hshift, hshift', hdown1]

  -- Second β step: reduce the self-application redex and use it as a common reduct.
  let argLam : Term := .lam (.app fT (.app (.var 0) (.var 0)))
  let selfApp : Term := .app argLam argLam

  have hArg : Steps (Term.ofComb (Comb.app .Y f)) selfApp := by
    simpa [Term.ofComb, argLam, selfApp] using trans h1 h1_simp

  have h2 :
      Steps selfApp (Term.substTop argLam (.app fT (.app (.var 0) (.var 0)))) := by
    simpa [selfApp, argLam] using
      ofStep (Step.beta (body := .app fT (.app (.var 0) (.var 0))) (arg := argLam))

  have h2_simp :
      Steps (Term.substTop argLam (.app fT (.app (.var 0) (.var 0)))) (.app fT selfApp) := by
    have hf1 : Term.closedAt 1 fT := Term.closedAt_mono (t := fT) (n := 0) (m := 1) hfT (Nat.zero_le 1)
    have hsub0 : Term.subst (Term.shift argLam 0 1) 0 fT = fT :=
      Term.subst_eq_of_closedAt (t := fT) (s := Term.shift argLam 0 1) (j := 0) hfT
    have hdown0 : Term.shiftDown fT 0 1 = fT :=
      Term.shiftDown_eq_of_closedAt (t := fT) (cutoff := 0) (dec := 1) hfT
    have hdown1 : Term.shiftDown fT 1 1 = fT :=
      Term.shiftDown_eq_of_closedAt (t := fT) (cutoff := 1) (dec := 1) hf1
    have hshift : Term.shift fT 0 1 = fT :=
      Term.shift_eq_of_closedAt (t := fT) (cutoff := 0) (inc := 1) hfT
    have hshift' : Term.shift (Term.shift fT 0 1) 0 1 = fT := by simpa [hshift] using hshift
    refine Steps.of_eq ?_
    simp [Term.substTop, Term.subst, Term.shiftDown, Term.shift, argLam, selfApp,
      hshift, hshift', hsub0, hdown0, hdown1]

  have hLeft : Steps (Term.ofComb (Comb.app .Y f)) (.app fT selfApp) :=
    trans hArg (trans h2 h2_simp)
  have hRight : Steps (Term.ofComb (Comb.app f (Comb.app .Y f))) (.app fT selfApp) := by
    -- `ofComb (f (Y f)) = fT (YEnc fT)`.
    simpa [Term.ofComb, fT] using app_right (f := fT) hArg

  exact ⟨.app fT selfApp, hLeft, hRight⟩

theorem ofComb_simulates_step_joinable {c d : Comb} :
    Comb.Step c d → Joinable (Term.ofComb c) (Term.ofComb d) := by
  intro h
  induction h with
  | K_rule x y =>
      exact ⟨Term.ofComb x, ofComb_K_rule x y, Steps.refl _⟩
  | S_rule x y z =>
      exact ⟨Term.ofComb (Comb.app (Comb.app x z) (Comb.app y z)), ofComb_S_rule x y z, Steps.refl _⟩
  | Y_rule f =>
      simpa using ofComb_Y_rule_joinable f
  | app_left hstep ih =>
      rename_i f f' a
      exact Joinable.app_left (a := Term.ofComb a) ih
  | app_right hstep ih =>
      rename_i f a a'
      exact Joinable.app_right (f := Term.ofComb f) ih

end Bridge

end Lambda
end Combinators
end LoF
end HeytingLean
