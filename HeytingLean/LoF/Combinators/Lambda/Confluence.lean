import Mathlib.Logic.Relation
import HeytingLean.LoF.Combinators.Lambda.Beta
import HeytingLean.LoF.Combinators.Lambda.ShiftSubst

/-!
# Lambda.Confluence — Church–Rosser (confluence) for β-reduction

This file proves that the multi-step β-reduction relation `Lambda.Steps` is confluent
(Church–Rosser).

Strategy (standard):
- define **parallel β-reduction** `Par`;
- prove `Par` has the **diamond** property (via Takahashi-style complete development);
- lift diamond to confluence of `Relation.ReflTransGen Par`;
- relate `Par` to the existing small-step relation `Step` and its closure `Steps`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Lambda

open Term

/-! ## Parallel β-reduction -/

inductive Par : Term → Term → Prop where
  | var (i : Nat) : Par (.var i) (.var i)
  | lam {t t' : Term} : Par t t' → Par (.lam t) (.lam t')
  | app {f f' a a' : Term} : Par f f' → Par a a' → Par (.app f a) (.app f' a')
  | beta {body body' arg arg' : Term} :
      Par body body' → Par arg arg' → Par (.app (.lam body) arg) (Term.substTop arg' body')

namespace Par

theorem refl : ∀ t : Term, Par t t := by
  intro t
  induction t with
  | var i =>
      exact Par.var i
  | app f a ihf iha =>
      exact Par.app ihf iha
  | lam body ih =>
      exact Par.lam ih

theorem shift {t u : Term} (h : Par t u) :
    ∀ (cutoff inc : Nat), Par (Term.shift t cutoff inc) (Term.shift u cutoff inc) := by
  intro cutoff inc
  induction h generalizing cutoff inc with
  | var i =>
      by_cases hi : i < cutoff
      ·
        have hShift : Term.shift (.var i) cutoff inc = .var i :=
          Term.shift_var_lt (cutoff := cutoff) (inc := inc) (i := i) hi
        simpa [hShift] using Par.var i
      ·
        have hi' : cutoff ≤ i := Nat.le_of_not_gt hi
        have hShift : Term.shift (.var i) cutoff inc = .var (i + inc) :=
          Term.shift_var_ge (cutoff := cutoff) (inc := inc) (i := i) hi'
        simpa [hShift] using Par.var (i + inc)
  | lam h ih =>
      simpa [Term.shift] using Par.lam (ih (cutoff := cutoff + 1) (inc := inc))
  | app hf ha ihf iha =>
      simpa [Term.shift] using Par.app (ihf (cutoff := cutoff) (inc := inc)) (iha (cutoff := cutoff) (inc := inc))
  | beta hBody hArg ihBody ihArg =>
      rename_i body body' arg arg'
      -- Reduce the shifted redex with `Par.beta`, then rewrite the target using `shift_substTop`.
      have hBeta :
          Par (Term.shift (.app (.lam body) arg) cutoff inc)
            (Term.substTop (Term.shift arg' cutoff inc) (Term.shift body' (cutoff + 1) inc)) := by
        simpa [Term.shift] using
          Par.beta (body := Term.shift body (cutoff + 1) inc) (arg := Term.shift arg cutoff inc)
            (ihBody (cutoff := cutoff + 1) (inc := inc)) (ihArg (cutoff := cutoff) (inc := inc))
      simpa [Term.shift_substTop] using hBeta

/-! ## Complete development (Takahashi) -/

private theorem nodeCount_lt_app_fun (f a : Term) : f.nodeCount < (Term.app f a).nodeCount := by
  have hPos : 0 < 1 + a.nodeCount := by
    simp [Nat.one_add]
  have h : f.nodeCount < f.nodeCount + (1 + a.nodeCount) :=
    Nat.lt_add_of_pos_right hPos
  simpa [Term.nodeCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

private theorem nodeCount_lt_app_arg (f a : Term) : a.nodeCount < (Term.app f a).nodeCount := by
  have hPos : 0 < 1 + f.nodeCount := by
    simp [Nat.one_add]
  have h : a.nodeCount < (1 + f.nodeCount) + a.nodeCount :=
    Nat.lt_add_of_pos_left hPos
  simpa [Term.nodeCount, Nat.add_assoc] using h

private theorem nodeCount_lt_app_lam_body (body a : Term) : body.nodeCount < (Term.app (.lam body) a).nodeCount := by
  have hLam : body.nodeCount < (Term.lam body).nodeCount := by
    simp [Term.nodeCount, Nat.one_add]
  have hApp : (Term.lam body).nodeCount < (Term.app (.lam body) a).nodeCount :=
    nodeCount_lt_app_fun (f := Term.lam body) (a := a)
  exact Nat.lt_trans hLam hApp

def develop : Term → Term
  | .var i => .var i
  | .lam body => .lam (develop body)
  | .app (.lam body) a => Term.substTop (develop a) (develop body)
  | .app f a => .app (develop f) (develop a)
termination_by t => t.nodeCount
decreasing_by
  ·
    simp [Term.nodeCount, Nat.one_add]
  ·
    simpa using nodeCount_lt_app_arg (f := Term.lam body) (a := a)
  ·
    simpa using nodeCount_lt_app_lam_body (body := body) (a := a)
  ·
    simpa using nodeCount_lt_app_fun (f := f) (a := a)
  ·
    simpa using nodeCount_lt_app_arg (f := f) (a := a)

theorem develops : ∀ t : Term, Par t (develop t) := by
  intro t
  induction t with
  | var i =>
      simpa [develop] using Par.var i
  | lam body ih =>
      simpa [develop] using Par.lam ih
  | app f a ihf iha =>
      cases f with
      | lam body =>
          have ihf' : Par (Term.lam body) (Term.lam (develop body)) := by
            simpa [develop] using ihf
          cases ihf' with
          | lam hBody =>
              simpa [develop] using Par.beta (body := body) (arg := a) hBody iha
      | var i =>
          simpa [develop] using Par.app ihf iha
      | app f1 f2 =>
          simpa [develop] using Par.app ihf iha

/-! ## Substitution is compatible with `Par` -/

theorem subst {t t' s s' : Term} (ht : Par t t') (hs : Par s s') :
    ∀ n : Nat, Par (Term.subst s n t) (Term.subst s' n t') := by
  intro n
  induction ht generalizing n s s' with
  | var i =>
      by_cases hi : i = n
      ·
        subst hi
        simpa [Term.subst] using hs
      ·
        simpa [Term.subst, hi] using Par.var i
  | lam hBody ih =>
      have hsShift : Par (Term.shift s 0 1) (Term.shift s' 0 1) :=
        Par.shift (t := s) (u := s') hs (cutoff := 0) (inc := 1)
      simpa [Term.subst] using
        Par.lam (ih (n := n + 1) (s := Term.shift s 0 1) (s' := Term.shift s' 0 1) hsShift)
  | app hf ha ihf iha =>
      simpa [Term.subst] using
        Par.app (ihf (n := n) (s := s) (s' := s') hs) (iha (n := n) (s := s) (s' := s') hs)
  | beta hBody hArg ihBody ihArg =>
      rename_i body body' arg arg'
      -- Apply the IHs to the reduced body/argument, then show the target is the corresponding
      -- β-substitution after pushing the external substitution through `substTop`.
      let argSub : Term := Term.subst s n arg
      let argSub' : Term := Term.subst s' n arg'
      let bodySub : Term := Term.subst (Term.shift s 0 1) (n + 1) body
      let bodySub' : Term := Term.subst (Term.shift s' 0 1) (n + 1) body'

      have hsShift : Par (Term.shift s 0 1) (Term.shift s' 0 1) :=
        Par.shift (t := s) (u := s') hs (cutoff := 0) (inc := 1)

      have hArgSub : Par argSub argSub' := by
        simpa [argSub, argSub'] using (ihArg (n := n) (s := s) (s' := s') hs)

      have hBodySub : Par bodySub bodySub' := by
        simpa [bodySub, bodySub'] using
          (ihBody (n := n + 1) (s := Term.shift s 0 1) (s' := Term.shift s' 0 1) hsShift)

      have hRhs :
          Term.subst s' n (Term.substTop arg' body') =
            Term.substTop argSub' bodySub' := by
        have htShifted :
            Term.Shifted 1 0 (Term.subst (Term.shift arg' 0 1) 0 body') := by
          simpa using (Term.Shifted.subst_shifted (arg := arg') (t := body') (j := 0))
        have hSwap :
            Term.subst (Term.shift s' 0 1) (n + 1) (Term.subst (Term.shift arg' 0 1) 0 body') =
              Term.subst (Term.subst (Term.shift s' 0 1) (n + 1) (Term.shift arg' 0 1)) 0
                (Term.subst (Term.shift s' 0 1) (n + 1) body') := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Term.substitution_swap (t := body') (t₂ := arg') (t₃ := s') (m := 0) (n := n))
        have hShiftSub :
            Term.subst (Term.shift s' 0 1) (n + 1) (Term.shift arg' 0 1) =
              Term.shift (Term.subst s' n arg') 0 1 := by
          have : (0 : Nat) ≤ n := Nat.zero_le n
          simpa using
            (Term.shift_subst_of_le_cutoff (t := arg') (s := s') (j := n) (cutoff := 0) (inc := 1) this).symm
        calc
          Term.subst s' n (Term.substTop arg' body') =
              Term.shiftDown
                (Term.subst (Term.shift s' 0 1) (n + 1) (Term.subst (Term.shift arg' 0 1) 0 body')) 0 1 := by
            simpa [Term.substTop] using
              (Term.shiftDown_subst_swap' (n := n) (t := Term.subst (Term.shift arg' 0 1) 0 body')
                (s := s') htShifted).symm
          _ =
              Term.shiftDown
                (Term.subst (Term.subst (Term.shift s' 0 1) (n + 1) (Term.shift arg' 0 1)) 0
                  (Term.subst (Term.shift s' 0 1) (n + 1) body')) 0 1 := by
            simp [hSwap]
          _ =
              Term.shiftDown
                (Term.subst (Term.shift (Term.subst s' n arg') 0 1) 0
                  (Term.subst (Term.shift s' 0 1) (n + 1) body')) 0 1 := by
            simp [hShiftSub]
          _ = Term.substTop argSub' bodySub' := by
            simp [Term.substTop, argSub', bodySub']

      have hBeta :
          Par (Term.subst s n (Term.app (Term.lam body) arg)) (Term.substTop argSub' bodySub') := by
        simpa [Term.subst, argSub, bodySub] using
          (Par.beta (body := bodySub) (body' := bodySub') (arg := argSub) (arg' := argSub') hBodySub hArgSub)

      simpa [hRhs] using hBeta

end Par

namespace Par

/-! ## `Shifted` invariants and `shiftDown` compatibility -/

theorem shifted_preserve {d c : Nat} {t u : Term} (ht : Term.Shifted d c t) (h : Par t u) :
    Term.Shifted d c u := by
  induction h generalizing d c with
  | var i =>
      simpa using ht
  | lam h ih =>
      cases ht with
      | lam htBody =>
          exact Term.Shifted.lam (ih (d := d) (c := c + 1) htBody)
  | app hf ha ihf iha =>
      cases ht with
      | app htF htA =>
          exact Term.Shifted.app (ihf (d := d) (c := c) htF) (iha (d := d) (c := c) htA)
  | beta hBody hArg ihBody ihArg =>
      rename_i body body' arg arg'
      cases ht with
      | app htLam htArg =>
          cases htLam with
          | lam htBody =>
              have htBody' : Term.Shifted d (c + 1) body' :=
                ihBody (d := d) (c := c + 1) htBody
              have htArg' : Term.Shifted d c arg' :=
                ihArg (d := d) (c := c) htArg
              have htBody'' : Term.Shifted d (0 + 1 + c) body' := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htBody'
              have htSub :
                  Term.Shifted d (0 + c)
                    (Term.shiftDown (Term.subst (Term.shift arg' 0 (0 + 1)) 0 body') 0 1) :=
                Term.shifted_subst (d := d) (c := c) (n := 0) (t₁ := body') (t₂ := arg') htBody'' htArg'
              simpa [Term.substTop] using htSub

theorem shiftDown_conservation {d c : Nat} {t u : Term} (ht : Term.Shifted d c t) (h : Par t u) :
    Par (Term.shiftDown t c d) (Term.shiftDown u c d) := by
  induction h generalizing d c with
  | var i =>
      cases ht with
      | var_lt hlt =>
          have hDown : Term.shiftDown (.var i) c d = .var i :=
            Term.shiftDown_var_lt (cutoff := c) (dec := d) (i := i) hlt
          simpa [hDown] using Par.var i
      | var_ge hge =>
          have hci : c ≤ i := Nat.le_trans (Nat.le_add_right c d) hge
          have hDown : Term.shiftDown (.var i) c d = .var (i - d) :=
            Term.shiftDown_var_ge (cutoff := c) (dec := d) (i := i) hci
          simpa [hDown] using Par.var (i - d)
  | lam hBody ih =>
      cases ht with
      | lam htBody =>
          simpa [Term.shiftDown] using Par.lam (ih (d := d) (c := c + 1) htBody)
  | app hf ha ihf iha =>
      cases ht with
      | app htF htA =>
          simpa [Term.shiftDown] using
            Par.app (ihf (d := d) (c := c) htF) (iha (d := d) (c := c) htA)
  | beta hBody hArg ihBody ihArg =>
      rename_i body body' arg arg'
      cases ht with
      | app htLam htArg =>
          cases htLam with
          | lam htBody =>
              have htBody' : Term.Shifted d (c + 1) body' :=
                shifted_preserve (d := d) (c := c + 1) htBody hBody
              have htArg' : Term.Shifted d c arg' :=
                shifted_preserve (d := d) (c := c) htArg hArg

              have hBodyDown :
                  Par (Term.shiftDown body (c + 1) d) (Term.shiftDown body' (c + 1) d) :=
                ihBody (d := d) (c := c + 1) htBody
              have hArgDown : Par (Term.shiftDown arg c d) (Term.shiftDown arg' c d) :=
                ihArg (d := d) (c := c) htArg

              have hBetaDown :
                  Par (Term.shiftDown (Term.app (Term.lam body) arg) c d)
                    (Term.substTop (Term.shiftDown arg' c d) (Term.shiftDown body' (c + 1) d)) := by
                simpa [Term.shiftDown] using
                  Par.beta (body := Term.shiftDown body (c + 1) d) (body' := Term.shiftDown body' (c + 1) d)
                    (arg := Term.shiftDown arg c d) (arg' := Term.shiftDown arg' c d) hBodyDown hArgDown

              have hSwap :
                  Term.shiftDown (Term.substTop arg' body') c d =
                    Term.substTop (Term.shiftDown arg' c d) (Term.shiftDown body' (c + 1) d) := by
                let tSub : Term := Term.subst (Term.shift arg' 0 1) 0 body'
                have htSubShifted : Term.Shifted 1 0 tSub := by
                  simpa [tSub] using (Term.Shifted.subst_shifted (arg := arg') (t := body') (j := 0))
                have htSubstTopShifted : Term.Shifted d c (Term.shiftDown tSub 0 1) := by
                  have : Term.Shifted d c (Term.substTop arg' body') :=
                    shifted_preserve (d := d) (c := c)
                      (Term.Shifted.app (Term.Shifted.lam htBody) htArg)
                      (Par.beta (body := body) (body' := body') (arg := arg) (arg' := arg') hBody hArg)
                  simpa [Term.substTop, tSub] using this
                have hSwapDown :=
                  Term.shiftDown_shiftDown_swap (d := d) (c := c) (d' := 1) (c' := 0) (t := tSub)
                    (Nat.zero_le c) htSubShifted htSubstTopShifted

                have htShiftArg' : Term.Shifted d (c + 1) (Term.shift arg' 0 1) := by
                  have : (0 : Nat) ≤ c + d := Nat.zero_le _
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    (Term.Shifted.shift_shifted' (d := d) (c := c) (d' := 1) (c' := 0) (t := arg') this htArg')

                have hInner :
                    Term.shiftDown (Term.subst (Term.shift arg' 0 1) 0 body') (c + 1) d =
                      Term.subst (Term.shiftDown (Term.shift arg' 0 1) (c + 1) d) 0
                        (Term.shiftDown body' (c + 1) d) := by
                  simpa using
                    (Term.shiftDown_subst_swap2 (d := d) (c := c + 1) (n := 0) (t := body')
                      (s := Term.shift arg' 0 1) (Nat.succ_pos c) htBody' htShiftArg')

                have hShiftSwap :
                    Term.shiftDown (Term.shift arg' 0 1) (c + 1) d =
                      Term.shift (Term.shiftDown arg' c d) 0 1 := by
                  simpa using
                    (Term.shiftDown_shift_swap (d := d) (c := c) (d' := 1) (c' := 0) (t := arg')
                      (Nat.zero_le c) htArg').symm

                calc
                  Term.shiftDown (Term.substTop arg' body') c d =
                      Term.shiftDown (Term.shiftDown tSub 0 1) c d := by
                    simp [Term.substTop, tSub]
                  _ = Term.shiftDown (Term.shiftDown tSub (c + 1) d) 0 1 := by
                    simpa using hSwapDown
                  _ =
                      Term.shiftDown
                        (Term.shiftDown (Term.subst (Term.shift arg' 0 1) 0 body') (c + 1) d) 0 1 := by
                    simp [tSub]
                  _ =
                      Term.shiftDown
                        (Term.subst (Term.shiftDown (Term.shift arg' 0 1) (c + 1) d) 0
                          (Term.shiftDown body' (c + 1) d)) 0 1 := by
                    simp [hInner]
                  _ =
                      Term.shiftDown
                        (Term.subst (Term.shift (Term.shiftDown arg' c d) 0 1) 0
                          (Term.shiftDown body' (c + 1) d)) 0 1 := by
                    simp [hShiftSwap]
                  _ = Term.substTop (Term.shiftDown arg' c d) (Term.shiftDown body' (c + 1) d) := by
                    simp [Term.substTop]

              simpa [hSwap] using hBetaDown

theorem substTop {arg arg' body body' : Term} (hArg : Par arg arg') (hBody : Par body body') :
    Par (Term.substTop arg body) (Term.substTop arg' body') := by
  let t : Term := Term.subst (Term.shift arg 0 1) 0 body
  let t' : Term := Term.subst (Term.shift arg' 0 1) 0 body'
  have hShiftArg : Par (Term.shift arg 0 1) (Term.shift arg' 0 1) :=
    Par.shift (t := arg) (u := arg') hArg (cutoff := 0) (inc := 1)
  have hSub : Par t t' := by
    simpa [t, t'] using (Par.subst (ht := hBody) (hs := hShiftArg) 0)
  have htShifted : Term.Shifted 1 0 t := by
    simpa [t] using (Term.Shifted.subst_shifted (arg := arg) (t := body) (j := 0))
  have hDown :
      Par (Term.shiftDown t 0 1) (Term.shiftDown t' 0 1) :=
    shiftDown_conservation (d := 1) (c := 0) (t := t) (u := t') htShifted hSub
  simpa [Term.substTop, t, t'] using hDown

/-! ## Cofinality and diamond for `Par` -/

theorem develop_cofinal : ∀ {t u : Term}, Par t u → Par u (develop t) := by
  intro t u h
  induction h with
  | var i =>
      simpa [develop] using Par.var i
  | lam h ih =>
      simpa [develop] using Par.lam ih
  | app hf ha ihf iha =>
      rename_i f f' a a'
      cases f with
      | lam body =>
          cases hf with
          | lam hfBody =>
              rename_i body₁
              have ihfLam : Par (Term.lam body₁) (Term.lam (develop body)) := by
                simpa [develop] using ihf
              cases ihfLam with
              | lam hBodyDev =>
                  simpa [develop] using
                    Par.beta (body := body₁) (body' := develop body) (arg := a') (arg' := develop a) hBodyDev iha
      | var i =>
          simpa [develop] using Par.app ihf iha
      | app f1 f2 =>
          simpa [develop] using Par.app ihf iha
  | beta hBody hArg ihBody ihArg =>
      rename_i body body' arg arg'
      -- `develop` of a redex is its complete development β-reduction.
      simpa [develop] using (Par.substTop (hArg := ihArg) (hBody := ihBody))

theorem diamond {t u v : Term} (htu : Par t u) (htv : Par t v) : ∃ w : Term, Par u w ∧ Par v w := by
  refine ⟨develop t, develop_cofinal htu, develop_cofinal htv⟩

theorem church_rosser_reflTransGen {t u v : Term} (htu : Relation.ReflTransGen Par t u)
    (htv : Relation.ReflTransGen Par t v) :
    Relation.Join (Relation.ReflTransGen Par) u v := by
  classical
  apply Relation.church_rosser (r := Par) (a := t) (b := u) (c := v) ?_ htu htv
  intro a b c hab hac
  rcases diamond (t := a) hab hac with ⟨d, hbd, hcd⟩
  exact ⟨d, Relation.ReflGen.single hbd, Relation.ReflTransGen.single hcd⟩

end Par

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

end StepsLemmas

theorem Step.toPar {t u : Term} (h : Step t u) : Par t u := by
  induction h with
  | beta body arg =>
      exact Par.beta (body := body) (body' := body) (arg := arg) (arg' := arg) (Par.refl _) (Par.refl _)
  | app_left h ih =>
      exact Par.app ih (Par.refl _)
  | app_right h ih =>
      exact Par.app (Par.refl _) ih
  | lam_body h ih =>
      exact Par.lam ih

theorem Steps.toReflTransGenPar {t u : Term} (h : Steps t u) : Relation.ReflTransGen Par t u := by
  induction h with
  | refl t =>
      exact Relation.ReflTransGen.refl
  | trans hstep hsteps ih =>
      exact Relation.ReflTransGen.head (Step.toPar hstep) ih

theorem Par.toSteps {t u : Term} (h : Par t u) : Steps t u := by
  induction h with
  | var i =>
      exact Steps.refl (.var i)
  | lam h ih =>
      exact StepsLemmas.lam_body ih
  | app hf ha ihf iha =>
      rename_i f f' a a'
      have h1 : Steps (Term.app f a) (Term.app f' a) :=
        StepsLemmas.app_left (a := a) ihf
      have h2 : Steps (Term.app f' a) (Term.app f' a') :=
        StepsLemmas.app_right (f := f') iha
      exact StepsLemmas.trans h1 h2
  | beta hBody hArg ihBody ihArg =>
      rename_i body body' arg arg'
      have hLam : Steps (.lam body) (.lam body') :=
        StepsLemmas.lam_body ihBody
      have h1 : Steps (Term.app (Term.lam body) arg) (Term.app (Term.lam body') arg) :=
        StepsLemmas.app_left (a := arg) hLam
      have h2 : Steps (Term.app (Term.lam body') arg) (Term.app (Term.lam body') arg') :=
        StepsLemmas.app_right (f := Term.lam body') ihArg
      have h3 : Steps (Term.app (Term.lam body') arg') (Term.substTop arg' body') :=
        StepsLemmas.ofStep (Step.beta (body := body') (arg := arg'))
      exact StepsLemmas.trans h1 (StepsLemmas.trans h2 h3)

theorem ReflTransGenPar.toSteps {t u : Term} (h : Relation.ReflTransGen Par t u) : Steps t u := by
  induction h with
  | refl =>
      exact Steps.refl _
  | tail hab hbc ih =>
      exact StepsLemmas.trans ih (Par.toSteps hbc)

theorem Steps.churchRosser {t u v : Term} (htu : Steps t u) (htv : Steps t v) :
    ∃ w : Term, Steps u w ∧ Steps v w := by
  have hu : Relation.ReflTransGen Par t u := Steps.toReflTransGenPar htu
  have hv : Relation.ReflTransGen Par t v := Steps.toReflTransGenPar htv
  rcases Par.church_rosser_reflTransGen (t := t) (u := u) (v := v) hu hv with ⟨w, huw, hvw⟩
  refine ⟨w, ReflTransGenPar.toSteps huw, ReflTransGenPar.toSteps hvw⟩

end Lambda
end Combinators
end LoF
end HeytingLean
