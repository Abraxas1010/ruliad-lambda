import Mathlib.Tactic
import HeytingLean.LoF.Combinators.Lambda.Syntax

/-!
# Lambda.ShiftSubst — shift/substitution algebra (de Bruijn)

This file collects “binder arithmetic” lemmas needed for confluence proofs:
interaction of `Term.shift`, `Term.shiftDown`, and `Term.subst`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Lambda

open Term

namespace Term

/-! ## A “no variables in the gap” predicate -/

/-- `Shifted d c t` means every de Bruijn index in `t` is either `< c` (untouched by shifting at
cutoff `c`) or `≥ c + d` (already shifted past the “gap” of size `d`). -/
inductive Shifted : Nat → Nat → Term → Prop where
  | var_lt {d c i : Nat} : i < c → Shifted d c (.var i)
  | var_ge {d c i : Nat} : c + d ≤ i → Shifted d c (.var i)
  | app {d c : Nat} {f a : Term} : Shifted d c f → Shifted d c a → Shifted d c (.app f a)
  | lam {d c : Nat} {body : Term} : Shifted d (c + 1) body → Shifted d c (.lam body)

namespace Shifted

theorem shift_shifted (d c : Nat) : ∀ t : Term, Shifted d c (Term.shift t c d) := by
  intro t
  induction t generalizing c with
  | var i =>
      by_cases h : i < c
      ·
        have : Term.shift (.var i) c d = .var i := Term.shift_var_lt (cutoff := c) (inc := d) (i := i) h
        simpa [this] using Shifted.var_lt (d := d) (c := c) (i := i) h
      ·
        have h' : c ≤ i := Nat.le_of_not_gt h
        have hShift : Term.shift (.var i) c d = .var (i + d) :=
          Term.shift_var_ge (cutoff := c) (inc := d) (i := i) h'
        have hShifted : Shifted d c (.var (i + d)) := by
          apply Shifted.var_ge (d := d) (c := c) (i := i + d)
          exact Nat.add_le_add_right h' d
        simpa [hShift] using hShifted
  | app f a ihf iha =>
      simp [Term.shift, Shifted.app, ihf, iha]
  | lam body ih =>
      simp [Term.shift, Shifted.lam, ih]

theorem weaken_gap {d c : Nat} {t : Term} :
    Shifted (d + 1) c t → Shifted 1 (c + d) t := by
  intro h
  induction h with
  | var_lt hlt =>
      rename_i c₀ i
      apply Shifted.var_lt (d := 1) (c := c₀ + d)
      exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right c₀ d)
  | var_ge hge =>
      rename_i c₀ i
      apply Shifted.var_ge (d := 1) (c := c₀ + d)
      -- Normalize `(c + d) + 1` into `c + (d + 1)`.
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hge
  | app hf ha ihf iha =>
      exact Shifted.app ihf iha
  | lam hbody ih =>
      rename_i c₀ body
      apply Shifted.lam
      -- IH produces `Shifted 1 ((c + 1) + d) body`, and `(c + 1) + d = (c + d) + 1`.
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih

/-- Shifting a `Shifted d c` term at any cutoff `c' ≤ c + d` preserves the gap `d`,
but moves its start by the shift amount. -/
theorem shift_shifted' {d c d' c' : Nat} {t : Term} :
    c' ≤ c + d → Shifted d c t → Shifted d (d' + c) (Term.shift t c' d') := by
  intro hcc hShifted
  induction hShifted generalizing c' with
  | var_lt hlt =>
      rename_i c₀ i
      by_cases hi : i < c'
      ·
        have hShift : Term.shift (.var i) c' d' = .var i :=
          Term.shift_var_lt (cutoff := c') (inc := d') (i := i) hi
        have : Shifted d (d' + c₀) (.var i) :=
          Shifted.var_lt (d := d) (c := d' + c₀) (i := i) (Nat.lt_of_lt_of_le hlt (Nat.le_add_left c₀ d'))
        simpa [hShift] using this
      ·
        have hic' : c' ≤ i := Nat.le_of_not_gt hi
        have hShift : Term.shift (.var i) c' d' = .var (i + d') :=
          Term.shift_var_ge (cutoff := c') (inc := d') (i := i) hic'
        have hlt' : i + d' < d' + c₀ := by
          have : i + d' < c₀ + d' := Nat.add_lt_add_right hlt d'
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
        have : Shifted d (d' + c₀) (.var (i + d')) :=
          Shifted.var_lt (d := d) (c := d' + c₀) (i := i + d') hlt'
        simpa [hShift] using this
  | var_ge hge =>
      rename_i c₀ i
      have hic' : c' ≤ i := Nat.le_trans hcc hge
      have hShift : Term.shift (.var i) c' d' = .var (i + d') :=
        Term.shift_var_ge (cutoff := c') (inc := d') (i := i) hic'
      have hge' : (d' + c₀) + d ≤ i + d' := by
        -- `(c₀ + d) + d' ≤ i + d'` and rearrange.
        have : (c₀ + d) + d' ≤ i + d' := Nat.add_le_add_right hge d'
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
      have : Shifted d (d' + c₀) (.var (i + d')) :=
        Shifted.var_ge (d := d) (c := d' + c₀) (i := i + d') hge'
      simpa [hShift] using this
  | app hf ha ihf iha =>
      simpa [Term.shift] using Shifted.app (ihf (c' := c') hcc) (iha (c' := c') hcc)
  | lam hbody ih =>
      rename_i c₀ body
      apply Shifted.lam
      have hcc' : c' + 1 ≤ (c₀ + 1) + d := by
        have : c' + 1 ≤ c₀ + d + 1 := Nat.succ_le_succ hcc
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
      simpa [Term.shift, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (ih (c' := c' + 1) hcc')

end Shifted

/-! ## Basic cancellation: `shiftDown` undoes `shift` above the cut -/

theorem shiftDown_shift_id :
    ∀ (t : Term) (c d : Nat), Term.shiftDown (Term.shift t c d) (c + d) d = t := by
  intro t c d
  induction t generalizing c with
  | var i =>
      by_cases h : i < c
      ·
        have hShift : Term.shift (.var i) c d = .var i := Term.shift_var_lt (cutoff := c) (inc := d) (i := i) h
        have hDown : Term.shiftDown (.var i) (c + d) d = .var i := by
          apply Term.shiftDown_var_lt
          exact Nat.lt_of_lt_of_le h (Nat.le_add_right c d)
        simp [hShift, hDown]
      ·
        have h' : c ≤ i := Nat.le_of_not_gt h
        have hShift : Term.shift (.var i) c d = .var (i + d) := Term.shift_var_ge (cutoff := c) (inc := d) (i := i) h'
        have hGe : c + d ≤ i + d := Nat.add_le_add_right h' d
        have hDown : Term.shiftDown (.var (i + d)) (c + d) d = .var ((i + d) - d) := by
          exact Term.shiftDown_var_ge (cutoff := c + d) (dec := d) (i := i + d) hGe
        simp [hShift, hDown]
  | app f a ihf iha =>
      simp [Term.shift, Term.shiftDown, ihf, iha]
  | lam body ih =>
      -- Peel the binder and use the induction hypothesis at cutoff `c + 1`.
      simp [Term.shift, Term.shiftDown]
      -- The cutoff arithmetic is `d + (c + 1) = (c + 1) + d`.
      simpa [Nat.add_assoc, Nat.add_comm] using (ih (c + 1))

theorem shiftDown_shift_cancel :
    ∀ (t : Term) (c d : Nat), Term.shiftDown (Term.shift t c d) c d = t := by
  intro t c d
  induction t generalizing c with
  | var i =>
      by_cases h : i < c
      ·
        have hShift : Term.shift (.var i) c d = .var i :=
          Term.shift_var_lt (cutoff := c) (inc := d) (i := i) h
        have hDown : Term.shiftDown (.var i) c d = .var i :=
          Term.shiftDown_var_lt (cutoff := c) (dec := d) (i := i) h
        simp [hShift, hDown]
      ·
        have h' : c ≤ i := Nat.le_of_not_gt h
        have hShift : Term.shift (.var i) c d = .var (i + d) :=
          Term.shift_var_ge (cutoff := c) (inc := d) (i := i) h'
        have hDown : Term.shiftDown (.var (i + d)) c d = .var ((i + d) - d) := by
          have : c ≤ i + d := Nat.le_trans h' (Nat.le_add_right i d)
          exact Term.shiftDown_var_ge (cutoff := c) (dec := d) (i := i + d) this
        simp [hShift, hDown]
  | app f a ihf iha =>
      simp [Term.shift, Term.shiftDown, ihf, iha]
  | lam body ih =>
      simp [Term.shift, Term.shiftDown]
      simpa using ih (c := c + 1)

theorem shiftDown_shift_setoff (t : Term) :
    ∀ {d c d' c' : Nat}, c ≤ c' → c' ≤ d' + d + c →
      Term.shiftDown (Term.shift t c (d' + d)) c' d' = Term.shift t c d := by
  intro d c d' c' hcc' hc'
  induction t generalizing c c' with
  | var n =>
      by_cases hn : n < c
      ·
        have hn' : n < c' := Nat.lt_of_lt_of_le hn hcc'
        simp [Term.shift_var_lt (cutoff := c) (inc := d' + d) (i := n) hn,
          Term.shiftDown_var_lt (cutoff := c') (dec := d') (i := n) hn',
          Term.shift_var_lt (cutoff := c) (inc := d) (i := n) hn]
      ·
        have hnc : c ≤ n := Nat.le_of_not_gt hn
        have hge : c' ≤ n + (d' + d) := by
          -- `c' ≤ c + d' + d ≤ n + d' + d`.
          have : c' ≤ c + (d' + d) := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc'
          exact Nat.le_trans this (Nat.add_le_add_right hnc (d' + d))
        simp [Term.shift_var_ge (cutoff := c) (inc := d' + d) (i := n) hnc,
          Term.shiftDown_var_ge (cutoff := c') (dec := d') (i := n + (d' + d)) hge,
          Term.shift_var_ge (cutoff := c) (inc := d) (i := n) hnc]
        omega
  | app f a ihf iha =>
      simp [Term.shift, Term.shiftDown, ihf (c := c) (c' := c') hcc' hc',
        iha (c := c) (c' := c') hcc' hc']
  | lam body ih =>
      have hcc'' : c + 1 ≤ c' + 1 := Nat.add_le_add_right hcc' 1
      have hc'' : c' + 1 ≤ d' + d + (c + 1) := by omega
      simp [Term.shift, Term.shiftDown, ih (c := c + 1) (c' := c' + 1) hcc'' hc'']

/-! ## Shift algebra -/

@[simp] theorem shift_zero (t : Term) : ∀ c : Nat, Term.shift t c 0 = t := by
  intro c
  induction t generalizing c with
  | var i =>
      by_cases h : i < c
      · simp [Term.shift_var_lt (cutoff := c) (inc := 0) (i := i) h]
      ·
        have h' : c ≤ i := Nat.le_of_not_gt h
        simp [Term.shift_var_ge (cutoff := c) (inc := 0) (i := i) h']
  | app f a ihf iha =>
      simp [Term.shift, ihf, iha]
  | lam body ih =>
      simp [Term.shift, ih]

theorem shift_shift_add (t : Term) :
    ∀ (c i₁ i₂ : Nat), Term.shift (Term.shift t c i₂) c i₁ = Term.shift t c (i₁ + i₂) := by
  intro c i₁ i₂
  induction t generalizing c with
  | var i =>
      by_cases h : i < c
      ·
        simp [Term.shift_var_lt (cutoff := c) (inc := i₂) (i := i) h,
          Term.shift_var_lt (cutoff := c) (inc := i₁) (i := i) h,
          Term.shift_var_lt (cutoff := c) (inc := i₁ + i₂) (i := i) h]
      ·
        have h' : c ≤ i := Nat.le_of_not_gt h
        have h'' : c ≤ i + i₂ := Nat.le_trans h' (Nat.le_add_right i i₂)
        have hLeft : Term.shift (Term.shift (.var i) c i₂) c i₁ = .var ((i + i₂) + i₁) := by
          have h₁ : Term.shift (.var i) c i₂ = .var (i + i₂) :=
            Term.shift_var_ge (cutoff := c) (inc := i₂) (i := i) h'
          have h₂ : Term.shift (.var (i + i₂)) c i₁ = .var ((i + i₂) + i₁) :=
            Term.shift_var_ge (cutoff := c) (inc := i₁) (i := i + i₂) h''
          simp [h₁, h₂]
        have hRight : Term.shift (.var i) c (i₁ + i₂) = .var (i + (i₁ + i₂)) :=
          Term.shift_var_ge (cutoff := c) (inc := i₁ + i₂) (i := i) h'
        -- Normalize arithmetic on both sides.
        simp [hLeft, hRight, Nat.add_left_comm, Nat.add_comm]
  | app f a ihf iha =>
      simp [Term.shift, ihf, iha]
  | lam body ih =>
      simp [Term.shift, ih]

namespace Shifted

/-- Substituting `shift arg 0 (j+1)` for index `j` removes occurrences of `j`
in the sense of `Shifted 1 j`. -/
theorem subst_shifted (arg : Term) :
    ∀ (t : Term) (j : Nat), Shifted 1 j (Term.subst (Term.shift arg 0 (j + 1)) j t) := by
  intro t
  induction t with
  | var k =>
      intro j
      by_cases hk : k = j
      · subst hk
        have hBig : Shifted (k + 1) 0 (Term.shift arg 0 (k + 1)) :=
          shift_shifted (d := k + 1) (c := 0) arg
        have hSmall : Shifted 1 k (Term.shift arg 0 (k + 1)) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (weaken_gap (d := k) (c := 0) (t := Term.shift arg 0 (k + 1)) hBig)
        simpa [Term.subst] using hSmall
      ·
        by_cases hlt : k < j
        ·
          simpa [Term.subst, hk] using Shifted.var_lt (d := 1) (c := j) (i := k) hlt
        ·
          have hjk : j ≤ k := Nat.le_of_not_gt hlt
          have hjk' : j < k := lt_of_le_of_ne hjk (Ne.symm hk)
          have hge : j + 1 ≤ k := Nat.succ_le_of_lt hjk'
          simpa [Term.subst, hk] using Shifted.var_ge (d := 1) (c := j) (i := k) hge
  | app f a ihf iha =>
      intro j
      simp [Term.subst, Shifted.app, ihf (j := j), iha (j := j)]
  | lam body ih =>
      intro j
      simp [Term.subst]
      refine Shifted.lam ?_
      have hshift :
          Term.shift (Term.shift arg 0 (j + 1)) 0 1 = Term.shift arg 0 (j + 2) := by
        -- Both shifts are at cutoff `0`, so they add on indices.
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (shift_shift_add (t := arg) (c := 0) (i₁ := 1) (i₂ := j + 1))
      have ih' : Shifted 1 (j + 1) (Term.subst (Term.shift arg 0 ((j + 1) + 1)) (j + 1) body) :=
        ih (j := j + 1)
      simpa [hshift, Nat.add_assoc] using ih'

end Shifted

theorem shift_shift_swap (t : Term) :
    ∀ {c c' i i' : Nat}, c ≤ c' →
      Term.shift (Term.shift t c' i') c i = Term.shift (Term.shift t c i) (c' + i) i' := by
  intro c c' i i' hcc'
  induction t generalizing c c' with
  | var n =>
      by_cases hn : n < c
      ·
        have hn' : n < c' := Nat.lt_of_lt_of_le hn hcc'
        have hn'' : n < c' + i := Nat.lt_of_lt_of_le hn' (Nat.le_add_right c' i)
        simp [Term.shift_var_lt (cutoff := c') (inc := i') (i := n) hn',
          Term.shift_var_lt (cutoff := c) (inc := i) (i := n) hn,
          Term.shift_var_lt (cutoff := c' + i) (inc := i') (i := n) hn'']
      ·
        have hnc : c ≤ n := Nat.le_of_not_gt hn
        by_cases hn' : n < c'
        ·
          have hlt : n + i < c' + i := Nat.add_lt_add_right hn' i
          simp [Term.shift_var_lt (cutoff := c') (inc := i') (i := n) hn',
            Term.shift_var_ge (cutoff := c) (inc := i) (i := n) hnc,
            Term.shift_var_lt (cutoff := c' + i) (inc := i') (i := n + i) hlt]
        ·
          have hnc' : c' ≤ n := Nat.le_of_not_gt hn'
          have hge₁ : c ≤ n + i' := Nat.le_trans hnc (Nat.le_add_right _ _)
          have hge₂ : c' + i ≤ n + i := Nat.add_le_add_right hnc' i
          have hL1 : Term.shift (.var n) c' i' = .var (n + i') :=
            Term.shift_var_ge (cutoff := c') (inc := i') (i := n) hnc'
          have hL2 : Term.shift (.var (n + i')) c i = .var ((n + i') + i) :=
            Term.shift_var_ge (cutoff := c) (inc := i) (i := n + i') hge₁
          have hR1 : Term.shift (.var n) c i = .var (n + i) :=
            Term.shift_var_ge (cutoff := c) (inc := i) (i := n) hnc
          have hR2 : Term.shift (.var (n + i)) (c' + i) i' = .var ((n + i) + i') :=
            Term.shift_var_ge (cutoff := c' + i) (inc := i') (i := n + i) hge₂
          simp [hL1, hL2, hR1, hR2]
          have : (n + i') + i = (n + i) + i' := by
            simp [Nat.add_left_comm, Nat.add_comm]
          simp [this]
  | app f a ihf iha =>
      simp [Term.shift, ihf, iha, hcc']
  | lam body ih =>
      simp [Term.shift, ih, Nat.add_assoc, Nat.add_comm, hcc']

/-! ## Swapping `shift` and `shiftDown` (under `Shifted`) -/

theorem shift_shiftDown_swap_of_Shifted {d d' c' : Nat} {t : Term} :
    Shifted d' c' t →
      ∀ {c : Nat}, c' ≤ c →
        Term.shift (Term.shiftDown t c' d') c d =
          Term.shiftDown (Term.shift t (c + d') d) c' d' := by
  intro hShifted
  induction hShifted with
  | var_lt hlt =>
      rename_i c₀ i
      intro c hcc
      -- The variable is below the `shiftDown` cutoff, so everything is unchanged.
      have hltc : i < c := Nat.lt_of_lt_of_le hlt hcc
      have hltc' : i < c + d' := Nat.lt_of_lt_of_le hltc (Nat.le_add_right c d')
      simp [Term.shiftDown_var_lt (cutoff := c₀) (dec := d') (i := i) hlt,
        Term.shift_var_lt (cutoff := c) (inc := d) (i := i) hltc,
        Term.shift_var_lt (cutoff := c + d') (inc := d) (i := i) hltc']
  | var_ge hge =>
      rename_i c₀ i
      intro c hcc
      have hc₀i : c₀ ≤ i := Nat.le_trans (Nat.le_add_right c₀ d') hge
      by_cases hcut : i < c + d'
      ·
        -- Below the shifted cutoff: the outer `shift` is inactive.
        have hlt : i - d' < c := by omega
        simp [Term.shiftDown_var_ge (cutoff := c₀) (dec := d') (i := i) hc₀i,
          Term.shift_var_lt (cutoff := c) (inc := d) (i := i - d') hlt,
          Term.shift_var_lt (cutoff := c + d') (inc := d) (i := i) hcut]
      ·
        -- Above the shifted cutoff: both sides shift by `d`, then unshift by `d'`.
        have hcut' : c + d' ≤ i := Nat.le_of_not_gt hcut
        have hge₁ : c ≤ i - d' := by omega
        have hc₀i2 : c₀ ≤ i + d := Nat.le_trans hc₀i (Nat.le_add_right _ _)
        simp [Term.shiftDown_var_ge (cutoff := c₀) (dec := d') (i := i) hc₀i,
          Term.shift_var_ge (cutoff := c) (inc := d) (i := i - d') hge₁,
          Term.shift_var_ge (cutoff := c + d') (inc := d) (i := i) hcut',
          Term.shiftDown_var_ge (cutoff := c₀) (dec := d') (i := i + d) hc₀i2]
        omega
  | app hf ha ihf iha =>
      intro c hcc
      simp [Term.shift, Term.shiftDown, ihf hcc, iha hcc]
  | lam hbody ih =>
      rename_i c₀ body
      intro c hcc
      -- Go under the binder (both cutoffs increase by 1).
      have hcc1 : c₀ + 1 ≤ c + 1 := Nat.add_le_add_right hcc 1
      simpa [Term.shift, Term.shiftDown, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih (c := c + 1) hcc1)

theorem shift_shiftDown_swap {d d' c c' : Nat} {t : Term} :
    c' ≤ c → Shifted d' c' t →
      Term.shift (Term.shiftDown t c' d') c d = Term.shiftDown (Term.shift t (c + d') d) c' d' := by
  intro hcc hShifted
  exact shift_shiftDown_swap_of_Shifted (d := d) (d' := d') (c' := c') (t := t) hShifted hcc

/-- The “other direction” swap: shifting after `shiftDown` at a higher cutoff can be pushed
through as `shiftDown` after shifting, with the `shiftDown` cutoff bumped. -/
theorem shiftDown_shift_swap {d c d' c' : Nat} {t : Term} :
    c' ≤ c → Shifted d c t →
      Term.shift (Term.shiftDown t c d) c' d' =
        Term.shiftDown (Term.shift t c' d') (c + d') d := by
  intro hcc hShifted
  induction t generalizing c c' with
  | var i =>
      cases hShifted with
      | var_lt hlt =>
          -- `shiftDown` is inactive; then the RHS `shiftDown` is also inactive since `i < c + d'`.
          by_cases hi : i < c'
          ·
            have hShift : Term.shift (.var i) c' d' = .var i :=
              Term.shift_var_lt (cutoff := c') (inc := d') (i := i) hi
            have hi' : i < c + d' := Nat.lt_of_lt_of_le hlt (Nat.le_add_right c d')
            have hDown : Term.shiftDown (.var i) (c + d') d = .var i :=
              Term.shiftDown_var_lt (cutoff := c + d') (dec := d) (i := i) hi'
            simp [Term.shiftDown_var_lt (cutoff := c) (dec := d) (i := i) hlt, hShift, hDown]
          ·
            have hic' : c' ≤ i := Nat.le_of_not_gt hi
            have hShift : Term.shift (.var i) c' d' = .var (i + d') :=
              Term.shift_var_ge (cutoff := c') (inc := d') (i := i) hic'
            have hi' : i + d' < c + d' := Nat.add_lt_add_right hlt d'
            have hDown : Term.shiftDown (.var (i + d')) (c + d') d = .var (i + d') :=
              Term.shiftDown_var_lt (cutoff := c + d') (dec := d) (i := i + d') hi'
            simp [Term.shiftDown_var_lt (cutoff := c) (dec := d) (i := i) hlt, hShift, hDown]
      | var_ge hge =>
          have hci : c ≤ i := Nat.le_trans (Nat.le_add_right c d) hge
          have hc'i : c' ≤ i := Nat.le_trans hcc hci
          have hci' : c ≤ i - d := Nat.le_sub_of_add_le hge
          have hc'i' : c' ≤ i - d := Nat.le_trans hcc hci'
          have hShiftL : Term.shift (.var (i - d)) c' d' = .var ((i - d) + d') :=
            Term.shift_var_ge (cutoff := c') (inc := d') (i := i - d) hc'i'
          have hShiftR : Term.shift (.var i) c' d' = .var (i + d') :=
            Term.shift_var_ge (cutoff := c') (inc := d') (i := i) hc'i
          have hDownL : Term.shiftDown (.var i) c d = .var (i - d) :=
            Term.shiftDown_var_ge (cutoff := c) (dec := d) (i := i) hci
          have hDownR : Term.shiftDown (.var (i + d')) (c + d') d = .var ((i + d') - d) := by
            have : c + d' ≤ i + d' := Nat.add_le_add_right hci d'
            exact Term.shiftDown_var_ge (cutoff := c + d') (dec := d) (i := i + d') this
          have hdi : d ≤ i := by
            -- `d ≤ c + d ≤ i`.
            exact Nat.le_trans (Nat.le_add_left d c) hge
          have heq : (i - d) + d' = (i + d') - d := by
            have h := Nat.add_sub_assoc hdi d'
            -- `d' + i - d = d' + (i - d)`; commute to match our goal.
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.symm
          simp [hDownL, hShiftL, hShiftR, hDownR, heq]
  | app f a ihf iha =>
      cases hShifted with
      | app hf ha =>
          simp [Term.shift, Term.shiftDown, ihf (c := c) (c' := c') hcc hf,
            iha (c := c) (c' := c') hcc ha]
  | lam body ih =>
      cases hShifted with
      | lam hbody =>
          have hcc' : c' + 1 ≤ c + 1 := Nat.succ_le_succ hcc
          simp [Term.shift, Term.shiftDown,
            ih (c := c + 1) (c' := c' + 1) hcc' hbody,
            Nat.add_assoc, Nat.add_comm]

/-! ## Interaction of `shift` with `subst` / `substTop` -/

theorem shift_subst_of_lt_cutoff :
    ∀ (t : Term) (s : Term) {j cutoff inc : Nat}, j < cutoff →
      Term.shift (Term.subst s j t) cutoff inc =
        Term.subst (Term.shift s cutoff inc) j (Term.shift t cutoff inc) := by
  intro t s j cutoff inc hj
  induction t generalizing j cutoff inc s with
  | var k =>
      by_cases hk : k = j
      · subst hk
        have hShiftVar : Term.shift (.var k) cutoff inc = .var k :=
          Term.shift_var_lt (cutoff := cutoff) (inc := inc) (i := k) hj
        simp [Term.subst, hShiftVar]
      ·
        by_cases hkcut : k < cutoff
        ·
          have hShiftVar : Term.shift (.var k) cutoff inc = .var k :=
            Term.shift_var_lt (cutoff := cutoff) (inc := inc) (i := k) hkcut
          simp [Term.subst, hk, hShiftVar]
        ·
          have hkge : cutoff ≤ k := Nat.le_of_not_gt hkcut
          have hShiftVar : Term.shift (.var k) cutoff inc = .var (k + inc) :=
            Term.shift_var_ge (cutoff := cutoff) (inc := inc) (i := k) hkge
          have hne : k + inc ≠ j := by
            intro hEq
            have hc : cutoff ≤ k + inc := Nat.le_trans hkge (Nat.le_add_right k inc)
            have : cutoff ≤ j := by simpa [hEq] using hc
            exact (Nat.not_le_of_gt hj) this
          simp [Term.subst, hk, hShiftVar, hne]
  | app f a ihf iha =>
      simp [Term.subst, Term.shift, ihf (s := s) (j := j) (cutoff := cutoff) (inc := inc) hj,
        iha (s := s) (j := j) (cutoff := cutoff) (inc := inc) hj]
  | lam body ih =>
      have hj' : j + 1 < cutoff + 1 := Nat.succ_lt_succ hj
      have hswap :
          Term.shift (Term.shift s 0 1) (cutoff + 1) inc =
            Term.shift (Term.shift s cutoff inc) 0 1 := by
        simpa using
          (shift_shift_swap (t := s) (c := 0) (c' := cutoff) (i := 1) (i' := inc) (Nat.zero_le cutoff)).symm
      have ih' :
          Term.shift (Term.subst (Term.shift s 0 1) (j + 1) body) (cutoff + 1) inc =
            Term.subst (Term.shift (Term.shift s 0 1) (cutoff + 1) inc) (j + 1)
              (Term.shift body (cutoff + 1) inc) :=
        ih (s := Term.shift s 0 1) (j := j + 1) (cutoff := cutoff + 1) (inc := inc) hj'
      simp [Term.subst, Term.shift, ih', hswap]

theorem shift_subst_of_le_cutoff :
    ∀ (t : Term) (s : Term) {j cutoff inc : Nat}, cutoff ≤ j →
      Term.shift (Term.subst s j t) cutoff inc =
        Term.subst (Term.shift s cutoff inc) (j + inc) (Term.shift t cutoff inc) := by
  intro t s j cutoff inc hj
  induction t generalizing j cutoff inc s with
  | var k =>
      by_cases hk : k = j
      ·
        subst hk
        simp [Term.subst, Term.shift_var_ge (cutoff := cutoff) (inc := inc) (i := k) hj]
      ·
        by_cases hkcut : k < cutoff
        ·
          have hShiftVar : Term.shift (.var k) cutoff inc = .var k :=
            Term.shift_var_lt (cutoff := cutoff) (inc := inc) (i := k) hkcut
          have hne : k ≠ j + inc := by
            intro hEq
            have : cutoff ≤ j + inc := Nat.le_trans hj (Nat.le_add_right j inc)
            have : cutoff ≤ k := by simpa [hEq] using this
            exact (Nat.not_le_of_gt hkcut) this
          simp [Term.subst, hk, hShiftVar, hne]
        ·
          have hkge : cutoff ≤ k := Nat.le_of_not_gt hkcut
          have hShiftVar : Term.shift (.var k) cutoff inc = .var (k + inc) :=
            Term.shift_var_ge (cutoff := cutoff) (inc := inc) (i := k) hkge
          simp [Term.subst, hk, hShiftVar]
  | app f a ihf iha =>
      simp [Term.subst, Term.shift, ihf (s := s) (j := j) (cutoff := cutoff) (inc := inc) hj,
        iha (s := s) (j := j) (cutoff := cutoff) (inc := inc) hj]
  | lam body ih =>
      have hj' : cutoff + 1 ≤ j + 1 := Nat.succ_le_succ hj
      have hswap :
          Term.shift (Term.shift s 0 1) (cutoff + 1) inc =
            Term.shift (Term.shift s cutoff inc) 0 1 := by
        simpa using
          (shift_shift_swap (t := s) (c := 0) (c' := cutoff) (i := 1) (i' := inc) (Nat.zero_le cutoff)).symm
      have ih' :
          Term.shift (Term.subst (Term.shift s 0 1) (j + 1) body) (cutoff + 1) inc =
            Term.subst (Term.shift (Term.shift s 0 1) (cutoff + 1) inc) (j + 1 + inc)
              (Term.shift body (cutoff + 1) inc) :=
        ih (s := Term.shift s 0 1) (j := j + 1) (cutoff := cutoff + 1) (inc := inc) hj'
      simp [Term.subst, Term.shift, ih', hswap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem shiftDown_subst_swap {c n : Nat} (t s : Term) :
    c ≤ n → Shifted 1 c t →
      Term.shiftDown (Term.subst (Term.shift s 0 (c + 1)) (n + 1) t) c 1 =
        Term.subst (Term.shift s 0 c) n (Term.shiftDown t c 1) := by
  intro hcn hShifted
  induction t generalizing c n s with
  | var m =>
      cases hShifted with
      | var_lt hlt =>
          have hm_lt_n : m < n := Nat.lt_of_lt_of_le hlt hcn
          have hne1 : m ≠ n + 1 := Nat.ne_of_lt (Nat.lt_of_lt_of_le hm_lt_n (Nat.le_succ n))
          have hne2 : m ≠ n := Nat.ne_of_lt hm_lt_n
          have hDown : Term.shiftDown (.var m) c 1 = .var m :=
            Term.shiftDown_var_lt (cutoff := c) (dec := 1) (i := m) hlt
          simp [Term.subst, hne1, hne2, hDown]
      | var_ge hge =>
          by_cases hm : m = n + 1
          ·
            subst hm
            have hset :
                Term.shiftDown (Term.shift s 0 (c + 1)) c 1 = Term.shift s 0 c := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (shiftDown_shift_setoff (t := s) (d := c) (c := 0) (d' := 1) (c' := c)
                  (Nat.zero_le c) (by omega))
            have hDown : Term.shiftDown (.var (n + 1)) c 1 = .var ((n + 1) - 1) :=
              Term.shiftDown_var_ge (cutoff := c) (dec := 1) (i := n + 1) (Nat.le_trans hcn (Nat.le_succ n))
            simp [Term.subst, hset, hDown]
          ·
            have hmc : c ≤ m := Nat.le_trans (Nat.le_add_right c 1) hge
            have hne : m - 1 ≠ n := by
              intro hEq
              have hmpos : 0 < m := by
                have : 1 ≤ m := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le c)) hge
                exact Nat.lt_of_lt_of_le (Nat.zero_lt_one) this
              have hsucc : Nat.succ (m - 1) = m := by
                simpa [Nat.pred_eq_sub_one] using Nat.succ_pred_eq_of_pos hmpos
              have hcong : Nat.succ (m - 1) = Nat.succ n := congrArg Nat.succ hEq
              have : m = n + 1 := by
                have : m = Nat.succ n := Eq.trans (Eq.symm hsucc) hcong
                simpa [Nat.succ_eq_add_one] using this
              exact hm this
            have hDown : Term.shiftDown (.var m) c 1 = .var (m - 1) :=
              Term.shiftDown_var_ge (cutoff := c) (dec := 1) (i := m) hmc
            simp [Term.subst, hm, hDown, hne]
  | app f a ihf iha =>
      cases hShifted with
      | app hf ha =>
          simp [Term.subst, Term.shiftDown, ihf (c := c) (n := n) (s := s) hcn hf,
            iha (c := c) (n := n) (s := s) hcn ha]
  | lam body ih =>
      cases hShifted with
      | lam hbody =>
          have hcn' : c + 1 ≤ n + 1 := Nat.succ_le_succ hcn
          have ih' := ih (c := c + 1) (n := n + 1) (s := s) hcn' hbody
          have hShift1 : Term.shift (Term.shift s 0 (c + 1)) 0 1 = Term.shift s 0 (c + 2) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (shift_shift_add (t := s) (c := 0) (i₁ := 1) (i₂ := c + 1))
          have hShift2 : Term.shift (Term.shift s 0 c) 0 1 = Term.shift s 0 (c + 1) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (shift_shift_add (t := s) (c := 0) (i₁ := 1) (i₂ := c))
          simp [Term.subst, Term.shiftDown, ih', hShift1, hShift2, Nat.add_comm, Nat.add_left_comm]

theorem shiftDown_subst_swap' {n : Nat} (t s : Term) (h : Shifted 1 0 t) :
    Term.shiftDown (Term.subst (Term.shift s 0 1) (n + 1) t) 0 1 =
      Term.subst s n (Term.shiftDown t 0 1) := by
  simpa using (shiftDown_subst_swap (t := t) (s := s) (c := 0) (n := n) (Nat.zero_le n) h)

theorem shiftDown_subst_swap2 {d c n : Nat} (t s : Term) :
    n < c → Shifted d c t → Shifted d c s →
      Term.shiftDown (Term.subst s n t) c d =
        Term.subst (Term.shiftDown s c d) n (Term.shiftDown t c d) := by
  intro hnc ht hs
  induction t generalizing c n s with
  | var m =>
      cases ht with
      | var_lt hlt =>
          by_cases hm : m = n
          ·
            subst hm
            -- substitution hits the variable; `shiftDown` just acts on the substituted term.
            have hDownVar : Term.shiftDown (.var m) c d = .var m :=
              Term.shiftDown_var_lt (cutoff := c) (dec := d) (i := m) hlt
            simp [Term.subst, hDownVar]
          ·
            have hm' : m ≠ n := hm
            have hDown : Term.shiftDown (.var m) c d = .var m :=
              Term.shiftDown_var_lt (cutoff := c) (dec := d) (i := m) hlt
            simp [Term.subst, hm', hDown]
      | var_ge hge =>
          have hmne : m ≠ n := by
            intro hEq
            have : c ≤ n := by simpa [hEq] using Nat.le_trans (Nat.le_add_right c d) hge
            exact (Nat.not_le_of_gt hnc) this
          have hmc : c ≤ m := Nat.le_trans (Nat.le_add_right c d) hge
          have hmcd : c + d ≤ m := hge
          have hmd : c ≤ m - d := by omega
          have hmne' : m - d ≠ n := by
            intro hEq
            have : c ≤ n := by simpa [hEq] using hmd
            exact (Nat.not_le_of_gt hnc) this
          have hDown : Term.shiftDown (.var m) c d = .var (m - d) :=
            Term.shiftDown_var_ge (cutoff := c) (dec := d) (i := m) hmc
          simp [Term.subst, hmne, hmne', hDown]
  | app f a ihf iha =>
      cases ht with
      | app hf ha =>
          simp [Term.subst, Term.shiftDown, ihf (c := c) (n := n) (s := s) hnc hf hs,
            iha (c := c) (n := n) (s := s) hnc ha hs]
  | lam body ih =>
      cases ht with
      | lam hbody =>
          have hnc' : n + 1 < c + 1 := Nat.succ_lt_succ hnc
          have hsShift : Shifted d (c + 1) (Term.shift s 0 1) := by
            have : (0 : Nat) ≤ c + d := Nat.zero_le _
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (Shifted.shift_shifted' (d := d) (c := c) (d' := 1) (c' := 0) (t := s) this hs)
          have ih' :=
            ih (c := c + 1) (n := n + 1) (s := Term.shift s 0 1) hnc' hbody hsShift
          have hswap :
              Term.shiftDown (Term.shift s 0 1) (c + 1) d =
                Term.shift (Term.shiftDown s c d) 0 1 := by
            have hcc0 : (0 : Nat) ≤ c := Nat.zero_le c
            simpa using (shiftDown_shift_swap (d := d) (c := c) (d' := 1) (c' := 0) (t := s) hcc0 hs).symm
          simp [Term.subst, Term.shiftDown, ih', hswap]

theorem shiftDown_shiftDown_swap {d c d' c' : Nat} {t : Term} :
    c' ≤ c → Shifted d' c' t → Shifted d c (Term.shiftDown t c' d') →
      Term.shiftDown (Term.shiftDown t c' d') c d =
        Term.shiftDown (Term.shiftDown t (c + d') d) c' d' := by
  intro hcc hShifted₁ hShifted₂
  induction t generalizing c c' with
  | var i =>
      cases hShifted₁ with
      | var_lt hlt =>
          have hltc : i < c := Nat.lt_of_lt_of_le hlt hcc
          have hltcd : i < c + d' := Nat.lt_of_lt_of_le hltc (Nat.le_add_right c d')
          simp [Term.shiftDown_var_lt (cutoff := c') (dec := d') (i := i) hlt,
            Term.shiftDown_var_lt (cutoff := c) (dec := d) (i := i) hltc,
            Term.shiftDown_var_lt (cutoff := c + d') (dec := d) (i := i) hltcd]
      | var_ge hge =>
          have hc'i : c' ≤ i := Nat.le_trans (Nat.le_add_right c' d') hge
          have hd'i : d' ≤ i := Nat.le_trans (Nat.le_add_left d' c') hge
          have hDown₁ : Term.shiftDown (.var i) c' d' = .var (i - d') :=
            Term.shiftDown_var_ge (cutoff := c') (dec := d') (i := i) hc'i
          have hShifted₂' : Shifted d c (.var (i - d')) := by
            simpa [hDown₁] using hShifted₂
          cases hShifted₂' with
          | var_lt hlt2 =>
              have hi_lt : i < c + d' := (Nat.sub_lt_iff_lt_add hd'i).1 hlt2
              have hDownL : Term.shiftDown (.var (i - d')) c d = .var (i - d') :=
                Term.shiftDown_var_lt (cutoff := c) (dec := d) (i := i - d') hlt2
              have hDownR₁ : Term.shiftDown (.var i) (c + d') d = .var i :=
                Term.shiftDown_var_lt (cutoff := c + d') (dec := d) (i := i) hi_lt
              simp [hDown₁, hDownL, hDownR₁]
            | var_ge hge2 =>
                have hcd : c + d ≤ i := Nat.le_trans hge2 (Nat.sub_le _ _)
                have hc2 : c + d' ≤ i := by
                  have : c + d + d' ≤ i := by
                    -- `(c + d) + d' ≤ (i - d') + d' = i`.
                    have : c + d + d' ≤ (i - d') + d' := Nat.add_le_add_right hge2 d'
                    simpa [Nat.sub_add_cancel hd'i, Nat.add_assoc] using this
                  omega
                have hc'i2 : c' ≤ i - d := Nat.le_trans hcc (Nat.le_sub_of_add_le hcd)
                have hDownL : Term.shiftDown (.var (i - d')) c d = .var ((i - d') - d) :=
                  Term.shiftDown_var_ge (cutoff := c) (dec := d) (i := i - d') (Nat.le_trans (Nat.le_add_right c d) hge2)
                have hDownR₁ : Term.shiftDown (.var i) (c + d') d = .var (i - d) :=
                  Term.shiftDown_var_ge (cutoff := c + d') (dec := d) (i := i) hc2
                have hDownR₂ : Term.shiftDown (.var (i - d)) c' d' = .var ((i - d) - d') :=
                  Term.shiftDown_var_ge (cutoff := c') (dec := d') (i := i - d) hc'i2
                have heq : (i - d') - d = (i - d) - d' := by
                  -- Both sides are `i - (d + d')`.
                  calc
                    (i - d') - d = i - (d' + d) := by
                      exact (Nat.sub_add_eq i d' d).symm
                    _ = i - (d + d') := by
                      simp [Nat.add_comm]
                    _ = (i - d) - d' := by
                      exact (Nat.sub_add_eq i d d')
                simp [hDown₁, hDownL, hDownR₁, hDownR₂, heq]
    | app f a ihf iha =>
        cases hShifted₁ with
        | app hf ha =>
            cases hShifted₂ with
            | app hf' ha' =>
                simp [Term.shiftDown, ihf (c := c) (c' := c') hcc hf hf',
                  iha (c := c) (c' := c') hcc ha ha']
  | lam body ih =>
      cases hShifted₁ with
      | lam hbody1 =>
          cases hShifted₂ with
          | lam hbody2 =>
              have hcc' : c' + 1 ≤ c + 1 := Nat.succ_le_succ hcc
              simp [Term.shiftDown,
                ih (c := c + 1) (c' := c' + 1) hcc' hbody1 hbody2,
                Nat.add_assoc, Nat.add_comm]

/-- If `t₁` has a `d`-gap starting at `n+1+c` and `t₂` has a `d`-gap starting at `c`,
then performing the capture-avoiding substitution at index `n` and dropping one level
via `shiftDown n 1` preserves the `d`-gap (now starting at `n+c`). -/
theorem shifted_subst {d c n : Nat} {t₁ t₂ : Term} :
    Shifted d (n + 1 + c) t₁ → Shifted d c t₂ →
      Shifted d (n + c) (Term.shiftDown (Term.subst (Term.shift t₂ 0 (n + 1)) n t₁) n 1) := by
  intro ht₁ ht₂
  induction t₁ generalizing n with
  | var i =>
      cases ht₁ with
      | var_lt hlt =>
          by_cases hi : i = n
          ·
            subst hi
            have hset :
                Term.shiftDown (Term.shift t₂ 0 (i + 1)) i 1 = Term.shift t₂ 0 i := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (shiftDown_shift_setoff (t := t₂) (d := i) (c := 0) (d' := 1) (c' := i)
                  (Nat.zero_le i) (by omega))
            have hShifted : Shifted d (i + c) (Term.shift t₂ 0 i) := by
              have : (0 : Nat) ≤ c + d := Nat.zero_le _
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (Shifted.shift_shifted' (d := d) (c := c) (d' := i) (c' := 0) (t := t₂) this ht₂)
            simpa [Term.subst, hset] using hShifted
          ·
            by_cases hin : i < n
            ·
              have hDown : Term.shiftDown (.var i) n 1 = .var i :=
                Term.shiftDown_var_lt (cutoff := n) (dec := 1) (i := i) hin
              have : Shifted d (n + c) (.var i) :=
                Shifted.var_lt (d := d) (c := n + c) (i := i) (Nat.lt_of_lt_of_le hin (Nat.le_add_right n c))
              simpa [Term.subst, hi, hDown] using this
            ·
              have hnle : n ≤ i := Nat.le_of_not_gt hin
              have hDown : Term.shiftDown (.var i) n 1 = .var (i - 1) :=
                Term.shiftDown_var_ge (cutoff := n) (dec := 1) (i := i) hnle
              have hlt' : i - 1 < n + c := by omega
              have : Shifted d (n + c) (.var (i - 1)) :=
                Shifted.var_lt (d := d) (c := n + c) (i := i - 1) hlt'
              simpa [Term.subst, hi, hDown] using this
      | var_ge hge =>
          have hi : i ≠ n := by omega
          have hnle : n ≤ i := by omega
          have hDown : Term.shiftDown (.var i) n 1 = .var (i - 1) :=
            Term.shiftDown_var_ge (cutoff := n) (dec := 1) (i := i) hnle
          have : Shifted d (n + c) (.var (i - 1)) := by
            apply Shifted.var_ge (d := d) (c := n + c) (i := i - 1)
            omega
          simpa [Term.subst, hi, hDown] using this
  | app f a ihf iha =>
      cases ht₁ with
      | app hf ha =>
          simpa [Term.subst, Term.shiftDown] using Shifted.app (ihf (n := n) hf) (iha (n := n) ha)
  | lam body ih =>
      cases ht₁ with
      | lam hbody =>
          apply Shifted.lam
          have hShift : Term.shift (Term.shift t₂ 0 (n + 1)) 0 1 = Term.shift t₂ 0 (n + 2) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (shift_shift_add (t := t₂) (c := 0) (i₁ := 1) (i₂ := n + 1))
          simpa [Term.subst, Term.shiftDown, Term.shift, hShift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (ih (n := n + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody))

theorem subst_shifted_cancel {d c n : Nat} (t s : Term) :
    c ≤ n → n < c + d → Shifted d c t → Term.subst s n t = t := by
  intro hcn hnc hShifted
  induction hShifted generalizing n s with
  | var_lt hlt =>
      rename_i i
      have : i ≠ n := by
        have : i < n := Nat.lt_of_lt_of_le hlt hcn
        exact Nat.ne_of_lt this
      simp [Term.subst, this]
  | var_ge hge =>
      rename_i i
      have : i ≠ n := by
        have : n < i := Nat.lt_of_lt_of_le hnc hge
        exact (Nat.ne_of_lt this).symm
      simp [Term.subst, this]
  | app hf ha ihf iha =>
      simp [Term.subst, ihf (n := n) (s := s) hcn hnc, iha (n := n) (s := s) hcn hnc]
  | lam hbody ih =>
      rename_i c₀ body
      have hcn' : c₀ + 1 ≤ n + 1 := Nat.succ_le_succ hcn
      have hnc' : n + 1 < (c₀ + 1) + d := by omega
      have hbodyEq : Term.subst (Term.shift s 0 1) (n + 1) body = body :=
        ih (n := n + 1) (s := Term.shift s 0 1) hcn' hnc'
      simpa [Term.subst] using congrArg Term.lam hbodyEq

theorem substitution_swap {n m : Nat} (t t₂ t₃ : Term) :
    Term.subst (Term.shift t₃ 0 (m + 1)) (m + 1 + n)
        (Term.subst (Term.shift t₂ 0 (m + 1)) m t) =
      Term.subst
          (Term.subst (Term.shift t₃ 0 (m + 1)) (m + 1 + n) (Term.shift t₂ 0 (m + 1))) m
          (Term.subst (Term.shift t₃ 0 (m + 1)) (m + 1 + n) t) := by
  induction t generalizing m n t₂ t₃ with
  | var k =>
      classical
      by_cases hk1 : m = k
      ·
        subst hk1
        have hmne : m ≠ m + 1 + n := by omega
        simp [Term.subst, hmne]
      ·
        by_cases hk2 : m + 1 + n = k
        ·
          subst hk2
          have hstay :
              Term.subst (Term.subst (Term.shift t₃ 0 (m + 1)) (m + 1 + n) (Term.shift t₂ 0 (m + 1))) m
                  (Term.shift t₃ 0 (m + 1)) =
                Term.shift t₃ 0 (m + 1) := by
            apply subst_shifted_cancel (t := Term.shift t₃ 0 (m + 1))
              (s := Term.subst (Term.shift t₃ 0 (m + 1)) (m + 1 + n) (Term.shift t₂ 0 (m + 1)))
              (c := 0) (d := m + 1) (n := m)
            · exact Nat.zero_le _
            · omega
            · simpa using (Shifted.shift_shifted (d := m + 1) (c := 0) t₃)
          have hne : m + 1 + n ≠ m := by omega
          simp [Term.subst, hne, hstay]
        ·
          have hkm : k ≠ m := by
            exact (Ne.symm hk1)
          have hkpeak : k ≠ m + 1 + n := by
            exact (Ne.symm hk2)
          simp [Term.subst, hkm, hkpeak]
  | app f a ihf iha =>
      simp [Term.subst, ihf, iha]
  | lam body ih =>
      simp [Term.subst]
      have hshift₂ : Term.shift (Term.shift t₂ 0 (m + 1)) 0 1 = Term.shift t₂ 0 (m + 2) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (shift_shift_add (t := t₂) (c := 0) (i₁ := 1) (i₂ := m + 1))
      have hshift₃ : Term.shift (Term.shift t₃ 0 (m + 1)) 0 1 = Term.shift t₃ 0 (m + 2) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (shift_shift_add (t := t₃) (c := 0) (i₁ := 1) (i₂ := m + 1))
      have hshift_swap :
          Term.shift
              (Term.subst (Term.shift t₃ 0 (m + 1)) (n + (m + 1)) (Term.shift t₂ 0 (m + 1))) 0 1 =
            Term.subst (Term.shift t₃ 0 (m + 2)) (n + (m + 2)) (Term.shift t₂ 0 (m + 2)) := by
        have : (0 : Nat) ≤ n + (m + 1) := Nat.zero_le _
        simpa [hshift₂, hshift₃, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (shift_subst_of_le_cutoff (t := Term.shift t₂ 0 (m + 1)) (s := Term.shift t₃ 0 (m + 1))
            (j := n + (m + 1)) (cutoff := 0) (inc := 1) this)
      have hEq : n + (m + 1) + 1 = n + (m + 2) := by omega
      -- Reduce the binder case to the induction hypothesis on the body.
      simpa [hshift₂, hshift₃, hshift_swap, hEq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg Term.lam (ih (m := m + 1) (n := n) (t₂ := t₂) (t₃ := t₃))

theorem shift_substTop (arg body : Term) (cutoff inc : Nat) :
    Term.shift (Term.substTop arg body) cutoff inc =
      Term.substTop (Term.shift arg cutoff inc) (Term.shift body (cutoff + 1) inc) := by
  let t : Term := Term.subst (Term.shift arg 0 1) 0 body
  have htShifted : Shifted 1 0 t := by
    -- This is the `j = 0` instance of `Shifted.subst_shifted`.
    simpa [t] using (Shifted.subst_shifted (arg := arg) (t := body) (j := 0))
  have hswap :=
    shift_shiftDown_swap (d := inc) (d' := 1) (c := cutoff) (c' := 0) (t := t) (Nat.zero_le cutoff) htShifted
  have htShift :
      Term.shift t (cutoff + 1) inc =
        Term.subst (Term.shift (Term.shift arg 0 1) (cutoff + 1) inc) 0 (Term.shift body (cutoff + 1) inc) := by
    have : (0 : Nat) < cutoff + 1 := Nat.succ_pos cutoff
    simpa [t] using
      (shift_subst_of_lt_cutoff (t := body) (s := Term.shift arg 0 1) (j := 0) (cutoff := cutoff + 1)
        (inc := inc) this)
  have hArg :
      Term.shift (Term.shift arg 0 1) (cutoff + 1) inc =
        Term.shift (Term.shift arg cutoff inc) 0 1 := by
    simpa using
      (shift_shift_swap (t := arg) (c := 0) (c' := cutoff) (i := 1) (i' := inc) (Nat.zero_le cutoff)).symm
  -- Rewrite the RHS of the `shift_shiftDown_swap` result into the `substTop` form.
  simpa [Term.substTop, t, htShift, hArg] using hswap

end Term

end Lambda
end Combinators
end LoF
end HeytingLean
