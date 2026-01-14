import HeytingLean.LoF.Combinators.Category.BranchialBicategory
import HeytingLean.LoF.Combinators.Category.BranchialBicategoryTrunc

/-!
# BranchialAncestorFunctor — relating branchial ancestor objects to the multiway path category

`BranchialBicategory.lean` and `BranchialBicategoryTrunc.lean` package branchial “common ancestor”
data as spans in `Type` by using ancestor objects:

* path-sensitive: `LAncestors t = Σ a, LSteps a t`
* path-insensitive: `LAncestorsTrunc t = Σ a, Trunc (LSteps a t)`

This file relates those objects back to the *multiway path category* `MWObj` by:

1. defining how a labeled path `p : LSteps t u` acts on ancestor objects (postcomposition);
2. packaging that action as ordinary functors `MWObj ⥤ Type`;
3. recording canonical “common ancestor = pullback of projections” equivalences.

This is a conservative bridge: it does not assert pullbacks in `MWObj`; it only uses the fact that
ancestor objects live in `Type`, where pullbacks are explicit.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

open HeytingLean.LoF
open HeytingLean.LoF.Comb

namespace Branchial

open CategoryTheory

/-! ## Postcomposition action on ancestor objects -/

/-- Postcompose an explicit ancestor path with a labeled path `t ⟶* u`. -/
def mapLAncestors {t u : Comb} (p : LSteps t u) : LAncestors t → LAncestors u
  | ⟨a, q⟩ => ⟨a, LSteps.comp q p⟩

@[simp] theorem mapLAncestors_id {t : Comb} :
    mapLAncestors (t := t) (u := t) (LSteps.refl t) = (fun x => x) := by
  funext x
  cases x with
  | mk a q =>
      simp [mapLAncestors, LSteps.comp_refl_right]

theorem mapLAncestors_comp {t u v : Comb} (p : LSteps t u) (q : LSteps u v) :
    mapLAncestors (t := t) (u := v) (LSteps.comp p q) =
      (mapLAncestors (t := u) (u := v) q) ∘ (mapLAncestors (t := t) (u := u) p) := by
  funext x
  cases x with
  | mk a r =>
      simp [mapLAncestors, LSteps.comp_assoc, Function.comp]

/-- The ancestor-object functor for labeled paths: `t ↦ Σ a, LSteps a t`. -/
def ancestorsFunctor : MWObj ⥤ Type where
  obj X := LAncestors X.term
  map {X Y} p := mapLAncestors (t := X.term) (u := Y.term) p
  map_id := by
    intro X
    funext x
    cases x with
    | mk a q =>
        have hid : (𝟙 X : LSteps X.term X.term) = LSteps.refl X.term := rfl
        simp [mapLAncestors, hid]
  map_comp := by
    intro X Y Z p q
    funext x
    cases x with
    | mk a r =>
        apply Sigma.ext
        · rfl
        · -- reassociate the path concatenation
          simpa using (LSteps.comp_assoc (p := r) (q := p) (r := q)).symm

/-! ## Truncated ancestors (path-insensitive) -/

/-- Postcompose a truncated ancestor witness with a labeled path `t ⟶* u`. -/
def mapLAncestorsTrunc {t u : Comb} (p : LSteps t u) : LAncestorsTrunc t → LAncestorsTrunc u
  | ⟨a, tq⟩ =>
      ⟨a, Trunc.map (fun q => LSteps.comp q p) tq⟩

@[simp] theorem mapLAncestorsTrunc_id {t : Comb} :
    mapLAncestorsTrunc (t := t) (u := t) (LSteps.refl t) = (fun x => x) := by
  funext x
  cases x with
  | mk a tq =>
      -- `Trunc _` is subsingleton, so only the ancestor term matters.
      haveI : Subsingleton (Trunc (LSteps a t)) := by infer_instance
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (Subsingleton.elim _ _)

theorem mapLAncestorsTrunc_comp {t u v : Comb} (p : LSteps t u) (q : LSteps u v) :
    mapLAncestorsTrunc (t := t) (u := v) (LSteps.comp p q) =
      (mapLAncestorsTrunc (t := u) (u := v) q) ∘ (mapLAncestorsTrunc (t := t) (u := u) p) := by
  funext x
  cases x with
  | mk a tq =>
      -- `Trunc _` is subsingleton, so the second component is proof-irrelevant here.
      haveI : Subsingleton (Trunc (LSteps a v)) := by infer_instance
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (Subsingleton.elim _ _)

/-- The truncated ancestor-object functor: `t ↦ Σ a, Trunc (LSteps a t)`. -/
def ancestorsTruncFunctor : MWObj ⥤ Type where
  obj X := LAncestorsTrunc X.term
  map {X Y} p := mapLAncestorsTrunc (t := X.term) (u := Y.term) p
  map_id := by
    intro X
    funext x
    cases x with
    | mk a tq =>
        haveI : Subsingleton (Trunc (LSteps a X.term)) := by infer_instance
        apply Sigma.ext
        · rfl
        · exact heq_of_eq (Subsingleton.elim _ _)
  map_comp := by
    intro X Y Z p q
    funext x
    cases x with
    | mk a tq =>
        haveI : Subsingleton (Trunc (LSteps a Z.term)) := by infer_instance
        apply Sigma.ext
        · rfl
        · exact heq_of_eq (Subsingleton.elim _ _)

/-! ## Common ancestors as pullbacks (in `Type`) -/

/-- “Common labeled ancestors” are the pullback of the ancestor projections
`LAncestors t → Comb` and `LAncestors u → Comb`. -/
def commonEquivPullback (t u : Comb) :
    LCommonAncestors t u ≃ {p : LAncestors t × LAncestors u // p.1.1 = p.2.1} where
  toFun x := ⟨(⟨x.1, x.2.1⟩, ⟨x.1, x.2.2⟩), rfl⟩
  invFun p :=
    ⟨p.1.1.1, by
      -- coerce the equality of ancestor terms to rewrite the second component.
      refine (p.1.1.2, ?_)  -- left path, right path
      -- right path: transport along `p.2 : p.1.1.1 = p.1.2.1`
      -- Here both are `Comb`, so rewriting is fine.
      simpa [p.2] using p.1.2.2⟩
  left_inv x := by
    cases x with
    | mk a pq =>
      cases pq with
      | mk p q =>
        rfl
  right_inv p := by
    cases p with
    | mk pq heq =>
      cases pq with
      | mk xt xu =>
        cases xt with
        | mk a pt =>
          cases xu with
          | mk b pu =>
            cases heq
            rfl

/-- Truncated common ancestors are the pullback of truncated ancestor projections. -/
def commonTruncEquivPullback (t u : Comb) :
    LCommonAncestorsTrunc t u ≃
      {p : LAncestorsTrunc t × LAncestorsTrunc u // p.1.1 = p.2.1} where
  toFun x := ⟨(⟨x.1, x.2.1⟩, ⟨x.1, x.2.2⟩), rfl⟩
  invFun p :=
    ⟨p.1.1.1, by
      refine (p.1.1.2, ?_)
      simpa [p.2] using p.1.2.2⟩
  left_inv x := by
    cases x with
    | mk a pq =>
      cases pq with
      | mk p q =>
        rfl
  right_inv p := by
    cases p with
    | mk pq heq =>
      cases pq with
      | mk xt xu =>
        cases xt with
        | mk a pt =>
          cases xu with
          | mk b pu =>
            cases heq
            rfl

end Branchial

end Category
end Combinators
end LoF
end HeytingLean
