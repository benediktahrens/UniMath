(**
“Displayed equivalences” of displayed (pre)categories
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.equivalences.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences_bis.


Definition preserves_cartesianness
           {C C' : category}
           {F : functor C C'}
           {D} {D'}
           (FF : disp_functor F D D') : UU
  :=
    ∏ (c c' : C) (f : C⟦c, c'⟧)
      (d : D c) (d' : D c')
      (ff : d -->[f] d'),
    is_cartesian ff -> is_cartesian (#FF ff).




Section fix_disp_adjunction.

Context {C C' : category}
        (A : adjunction C C')
        {D : disp_cat C}
        {D': disp_cat C'}
        (X : disp_adjunction A D D').
(*
Let F : functor _ _ := left_adj A.
*)
Let FF : disp_functor _ D D' := left_adj_over X.
Let GG : disp_functor _ D' D := right_adj_over X.


Lemma right_over_adj_preserves_cartesianness : preserves_cartesianness GG.
Proof.
  unfold preserves_cartesianness.
  intros c c' f d d' ff ff_cart.
  intros c'' g d'' h.
  unfold is_cartesian in ff_cart.

  (** Path to happiness:

- construct homset-isomorphisms defined by a displayed adjunction;
  in particular,
  d -->[g] GG e  ≃   FF d -->[F g · counit _ ] e
- this equivalence is the equivalence in the first component of
   an equivalence between sigma types as occurring in def of [is_cartesian]
- use lemma saying that given an equivalence of types where one type is contractible,
  the other is, too
*)

Abort.

End fix_disp_adjunction.