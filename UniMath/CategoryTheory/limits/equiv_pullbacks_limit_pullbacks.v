
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.

Require Import UniMath.CategoryTheory.limits.limits_via_colimits.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.limits.pullbacks_as_colimits.
Require Export UniMath.CategoryTheory.limits.pullbacks .

Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").


Section fix_a_category.

Variable C : precategory.
Variable hs: has_homsets C.

Lemma equiv_isPullback_1 {a b c d : C} (f : C ⟦b, a⟧) (g : C ⟦c, a⟧)
           (p1 : C⟦d,b⟧) (p2 : C⟦d,c⟧) (H : p1 ;; f = p2;; g) :
isPullback f g p1 p2 H -> limits.pullbacks_as_colimits.isPullback _ f g p1 p2 H.
Proof.
  intro X.
  intros R cc.
  set (XR := mk_Pullback _ _ _ _ _ _ X).
  mkpair.
  - mkpair.
    + use (PullbackArrow XR).
      * apply (coconeIn cc One).
      * apply (coconeIn cc Three).
      * abstract (
        assert (XRT := coconeInCommutes cc Two Three tt); simpl in XRT;
        eapply pathscomp0; [| apply (!XRT)]; clear XRT;
        assert (XRT := coconeInCommutes cc Two One tt); simpl in XRT;
        eapply pathscomp0; [| apply (XRT)]; apply idpath
         ).
    + simpl. intro v; induction v; simpl.
      * apply (PullbackArrow_PullbackPr1 XR).
      * rewrite assoc.
        rewrite  (PullbackArrow_PullbackPr1 XR).
        assert (XRT := coconeInCommutes cc Two One tt); simpl in XRT;
        eapply pathscomp0; [| apply (XRT)]; apply idpath.
      * apply (PullbackArrow_PullbackPr2 XR).
  - intro t.
    apply subtypeEquality.
    { intro. apply impred; intro. apply hs. }
    simpl. destruct t as [t HH].  simpl in *.
    apply PullbackArrowUnique.
    + apply (HH One).
    + apply (HH Three).
Defined.

Lemma equiv_isPullback_2 {a b c d : C} (f : C ⟦b, a⟧) (g : C ⟦c, a⟧)
           (p1 : C⟦d,b⟧) (p2 : C⟦d,c⟧) (H : p1 ;; f = p2;; g) :
isPullback f g p1 p2 H <- limits.pullbacks_as_colimits.isPullback _ f g p1 p2 H.
Proof.
  intro X.
  set (XR := pullbacks_as_colimits.mk_Pullback _ _ _ _ _ _  _ X).
  intros R k h HH.
  mkpair.
  - mkpair.
    use (pullbacks_as_colimits.PullbackArrow _ XR); try assumption.
    split.
    + apply (pullbacks_as_colimits.PullbackArrow_PullbackPr1 _ XR).
    + apply (pullbacks_as_colimits.PullbackArrow_PullbackPr2 _ XR).
  - intro t; apply subtypeEquality.
    { intro. apply isapropdirprod; apply hs. }
    induction t as [x Hx]; simpl in *.
    use (pullbacks_as_colimits.PullbackArrowUnique _ _ _ XR).
    apply R.
    apply (pr1 Hx).
    apply (pr2 Hx).
Defined.

End fix_a_category.