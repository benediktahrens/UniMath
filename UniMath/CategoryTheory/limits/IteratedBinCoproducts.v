(** A direct definition of iterated binary coproducts by using coproducts *)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.Iter.

Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.


(** Definition of iterated binary coproduct. *)
Section def_IteratedBinCoproducts.

  Variable C : precategory.

  Definition IteratedBinCoproducts :=
    forall (n : nat) (a : iter n -> C), CoproductCocone (iter n) C a.
  Definition hasIteratedBinCoproducts := ishinh IteratedBinCoproducts.

End def_IteratedBinCoproducts.


(** Construction of IteratedBinCoproducts from Initial and BinCoproducts. *)
Section IteratedBinCoproduct_criteria.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** This result is used in the induction step of the proof of the criteria. It
    says that from any object of C we can construct a coproduct of 1 object from
    it. *)
  Lemma identity_to_coproduct (c : C) :
    CoproductCocone unit C (termfun c).
  Proof.
    refine (mk_CoproductCocone _ _ _ c (fun tt : unit => identity _) _).
    refine (mk_isCoproductCocone _ _ hs _ _ _ _).
    intros c0 g.

    use (unique_exists (g tt)); simpl.
    intros i. apply remove_id_left. apply idpath.
    apply maponpaths, isconnectedunit.

    (* Equality of equalities of morphisms *)
    intros y. apply impred_isaprop. intros t. apply hs.

    (* Uniqueness *)
    intros y X. rewrite <- (X tt). apply pathsinv0.
    apply remove_id_left; apply idpath.
  Defined.

  (** In this Theorem we prove that iterated binary coproducts can be
    constructed from Initial and Coproducts. The result is proved by induction
    on the number of objects in the iterated binary coproduct. *)
  Theorem IteratedBinCoproducts_from_Initial_and_BinCoproducts :
    Initial C -> BinCoproducts C -> IteratedBinCoproducts C.
  Proof.
    intros I Coprods. unfold IteratedBinCoproducts. intros n. induction n.

    (** Case n = 0 follows from the fact the empty coproducts can be
      constructed from Initial. *)
    unfold iter. intros a. assert (H : a = fromempty) by apply fromemptyeq.
    rewrite H. apply (empty_coproduct_from_initial _ hs I).

    (** The general case uses the result that from two coproducts, such that the
      binarycoproduct of these exists, we can construct a new coproduct. *)
    intros a.
    set (A1 := IHn (a ∘ (iterincl n))).
    set (A2 := identity_to_coproduct (a(ii2 tt))).
    set (A1in := CoproductIn _ _ A1).
    set (A2in := CoproductIn _ _ A2).
    set (Cone := Coprods (CoproductObject (iter n) C A1)
                         (CoproductObject unit C A2)).
    set (in1 := BinCoproductIn1 _ Cone).
    set (in2 := BinCoproductIn2 _ Cone).
    set (m1 := fun i1 : iter n => (A1in i1) ;; in1).
    set (m2 := fun i2 : unit => (A2in i2) ;; in2).
    set (ConeOb := BinCoproductObject _ Cone).
    set (homoteq := @iter_equality _ (S n) _ a (iterincleq _ n a)).

    rewrite <- homoteq.
    apply (coproduct_from_coproducts _ hs _ _ _ _ A1 A2 Cone).
  Defined.
End IteratedBinCoproduct_criteria.
