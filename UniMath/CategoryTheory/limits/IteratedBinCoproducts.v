(** A direct definition of finite ordered coproducts by using coproducts *)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ProductPrecategory.

Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.


(** Definition of finite ordered coproducts. *)
Section def_FinOrdCoproducts.

  Variable C : precategory.

  Definition FinOrdCoproducts : UU :=
    forall (n : nat) (a : stn n -> C), CoproductCocone (stn n) C a.
  Definition hasFinOrdCoproducts := ishinh FinOrdCoproducts.

End def_FinOrdCoproducts.


(** Construction of FinOrdCoproducts from Initial and BinCoproducts. *)
Section FinOrdCoproduct_criteria.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Lemma stn1isconnected : forall i : stn 1, invweq(weqstn1tounit) tt = i.
  Proof.
    intros i.
    apply (invmaponpathsweq weqstn1tounit).
    apply isconnectedunit.
  Defined.

  (** Case n = 1. *)
  Lemma identity_to_coproduct:
    forall (a : stn 1 -> C), CoproductCocone (stn 1) C a.
  Proof.
    intros a.
    set (stn1ob := invweq(weqstn1tounit) tt).

    use (mk_CoproductCocone _ _ _ (a stn1ob)).
    intros i. exact (idtoiso (! (maponpaths a (stn1isconnected i)))).

    use (mk_isCoproductCocone _ _ hs).
    intros c g.
    use (unique_exists).
    exact (g stn1ob).

    (* Commutativity. *)
    intros i. rewrite <- (stn1isconnected i). apply id_left.

    (* Equality of equalities of morphisms. *)
    intros y. apply impred_isaprop. intros t. apply hs.

    (* Uniqueness. *)
    intros y X. rewrite <- (X stn1ob). apply pathsinv0. apply id_left.
  Defined.

  Lemma stnneq : forall (n : nat) (i : stn (S n)) (a0 : pr1 i < n),
      i = dni_lastelement (stnpair n (pr1 i) a0).
  Proof.
    intros n i a0.
    apply isinjstntonat.
    apply idpath.
  Defined.

  Lemma stneq1 : forall (n : nat) (i : stn (S n)) (a0 : pr1 i = n),
      i = lastelement n.
  Proof.
    intros n i a0.
    unfold lastelement.
    apply isinjstntonat.
    apply a0.
  Defined.

  Theorem FinOrdCoproducts_from_Initial_and_BinCoproducts :
    Initial C -> BinCoproducts C -> FinOrdCoproducts C.
  Proof.
    intros I Coprods. unfold FinOrdCoproducts. intros n. induction n.

    (** Case n = 0 follows from the fact that empty coproducts can be
      constructed from Initial. *)
    intros a.
    use (mk_CoproductCocone _ _ _ I (fun i : stn 0 => fromempty (weqstn0toempty i))).
    use (mk_isCoproductCocone _ _ hs).
    intros c g. use unique_exists; cbn.

    apply (InitialArrow I c).
    intros i. apply (fromempty (weqstn0toempty i)).
    intros y. apply impred_isaprop. intros t. apply hs.
    intros y. intros X. apply InitialArrowUnique.

    (** General case. *)
    intros a.
    set (a1 := fun (i : stn n) => a (dni_lastelement i)).
    set (A1 := IHn a1).
    set (a2 := (fun _ : stn 1 => a (lastelement n))).
    set (A2 := identity_to_coproduct a2).
    set (A1in := CoproductIn _ _ A1).
    set (A2in := CoproductIn _ _ A2).
    set (Cone := Coprods (CoproductObject (stn n) C A1)
                         (CoproductObject (stn 1) C A2)).
    set (in1 := BinCoproductIn1 _ Cone).
    set (in2 := BinCoproductIn2 _ Cone).
    set (m1 := fun i1 : stn n => (A1in i1) ;; in1).
    set (m2 := fun i2 : stn 1 => (A2in i2) ;; in2).
    set (ConeOb := BinCoproductObject _ Cone).
    fold ConeOb in in1, in2, m1, m2.

    use (mk_CoproductCocone (stn (S n)) C a ConeOb _).

    (* Construction of the arrows from a i to ConeOb *)
    intros i. induction (natlehchoice4 (pr1 i) _ (pr2 i)).
    exact (idtoiso (maponpaths a (stnneq n i a0)) ;; m1 (stnpair n (pr1 i) a0)).
    exact (idtoiso (maponpaths a (stneq1 n i b))
                   ;;  m2 (invweq(weqstn1tounit) tt)).

    (* Construction of isCoproductCocone. *)
    use (mk_isCoproductCocone _ _ hs).
    intros c g.

    set (g1 := fun i : stn n => g(dni_lastelement i)).
    set (ar1 := CoproductArrow _ _ A1 g1). fold ar1.
    set (com1 := BinCoproductIn1Commutes  _ _ _ Cone c ar1 (g(lastelement n))).
    set (com2 := BinCoproductIn2Commutes _ _ _ Cone c ar1 (g(lastelement n))).
    set (com3 := CoproductInCommutes _ _ _ A1 _ g1).
    set (com4 := CoproductInCommutes _ _ _ A2 _ (fun _ : stn 1 => g(lastelement n))).

    use (unique_exists).

    (* Construction of the unique arrow from ConeOb to c. *)
    use (BinCoproductArrow _ Cone).
    use (CoproductArrow _ _ A1). intros i. exact (g(dni_lastelement i)).
    use (CoproductArrow _ _ A2). intros i. exact (g (lastelement n)).

    (* First commutativity. *)
    intros i. unfold coprod_rect. induction (natlehchoice4 (pr1 i) n (pr2 i)).
    rewrite (stnneq n i a0). cbn. repeat rewrite <- assoc. apply remove_id_left.
    apply idpath.

    unfold m1. unfold in1. rewrite <- assoc. fold g1. fold ar1.
    set (XX := maponpaths (fun f : _ => A1in (stnpair n (pr1 i) a0) ;; f) com1).
    cbn in XX.
    eapply pathscomp0. apply XX.
    fold ar1 in com3.
    rewrite com3.
    unfold g1.
    apply idpath.


    (* Second commutativity. *)
    rewrite (stneq1 n i b). cbn. repeat rewrite <- assoc. apply remove_id_left.
    apply idpath.

    unfold m2. unfold in2. rewrite <- assoc. fold g1. fold ar1.
    set (XX := maponpaths (fun f : _ => A2in (lastelement 0) ;; f) com2).
    eapply pathscomp0. apply XX.
    rewrite com4.
    apply idpath.


    (* Equality on equalities of morphisms. *)
    intros y. apply impred_isaprop. intros t. apply hs.

    (* Uniqueness *)
    unfold coprod_rect. intros k X.
    apply BinCoproductArrowUnique. apply CoproductArrowUnique.

    intros i.

    rewrite <- (X (dni_lastelement i)). rewrite assoc.
    apply cancel_postcomposition.
    destruct (natlehchoice4 (pr1 (dni_lastelement i)) n (pr2 (dni_lastelement i))).
    unfold m1. rewrite assoc. unfold in1.
    apply cancel_postcomposition.
    unfold A1in.
    apply pathsinv0.

    (* Can't do more than this. *)
  Abort.
End FinOrdCoproduct_criteria.
