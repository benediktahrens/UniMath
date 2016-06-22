Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Section def_iter.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** This is stn_alt with different name. *)
  Fixpoint iter (n : nat) := match n with
                           | 0 => empty
                           | S n' => (iter n') ⨿ unit
                           end.
  (** We are going to use iter 2, which corresponds to empty ⨿ unit ⨿ unit.*)
  (** Here are the terms of this type. *)
  Definition iter0 : iter 2 := @ii1 _ unit (@ii2 empty unit tt).
  Definition iter1 :iter 2 := @ii2 (empty ⨿ unit) unit tt.

  (** We use the following for induction. *)
  Definition iter2_rec (x : iter 2) : (x = iter0) ⨿ (x = iter1).
  Proof.
    induction x. induction a.

    (* No empty terms. *)
    apply (fromempty a).

    (* Construction of equalities *)
    assert (H : b = tt) by apply isconnectedunit.
    apply (maponpaths (@ii2 empty unit)) in H.
    apply (maponpaths (@ii1 _ unit)) in H.
    exact (ii1 H).

    assert (H : b = tt) by apply isconnectedunit.
    apply (maponpaths (@ii2 (empty ⨿ unit) unit)) in H.
    exact (ii2 H).
  Defined.

  (** Construct a family of 2 objects from a pair of objects. *)
  Definition pair_to_iter2 (c1 c2 : C) : (iter 2) -> C.
  Proof.
    intros X. induction (iter2_rec X).
    exact c1.
    exact c2.
  Defined.


  (** Construct a family of 2 morphisms with the same target from 2 morphisms
    with the same target. *)
  Definition pair_to_iter2_mors_from (c : C) (a : (iter 2) -> C)
             (f : C⟦a iter0, c⟧) (g : C⟦a iter1, c⟧) : forall i : iter 2, C⟦a i, c⟧.
  Proof.
    intros i. induction (iter2_rec i).
    rewrite <- a0 in f. exact f.
    rewrite <- b in g. exact g.
  Defined.

  (** Construct a family of 2 morphisms with the same domain from 2 morphisms
     with the same domain. *)
  Definition pair_to_iter2_mors_to (c : C) (a : iter 2 -> C) (f : C⟦c, a iter0⟧)
             (g : C⟦c, a iter1⟧) : forall i : iter 2, C⟦c, a i⟧.
  Proof.
    intros i. induction (iter2_rec i).
    rewrite <- a0 in f. exact f.
    rewrite <- b in g. exact g.
  Defined.

  (** Inclusion of iterations. *)
  Definition iterincl (n : nat) : iter n -> iter n ⨿ unit := (fun H : _ => ii1 H).

  (** The following says that to give a morphism iter (S n) -> C is homotopic to
    give a morphism iter n -> C and a morphism unit -> C and then take
    sumofmaps. *)
  Definition iterincleq (n : nat) :
    forall (a : iter n ⨿ unit -> C) (i : iter n ⨿ unit),

      sumofmaps (a ∘ iterincl n) (termfun (a (ii2 tt))) i = a i.
  Proof.
    intros. unfold sumofmaps, iterincl, termfun.
    induction i. apply idpath.
    apply maponpaths, maponpaths.
    apply isconnectedunit.
  Defined.

  (** The following says that homotopic iterations are equal by funextfun.
    Similar to sequenceEquality (FiniteSequences.v). *)
  Definition iter_equality {n : nat} (f g : iter n -> C) :
    (forall (i : iter n), f i = g i) -> f = g.
  Proof.
    intros i. apply funextfun. intros x. exact (i x).
  Defined.


  (** Stuff below this should be moved to somewhere? *)


  (** Sum of two families of morphisms a1 and a2 with a common target. *)
  Definition sumofmorsfrom :
    forall (c : C) (I1 I2 : UU) (a1 : I1 -> C) (a2 : I2 -> C)
      (m1 : forall i1 : I1, C⟦a1 i1, c⟧) (m2 : forall i2 : I2, C⟦a2 i2, c⟧),
    forall i : I1 ⨿ I2, C⟦(sumofmaps a1 a2) i, c⟧.
  Proof.
    intros c I1 I2 a1 a2 m1 m2 i. unfold sumofmaps.
    induction i.
    exact (m1 a).
    exact (m2 b).
  Defined.

  (** Sum of two families of morphisms a1 and a2 with a common domain. *)
  Definition sumofmorsto :
    forall (c : C) (I1 I2 : UU) (a1 : I1 -> C) (a2 : I2 -> C)
      (m1 : forall i1 : I1, C⟦c, a1 i1⟧) (m2 : forall i2 : I2, C⟦c, a2 i2⟧),
    forall i : I1 ⨿ I2, C⟦c, (sumofmaps a1 a2) i⟧.
  Proof.
    intros c I1 I2 a1 a2 m1 m2 i. unfold sumofmaps.
    induction i.
    exact (m1 a).
    exact (m2 b).
  Defined.

  (** Any morphism from empty is equal to fromempty. *)
  Lemma fromemptyeq (X : UU) : forall (f : empty -> X), f = fromempty.
  Proof.
    intros f.
    set (e := iscontrfunfromempty X).
    apply (@pathscomp0  _ _ (pr1 e) _).
    apply ((pr2 e) f).
    apply pathsinv0.
    apply ((pr2 e) fromempty).
  Defined.
End def_iter.