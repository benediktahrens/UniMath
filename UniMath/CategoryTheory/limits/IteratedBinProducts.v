(** A direct definition of iterated binary products by using products *)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.Iter.

Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.


(** Definition of iterated binary products. *)
Section def_IteratedBinProducts.

  Variable C : precategory.

  Definition IteratedBinProducts : UU :=
    forall (n : nat) (a : iter n -> C), ProductCone (iter n) C a.
  Definition hasIteratedBinProducts := ishinh IteratedBinProducts.

End def_IteratedBinProducts.


(** Construction of IteratedBinProducts from Terminal and BinProducts. *)
Section IteratedBinProducts_criteria.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** This result is used in the induction step of the proof of the criteria. It
    says that from any object of C we can construct a product of 1 object from
    it. *)
  Lemma identity_to_product (c : C) :
    ProductCone unit C (termfun c).
  Proof.
    refine (mk_ProductCone _ _ _ c (fun tt : unit => identity _) _).
    refine (mk_isProductCone _ _ hs _ _ _ _).
    intros c0 g.

    use (unique_exists (g tt)); simpl.
    intros i. apply remove_id_right. apply idpath.
    apply maponpaths, isconnectedunit.

    (* Equality on equalities of morphisms *)
    intros y. apply impred_isaprop. intros t. apply hs.

    (* Uniqueness *)
    intros y X. rewrite <- (X tt). apply pathsinv0.
    apply remove_id_right; apply idpath.
  Defined.

  (** In this Theorem we prove that iterated binary products can be constructed
    from Terminal and Products. The result is proved by induction on the number
    of objects in the iterated binary product. *)
  Theorem IteratedBinProducts_from_Terminal_and_Products :
    Terminal C -> BinProducts C -> IteratedBinProducts C.
  Proof.
    intros T BinProds. unfold IteratedBinProducts. intros n. induction n.

    (** Case n = 0 follows from the fact the empty coproducts can be
      constructed from Initial. *)
    unfold iter. intros a. assert (H : a = fromempty) by apply fromemptyeq.
    rewrite H. apply (empty_product_from_terminal _ hs T).

    (** The general case uses the result that from two coproducts, such that the
      binarycoproduct of these exists, we can construct a new coproduct. *)
    intros a.
    set (A1 := IHn (a ∘ (iterincl n))).
    set (A2 := identity_to_product (a(ii2 tt))).
    set (A1pr := ProductPr _ _ A1).
    set (A2pr := ProductPr _ _ A2).
    set (Cone := BinProds (ProductObject (iter n) C A1)
                          (ProductObject unit C A2)).
    set (p1 := BinProductPr1 _ Cone).
    set (p2 := BinProductPr2 _ Cone).
    set (m1 := fun i1 : iter n => p1 ;; (A1pr i1)).
    set (m2 := fun i2 : unit => p2 ;; (A2pr i2)).
    set (ConeOb := BinProductObject _ Cone).
    set (homoteq := @iter_equality _ (S n) _ a (iterincleq _ n a)).

    rewrite <- homoteq.
    apply (product_from_products _ hs _ _ _ _ A1 A2 Cone).
  Defined.
End IteratedBinProducts_criteria.
