(* Direct implementation of binary products *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.Iter.
Require Import UniMath.CategoryTheory.BinProductPrecategory.
Require Import UniMath.CategoryTheory.limits.products.


Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Section binproduct_def.

Variable C : precategory.

Definition isBinProductCone (c d p: C) (p1 : p --> c) (p2 : p --> d) :=
  forall (a : C) (f : a --> c) (g : a --> d),
    iscontr (total2 (fun fg : a --> p => dirprod (fg ;; p1 = f)
                                                 (fg ;; p2 = g))).

Definition BinProductCone (c d : C) :=
   total2 (fun pp1p2 : total2 (fun p : C => dirprod (p --> c) (p --> d)) =>
             isBinProductCone c d (pr1 pp1p2) (pr1 (pr2 pp1p2)) (pr2 (pr2 pp1p2))).


Definition BinProducts := forall (c d : C), BinProductCone c d.
Definition hasBinProducts := ishinh BinProducts.

Definition BinProductObject {c d : C} (P : BinProductCone c d) : C := pr1 (pr1 P).
Definition BinProductPr1 {c d : C} (P : BinProductCone c d): BinProductObject P --> c :=
  pr1 (pr2 (pr1 P)).
Definition BinProductPr2 {c d : C} (P : BinProductCone c d) : BinProductObject P --> d :=
   pr2 (pr2 (pr1 P)).

Definition isBinProductCone_BinProductCone {c d : C} (P : BinProductCone c d) :
   isBinProductCone c d (BinProductObject P) (BinProductPr1 P) (BinProductPr2 P).
Proof.
  exact (pr2 P).
Defined.

Definition BinProductArrow {c d : C} (P : BinProductCone c d) {a : C} (f : a --> c) (g : a --> d) :
       a --> BinProductObject P.
Proof.
  exact (pr1 (pr1 (isBinProductCone_BinProductCone P _ f g))).
Defined.

Lemma BinProductPr1Commutes (c d : C) (P : BinProductCone c d):
     forall (a : C) (f : a --> c) g, BinProductArrow P f g ;; BinProductPr1 P = f.
Proof.
  intros a f g.
  exact (pr1 (pr2 (pr1 (isBinProductCone_BinProductCone P _ f g)))).
Qed.

Lemma BinProductPr2Commutes (c d : C) (P : BinProductCone c d):
     forall (a : C) (f : a --> c) g, BinProductArrow P f g ;; BinProductPr2 P = g.
Proof.
  intros a f g.
  exact (pr2 (pr2 (pr1 (isBinProductCone_BinProductCone P _ f g)))).
Qed.

Lemma BinProductArrowUnique (c d : C) (P : BinProductCone c d) (x : C)
    (f : x --> c) (g : x --> d) (k : x --> BinProductObject P) :
    k ;; BinProductPr1 P = f -> k ;; BinProductPr2 P = g ->
      k = BinProductArrow P f g.
Proof.
  intros H1 H2.
  set (H := tpair (fun h => dirprod _ _ ) k (dirprodpair H1 H2)).
  set (H' := (pr2 (isBinProductCone_BinProductCone P _ f g)) H).
  apply (base_paths _ _ H').
Qed.


Definition mk_BinProductCone (a b : C) :
  ∀ (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
   isBinProductCone _ _ _ f g -> BinProductCone a b.
Proof.
  intros.
  simple refine (tpair _ _ _ ).
  - exists c.
    exists f.
    exact g.
  - exact X.
Defined.

Definition mk_isBinProductCone (hsC : has_homsets C) (a b p : C)
  (pa : C⟦p,a⟧) (pb : C⟦p,b⟧) :
  (∀ (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
    ∃! k : C⟦c,p⟧, k ;; pa = f × k ;; pb = g) ->
  isBinProductCone a b p pa pb.
Proof.
  intros H c cc g.
  apply H.
Defined.

Lemma BinProductArrowEta (c d : C) (P : BinProductCone c d) (x : C)
    (f : x --> BinProductObject P) :
    f = BinProductArrow P (f ;; BinProductPr1 P) (f ;; BinProductPr2 P).
Proof.
  apply BinProductArrowUnique;
  apply idpath.
Qed.


Definition BinProductOfArrows {c d : C} (Pcd : BinProductCone c d) {a b : C}
    (Pab : BinProductCone a b) (f : a --> c) (g : b --> d) :
          BinProductObject Pab --> BinProductObject Pcd :=
    BinProductArrow Pcd (BinProductPr1 Pab ;; f) (BinProductPr2 Pab ;; g).

Lemma BinProductOfArrowsPr1 {c d : C} (Pcd : BinProductCone c d) {a b : C}
    (Pab : BinProductCone a b) (f : a --> c) (g : b --> d) :
    BinProductOfArrows Pcd Pab f g ;; BinProductPr1 Pcd = BinProductPr1 Pab ;; f.
Proof.
  unfold BinProductOfArrows.
  rewrite BinProductPr1Commutes.
  apply idpath.
Qed.

Lemma BinProductOfArrowsPr2 {c d : C} (Pcd : BinProductCone c d) {a b : C}
    (Pab : BinProductCone a b) (f : a --> c) (g : b --> d) :
    BinProductOfArrows Pcd Pab f g ;; BinProductPr2 Pcd = BinProductPr2 Pab ;; g.
Proof.
  unfold BinProductOfArrows.
  rewrite BinProductPr2Commutes.
  apply idpath.
Qed.


Lemma postcompWithBinProductArrow {c d : C} (Pcd : BinProductCone c d) {a b : C}
    (Pab : BinProductCone a b) (f : a --> c) (g : b --> d)
    {x : C} (k : x --> a) (h : x --> b) :
        BinProductArrow Pab k h ;; BinProductOfArrows Pcd Pab f g =
         BinProductArrow Pcd (k ;; f) (h ;; g).
Proof.
  apply BinProductArrowUnique.
  - rewrite <- assoc, BinProductOfArrowsPr1.
    rewrite assoc, BinProductPr1Commutes.
    apply idpath.
  - rewrite <- assoc, BinProductOfArrowsPr2.
    rewrite assoc, BinProductPr2Commutes.
    apply idpath.
Qed.


Lemma precompWithBinProductArrow {c d : C} (Pcd : BinProductCone c d) {a : C}
    (f : a --> c) (g : a --> d) {x : C} (k : x --> a)  :
       k ;; BinProductArrow Pcd f g  = BinProductArrow Pcd (k ;; f) (k ;; g).
Proof.
  apply BinProductArrowUnique.
  -  rewrite <- assoc, BinProductPr1Commutes;
     apply idpath.
  -  rewrite <- assoc, BinProductPr2Commutes;
     apply idpath.
Qed.

End binproduct_def.


Section BinProducts.

Variable C : precategory.
Variable CC : BinProducts C.
Variables a b c d x y : C.

Definition BinProductOfArrows_comp (f : a --> c) (f' : b --> d) (g : c --> x) (g' : d --> y)
  : BinProductOfArrows _ (CC c d) (CC a b) f f' ;;
    BinProductOfArrows _ (CC _ _) (CC _ _) g g'
    =
    BinProductOfArrows _ (CC _ _) (CC _ _)(f ;; g) (f' ;; g').
Proof.
  apply BinProductArrowUnique.
  - rewrite <- assoc.
    rewrite BinProductOfArrowsPr1.
    rewrite assoc.
    rewrite BinProductOfArrowsPr1.
    apply pathsinv0.
    apply assoc.
  - rewrite <- assoc.
    rewrite BinProductOfArrowsPr2.
    rewrite assoc.
    rewrite BinProductOfArrowsPr2.
    apply pathsinv0.
    apply assoc.
Qed.

Definition BinProductOfArrows_eq (f f' : a --> c) (g g' : b --> d)
  : f = f' → g = g' →
      BinProductOfArrows _ _ _ f g = BinProductOfArrows _ (CC _ _) (CC _ _) f' g'.
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.

End BinProducts.

(** In this section we construct a binproduct from a product and a product from
  a binproduct. *)
Section BinProducts_Products.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** Construction of a binproduct from a product. *)
  Definition binproduct_from_product (a : iter 2 -> C)
             (Cone : ProductCone (iter 2) C a) :
    BinProductCone C (a iter0) (a iter1).
  Proof.
    set (p1 := ProductPr _ _ Cone iter0).
    set (p2 := ProductPr _ _ Cone iter1).
    set (Coneob := (ProductObject _ _ Cone)).

    refine (mk_BinProductCone _ (a iter0) (a iter1) Coneob p1 p2 _).
    refine (mk_isBinProductCone _ hs _ _ _ _ _ _).

    intros c f g.
    set (mors := pair_to_iter2_mors_to _ c a f g).
    set (com1 := ProductPrCommutes _ _ a Cone c mors iter0).
    set (com2 := ProductPrCommutes _ _ a Cone c mors iter1).
    set (ar := (ProductArrow _ _ Cone mors)).

    use (unique_exists ar); simpl.

    (* Commutativity *)
    split.
    apply com1.
    apply com2.

    (* Equality on equality of morphisms *)
    intros y. apply isapropdirprod; apply hs.

    (* Uniqueness *)
    intros y X. apply ProductArrowUnique.
    intros i. induction (iter2_rec i).
    rewrite a0. apply (dirprod_pr1 X).
    rewrite b. apply (dirprod_pr2 X).
  Defined.

  (** Construction of a product from a binproduct. *)
  Definition product_from_binproduct (c1 c2 : C)
             (Cone : BinProductCone C c1 c2) :
    ProductCone (iter 2) C (pair_to_iter2 _ c1 c2).
  Proof.
    set (a := pair_to_iter2 _ c1 c2).
    set (p1 := BinProductPr1 _ Cone).
    set (p2 := BinProductPr2 _ Cone).
    set (ConeOb := BinProductObject _ Cone).
    set (f := pair_to_iter2_mors_to _ ConeOb a p1 p2).

    refine (mk_ProductCone _ _ a ConeOb f _ ).
    refine (mk_isProductCone _ _ hs _ _ _ _).
    intros c g.

    set (f1 := g iter0).
    set (f2 := g iter1).
    set (ar := BinProductArrow _ Cone f1 f2).
    set (com1 := BinProductPr1Commutes _ _ _ Cone _ f1 f2).
    set (com2 := BinProductPr2Commutes _ _ _ Cone _ f1 f2).

    use (unique_exists ar); simpl.

    (* Commutativity *)
    intros i. induction (iter2_rec i).
    rewrite a0. apply com1.
    rewrite b. apply com2.

    (* Equality on morphism equalities *)
    intros y. apply impred_isaprop. intros t0. apply hs.

    (* Uniqueness *)
    intros y X. apply BinProductArrowUnique.
    apply (X iter0).
    apply (X iter1).
  Defined.
End BinProducts_Products.


(** In this section we construct a product from two products by taking the
  disjoint union of the objects. To do this, we need to assume that the
  binproduct of the products exists. *)
Section Product_from_Products.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** Construction of a product from two products and a binproduct of the
    products. *)
  Theorem product_from_products :
    forall (I1 I2 : UU) (a1 : I1 -> C) (a2 : I2 -> C)
      (A1 : ProductCone _ C a1)
      (A2 : ProductCone _ C a2)
      (Cone : BinProductCone C (ProductObject _ _ A1)
                             (ProductObject _ _ A2)),
      ProductCone _ C (sumofmaps a1 a2).
  Proof.
    intros I1 I2 a1 a2 A1 A2 Cone.

    (* Set names from useful terms *)
    set (A1pr := ProductPr _ _ A1).
    set (A2pr := ProductPr _ _ A2).
    set (p1 := BinProductPr1 _ Cone).
    set (p2 := BinProductPr2 _ Cone).
    set (m1 := fun i1 : I1 => p1 ;; (A1pr i1)).
    set (m2 := fun i2 : I2 => p2 ;; (A2pr i2)).
    set (ConeOb := BinProductObject _ Cone).

    refine (mk_ProductCone
              _ _ _ ConeOb (sumofmorsto _ ConeOb _ _ _ _ m1 m2) _).
    refine (mk_isProductCone _ _ hs _ _ _ _).
    intros c g.

    (* Set names for useful terms *)
    set (g1 := fun i : I1 => g (ii1 i)).
    set (g2 := fun i : I2 => g (ii2 i)).
    set (ar1 := ProductArrow _ _ A1 g1).
    set (ar2 := ProductArrow _ _ A2 g2).
    set (ar := BinProductArrow _ Cone ar1 ar2).
    set (com1 := BinProductPr1Commutes _ _ _ Cone c ar1 ar2).
    set (com2 := BinProductPr2Commutes _ _ _ Cone c ar1 ar2).

    use (unique_exists ar); simpl.

    (* Commutativity of morphisms *)
    intros i. unfold sumofmorsto, coprod_rect. induction i.

    set (com'1 := ProductPrCommutes _ _ _ A1 c g1 a).
    unfold ar, m1. rewrite assoc. unfold p1, A1pr. rewrite com1.
    unfold ar1. rewrite -> com'1. apply idpath.

    set (com'2 := ProductPrCommutes _ _ _ A2 c g2 b).
    unfold ar, m2. rewrite assoc. unfold p2, A2pr. rewrite com2.
    unfold ar2. rewrite com'2. apply idpath.

    (* Equality of equality of morphisms *)
    intros y. apply impred_isaprop. intros t0. apply hs.

    (* Uniqueness of the morphism to the cone *)
    intros y X. apply BinProductArrowUnique.
    apply ProductArrowUnique.
    intros i. unfold sumofmorsto, coprod_rect in X.
    set (t2 := X (ii1 i)). simpl in t2.
    fold A1pr. rewrite <- assoc. apply t2.

    apply ProductArrowUnique.
    intros i. unfold sumofmorsto, coprod_rect in X.
    set (t2 := X (ii2 i)). simpl in t2.
    fold A2pr. rewrite <- assoc. apply t2.
  Defined.
End Product_from_Products.


Section BinProduct_unique.

Variable C : precategory.
Variable CC : BinProducts C.
Variables a b : C.

Lemma BinProduct_endo_is_identity (P : BinProductCone _ a b)
  (k : BinProductObject _ P --> BinProductObject _ P)
  (H1 : k ;; BinProductPr1 _ P = BinProductPr1 _ P)
  (H2 : k ;; BinProductPr2 _ P = BinProductPr2 _ P)
  : identity _ = k.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
  apply BinProductArrowEta.
  apply pathsinv0.
  apply BinProductArrowUnique; apply pathsinv0.
  + rewrite id_left. exact H1.
  + rewrite id_left. exact H2.
Qed.

End BinProduct_unique.

(* Section BinProducts_from_Lims. *)

(* Require Import UniMath.CategoryTheory.limits.graphs.colimits. *)
(* Require Import UniMath.CategoryTheory.limits.graphs.limits. *)
(* Require Import UniMath.CategoryTheory.opp_precat. *)
(* Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op"). *)

(* Variable C : precategory. *)
(* Variable hsC : has_homsets C. *)

(* Definition two_graph : graph. *)
(* Proof. *)
(*   exists bool. *)
(*   exact (fun _ _ => empty). *)
(* Defined. *)

(* Definition product_diagram (a b : C) : diagram two_graph C^op. *)
(* Proof. *)
(*   exists (fun x : bool => if x then a else b). *)
(*   intros u v F. *)
(*   induction F. *)
(* Defined. *)

(* Definition ProdCone {a b c : C} (f : c --> a) (g : c --> b) : cone (product_diagram a b) c. *)
(* Proof. *)
(* simple refine (mk_cone _ _); simpl. *)
(*   + intros x; case x; [apply f | apply g]. *)
(*   + abstract (intros x y e; destruct e). *)
(* Defined. *)

(* Lemma BinProducts_from_Lims : Lims C -> BinProducts C. *)
(* Proof. *)
(* intros H a b. *)
(* case (H _ (product_diagram a b)); simpl. *)
(* intros t; destruct t as [ab cc]; simpl; intros iscc. *)
(* apply (mk_BinProductCone _ _ _ ab (coconeIn cc true) (coconeIn cc false)). *)
(* apply (mk_isBinProductCone _ hsC); simpl; intros c f g. *)
(* case (iscc c (ProdCone f g)); simpl; intros t Ht. *)
(* simple refine (tpair _ _ _). *)
(* + apply (tpair _ (pr1 t)); split; [ apply (pr2 t true) | apply (pr2 t false) ]. *)
(* + intros t0. *)
(*   apply subtypeEquality; [intros aa; apply isapropdirprod; apply hsC|]; simpl. *)
(*   simple refine (let X : Σ x : c --> ab, ∀ v, coconeIn cc v ;; x = *)
(*             (if v as b0 return (c --> (if b0 then a else b)) then f else g) := _ in _). *)
(*   { apply (tpair _ (pr1 t0)); intro x; case x; *)
(*     [ apply (pr1 (pr2 t0)) | apply (pr2 (pr2 t0)) ]. } *)
(* apply (maponpaths pr1 (Ht X)). *)
(* Defined. *)

(* End BinProducts_from_Lims. *)

Section test.

Variable C : precategory.
Variable H : BinProducts C.
Arguments BinProductObject [C] c d {_}.
Local Notation "c 'x' d" := (BinProductObject  c d )(at level 5).
(*
Check (fun c d : C => c x d).
*)
End test.

(* The binary product functor: C * C -> C *)
Section binproduct_functor.

Context {C : precategory} (PC : BinProducts C).

Definition binproduct_functor_data :
  functor_data (binproduct_precategory C C) C.
Proof.
mkpair.
- intros p.
  apply (BinProductObject _ (PC (pr1 p) (pr2 p))).
- simpl; intros p q f.
  apply (BinProductOfArrows _ (PC (pr1 q) (pr2 q))
                           (PC (pr1 p) (pr2 p)) (pr1 f) (pr2 f)).
Defined.

Definition binproduct_functor : functor (binproduct_precategory C C) C.
Proof.
apply (tpair _ binproduct_functor_data).
abstract (split;
  [ intro x; simpl; apply pathsinv0, BinProduct_endo_is_identity;
    [ now rewrite BinProductOfArrowsPr1, id_right
    | now rewrite BinProductOfArrowsPr2, id_right ]
  | now intros x y z f g; simpl; rewrite BinProductOfArrows_comp]).
Defined.

End binproduct_functor.

(* Defines the product of two functors by:
    x -> (x,x) -> (F x,G x) -> F x * G x

  For a direct definition see FunctorsPointwiseBinProduct.v

*)
Definition BinProduct_of_functors_alt {C D : precategory} (HD : BinProducts D)
  (F G : functor C D) : functor C D :=
  functor_composite (bindelta_functor C)
     (functor_composite (binproduct_pair_functor F G) (binproduct_functor HD)).
