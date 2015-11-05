(************************************************************
      Benedikt Ahrens and Anders Mörtberg, October 2015
*************************************************************)

(** *********************************************************

Contents :

   Definition of chains of endofunctors

   Construction of the initial algebra of the initial chain

*************************************************************)

Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).

Section move_upstream.

(* Move to limits.initial *)

Fixpoint iter_functor {C : precategory} (F : functor C C) (n : nat) : functor C C :=
  match n with
  | O => functor_identity _
  | S n' => functor_composite _ _ _ (iter_functor F n') F
  end.
(*
Proof.
induction n as [|n Fn].
  now apply functor_identity.
now apply (functor_composite _ _ _ Fn F).
Defined.
*)
(* TODO : state this for any object and morphism, that is,
   - Id^n a = a
   - #(Id^n) f = f
   thus avoiding use of funext

  TODO: similar for
   - (G o F)^n (a) = G^n(a) o F^n(a)
   - #(G o F)^n (f) = #G^n(f) o #F^n(f)

*)
Lemma iter_functor_identity (C : precategory) (n : nat) :
  iter_functor (functor_identity C) n = functor_identity C.
Proof. (* THIS IS NOT A USEFUL FORMULATION OF THAT LEMMA *)
Admitted.

Arguments iter_functor : simpl never.

End move_upstream.

(* Local Notation "F ^ n" := (iter_functor _ F n) (at level 10, format "F ^ n"). *)

Section chains.

Variables (C : precategory) (hsC : has_homsets C).

(* Define the chain:

     0 --> 1 --> 2 --> 3 --> ...

   with exactly one arrow from n to S n.
*)
Definition nat_graph : graph :=
  tpair (λ D : UU, D → D → UU) nat (λ m n, S m = n).

(* Alternative definition of chains: *)
(* Definition chain := Σ (f0 : nat -> C), ∀ n, C⟦f0 n,f0 (S n)⟧. *)

(* Definition to_chain : diagram nat_graph C -> chain. *)
(* Proof. *)
(* intro D. *)
(* exists (pr1 D); intro n. *)
(* now apply (pr2 D). *)
(* Defined. *)

(* Definition from_chain : chain -> diagram nat_graph C. *)
(* Proof. *)
(* intro c. *)
(* exists (pr1 c); simpl; intros m n Hmn. *)
(* destruct Hmn. *)
(* now apply (pr2 c). *)
(* Defined. (* Maybe define using idtoiso? *) *)

(* Drop the first element of the diagram *)
Definition shift (d : diagram nat_graph C) : diagram nat_graph C.
Proof.
exists (λ n, pr1 d (S n)); simpl; intros m n Hmn.
destruct Hmn.
now apply (pr2 d).
Defined.

(* Construct a cocone over the shifted diagram *)
Definition shift_cocone {D : diagram nat_graph C}
  {x : C} (cx : cocone D x) : cocone (shift D) x.
Proof.
refine (tpair _ _ _).
- now intro n; apply (coconeIn cx).
- abstract (now intros m n Hmn; destruct Hmn; apply (coconeInCommutes cx)).
Defined.

Lemma shift_cocone_coconeIn (D : diagram nat_graph C) (x : C) (cx : cocone D x) (n : nat):
  coconeIn (shift_cocone cx) n = coconeIn cx (S n).
Proof.
  apply idpath.
Qed.

(* Construct a cocone over the non-shifted diagram *)
Definition unshift_cocone {D : diagram nat_graph C}
  {x : C} (cx : cocone (shift D) x) : cocone D x.
Proof.
refine (mk_cocone _ _).
- intro n.
  now apply (@dmor _ _ _ n _ (idpath _) ;; coconeIn cx n).
- abstract (now intros m n Hmn; destruct Hmn; simpl;
            apply maponpaths, (coconeInCommutes cx _ _ (idpath _))).
Defined.

Lemma unshift_cocone_coconeIn_S (D : diagram nat_graph C) (x : C) (cx : cocone (shift D) x) (n : nat):
  coconeIn (unshift_cocone cx) (S n) = coconeIn cx n.
Proof.
  simpl.
  apply (coconeInCommutes cx _ _ (idpath _ )).
Qed.

Lemma unshift_cocone_coconeIn_O (D : diagram nat_graph C) (x : C) (cx : cocone (shift D) x) :
  coconeIn (unshift_cocone cx) 0 = dmor D (idpath 1) ;; coconeIn cx 0.
Proof.
  apply idpath.
Qed.


Lemma unshift_shift_cocone (D : diagram nat_graph C)
  (x : C) (cx : cocone D x) : unshift_cocone (shift_cocone cx) = cx.
Proof.
apply subtypeEquality; simpl.
- intro. now repeat (apply impred; intro); apply hsC.
- now apply funextsec; intro n; apply (coconeInCommutes cx).
Qed.

Lemma shift_unshift_cocone (D : diagram nat_graph C)
  (x : C) (cx : cocone (shift D) x) : shift_cocone (unshift_cocone cx) = cx.
Proof.
apply subtypeEquality; simpl.
- intro. now repeat (apply impred; intro); apply hsC.
- now apply funextsec; intro n; apply (coconeInCommutes cx _ _ (idpath _)).
Qed.

(* Construct the colimit of the shifted diagram *)
Definition shift_colim (D : diagram nat_graph C) (CC : ColimCocone D) :
  ColimCocone (shift D).
Proof.
apply (mk_ColimCocone _ (colim CC) (shift_cocone (colimCocone CC))).
intros x fx.
refine (tpair _ _ _).
+ exists (colimArrow CC x (unshift_cocone fx)).
  abstract (intro n; simpl;
            eapply pathscomp0;
              [ apply (colimArrowCommutes _ _ (unshift_cocone _))
              | now apply (coconeInCommutes fx _ _ (idpath _)) ]).
+ abstract (simpl; intro f;
            apply subtypeEquality; simpl;
              [ intro; now apply impred; intro; apply hsC | ];
            apply colimArrowUnique; simpl; intro n;
            destruct f as [f Hf]; simpl;
            rewrite <- (Hf n), assoc;
            now apply cancel_postcomposition, pathsinv0, (@colimInCommutes C)).
Defined.

(* Construct the colimit of the unshifted diagram *)
Definition unshift_colim (D : diagram nat_graph C) (CC : ColimCocone (shift D)) :
  ColimCocone D.
Proof.
apply (mk_ColimCocone _ (colim CC) (unshift_cocone (colimCocone CC))).
intros x fx.
refine (tpair _ _ _).
+ exists (colimArrow CC x (shift_cocone fx)).
  abstract (simpl; intro n;
            rewrite <- assoc;
            eapply pathscomp0;
              [ apply maponpaths, (colimArrowCommutes CC x _ n)
              | simpl; now eapply pathscomp0;
                  [|apply (coconeInCommutes fx _ _ (idpath _))]]).
+ abstract (simpl; intro f;
            apply subtypeEquality;
              [ intro; now apply impred; intro; apply hsC|]; simpl;
            apply colimArrowUnique; simpl; intro n;
            destruct f as [f Hf]; simpl;
            rewrite <- Hf;
            apply cancel_postcomposition, pathsinv0;
            now apply (colimInCommutes CC _ _ (idpath _))).
Defined.

Definition colim_shift_iso (D : diagram nat_graph C)
 (CC : ColimCocone D) : iso (colim CC) (colim (shift_colim D CC)).
Proof.
now apply identity_iso.
Defined.

End chains.

Section functor_chain.

Context {C : precategory} (hsC : has_homsets C) (F : functor C C).
Context (c : C) (s : C⟦c,F c⟧).

(* Construct the chain:

         s          Fs            F^2 s
     c -----> F c ------> F^2 c --------> F^3 c ---> ...

*)
Definition Fdiagram : diagram nat_graph C.
Proof.
exists (λ n, iter_functor F n c); simpl; intros m n Hmn.
destruct Hmn; simpl.
induction m; simpl.
- exact s.
- exact (# F IHm).
Defined.

(** Experiment with shift and Fdiagram *)
Definition shift_Fdiagram (x : C) : cocone Fdiagram x -> cocone (shift C Fdiagram) (F x).
Proof.
  intro cx.
  refine (mk_cocone _ _).
  - simpl.
    intro n.
    exact (#F (coconeIn cx n)).
  - abstract (intros u v e;
               destruct e ; simpl;
               rewrite <- functor_comp;
               apply maponpaths;
               apply (coconeInCommutes cx _ _ (idpath _ ))).
(*
    destruct n.
    + exact (# F (coconeIn H 0)).
    + exact (# F (coconeIn H (S n))).

  - simpl; intros m n e; destruct e.
    destruct m; simpl.
    + rewrite <- functor_comp.
      apply maponpaths, (pr2 H 0 1 (idpath _)). (* remove pr2 ... *)
    + rewrite <- functor_comp.
      apply maponpaths, (pr2 H (S m) (S (S m)) (idpath _)). (* remove pr2 *)
*)
Defined.

Lemma shift_Fdiagram_coconeIn (x : C) (cx : cocone Fdiagram x) (n : nat) :
  coconeIn (shift_Fdiagram x cx) n = #F (coconeIn cx n).
Proof.
  apply idpath.
Qed.

Definition Fcocone {x : C} (cx : cocone Fdiagram x) : cocone Fdiagram (F x).
Proof.
  apply unshift_cocone.
  apply shift_Fdiagram.
  apply cx.
Defined.

Lemma Fcocone_coconeIn_S (x : C) (cx : cocone Fdiagram x) n :
  coconeIn (Fcocone cx) (S n) = #F (coconeIn cx n ).
Proof.
  unfold Fcocone.
  rewrite unshift_cocone_coconeIn_S.
  apply shift_Fdiagram_coconeIn.
Qed.
(*
Lemma Fcocone_coconeIn_O (x : C) (cx : cocone Fdiagram x) :
  coconeIn (Fcocone cx) 0 = #F (dmor Fdiagram  (idpath _) ;; coconeIn cx _). #F (dmor Fdiagram (idpath _) ;;  (coconeIn cx 1)).
Proof.
  unfold Fcocone.
  rewrite unshift_cocone_coconeIn_S.
  apply shift_Fdiagram_coconeIn.
Qed.
*)

Variables (CC : ColimCocone Fdiagram).

Local Notation L := (colim CC).
Local Notation LF := (colim (shift_colim C hsC Fdiagram CC)).

(*
Definition Fcocone : cocone Fdiagram (F L).
Proof.
refine (mk_cocone _ _).
- intro n.
  destruct n; simpl.
  + exact (s ;; # F (colimIn CC 0)).
  + exact (# F (colimIn CC n)).
- abstract (simpl; intros m n Hmn; destruct Hmn; simpl; destruct m; simpl;
            [apply idpath|]; simpl; rewrite <- functor_comp; apply maponpaths;
            apply (colimInCommutes CC _ _ (idpath _))).
Defined.
*)

(* this is m^-1 : L -> FL in TACL slides page 9 *)
Definition from_colim_shift : C⟦LF,F L⟧ := colimArrow _ _ (Fcocone (colimCocone CC)).

(* This uses that LF and L are convertible *)
Definition from_colim : C⟦L,F L⟧ := from_colim_shift.

Definition chain_cocontinuous : UU := is_iso from_colim_shift.

(* This could also be defined as: *)
(* Definition chain_cocontinuous : UU := is_iso from_colim. *)

Variable Hcc : chain_cocontinuous.
Let minv : iso L (F L) := isopair _ Hcc.
Let m : C⟦F L,L⟧ := inv_from_iso minv.

Lemma mCommutes (n : nat) : coconeIn (colimCocone CC) n = coconeIn (Fcocone (colimCocone CC))  n ;; m.
Proof.
now apply iso_inv_on_left, pathsinv0, (colimArrowCommutes _ _ (Fcocone _ )).
Qed.

Lemma minvCommutes (n : nat) : coconeIn (colimCocone CC) n ;; minv = coconeIn (Fcocone (colimCocone CC))  n.
Proof.
now apply (colimArrowCommutes _ _ (Fcocone _ )).
Qed.

End functor_chain.

(* Proves that (L,m : F L -> L) is the initial algebra where L is the
   colimit of the inital chain:

         !          F !           F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...

*)
Section colim_initial_algebra.

Variables (C : precategory) (F : functor C C).
Variables (hsC : has_homsets C) (Init : Initial C).

Definition initDiag : diagram nat_graph C :=
  Fdiagram F (InitialObject Init) (InitialArrow Init (F (InitialObject Init))).

Variable (CC : ColimCocone initDiag).
Variable (Fcont : chain_cocontinuous hsC F (InitialObject Init) (InitialArrow Init _) CC).

Local Notation L := (colim CC).
Local Notation minv := (isopair _ Fcont).

Local Definition m : C⟦F L,L⟧ := inv_from_iso minv.
Local Definition colimAlg : algebra_ob F := tpair (λ X : C, C ⟦ F X, X ⟧) L m.

Section algebra.

Variable (Aa : algebra_ob F).

Local Notation A := (alg_carrier _ Aa).
Local Notation a := (alg_map _ Aa).

Definition cocone_over_alg (n : nat) : C ⟦ dob initDiag n, A ⟧.
Proof.
induction n as [|n Fn]; simpl.
- now apply InitialArrow.
- now apply (# F Fn ;; a).
Defined.

(* a_n : F^n 0 -> A *)
Local Notation an := cocone_over_alg.

(* This makes Coq not unfold dmor during simpl *)
Arguments dmor : simpl never.

Lemma isCoconeOverAlg n Sn (e : edge n Sn) : dmor initDiag e ;; an Sn = an n.
Proof.
destruct e.
induction n as [|n IHn].
- now apply InitialArrowUnique.
- simpl; rewrite assoc.
  apply cancel_postcomposition, pathsinv0.
  eapply pathscomp0; [|simpl; apply functor_comp].
  now apply maponpaths, pathsinv0, IHn.
Qed.

(* ad = a† = a dagger *)
Local Definition ad : C⟦L,A⟧.
Proof.
apply colimArrow.
refine (mk_cocone _ _).
- apply cocone_over_alg.
- apply isCoconeOverAlg.
Defined.

Lemma adaggerCommutes (n : nat) : colimIn CC n ;; ad = an n.
Proof.
now apply colimArrowCommutes.
Qed.

Lemma adaggerCommutes2 (n : nat) : colimIn CC n ;; minv ;; # F ad ;; a = an n.
Proof.
induction n as [|n IHn].
- now apply InitialArrowUnique.
- rewrite <- assoc.
  eapply pathscomp0;
    [ eapply cancel_postcomposition; apply (minvCommutes hsC F _ _ CC Fcont (S n))|].
  rewrite assoc.
  rewrite Fcocone_coconeIn_S. simpl. rewrite <- (functor_comp F).
  now apply cancel_postcomposition, maponpaths, adaggerCommutes.
Qed.

Lemma adaggerDef : ad = minv ;; #F ad ;; a.
Proof.
apply pathsinv0, colimArrowUnique; simpl; intro n.
rewrite !assoc.
now apply adaggerCommutes2.
Qed.

Lemma ad_is_algebra_mor : is_algebra_mor _ colimAlg Aa ad.
Proof.
unfold is_algebra_mor; simpl; unfold colimAlg.
apply iso_inv_on_right.
rewrite assoc.
now apply adaggerDef.
Qed.

Definition adaggerMor : algebra_mor F colimAlg Aa := tpair _ _ ad_is_algebra_mor.

End algebra.

Lemma colimAlgIsInitial : isInitial (precategory_FunctorAlg F hsC) colimAlg.
Proof.
refine (mk_isInitial _ _).
intros Aa.
exists (adaggerMor Aa); simpl; intro Fa.
apply (algebra_mor_eq _ hsC); simpl.
unfold ad.
apply colimArrowUnique; simpl; intro n.
destruct Fa as [f hf]; simpl.
unfold is_algebra_mor in hf.
simpl in hf.
induction n as [|n IHn]; simpl.
- now apply InitialArrowUnique.
- rewrite <- IHn, functor_comp, <- assoc.
  eapply pathscomp0; [| eapply maponpaths; apply hf].
  rewrite assoc.
  apply cancel_postcomposition.
  assert (T:= mCommutes hsC _ _ _ CC Fcont (S n)).
  unfold colimIn.
  eapply pathscomp0. apply T.
  apply cancel_postcomposition.
  apply Fcocone_coconeIn_S.
Qed.

Definition colimAlgInitial : Initial (precategory_FunctorAlg F hsC) :=
  mk_Initial _ colimAlgIsInitial.

End colim_initial_algebra.

About Fcocone.
Check unshift_cocone.
(* WIP below of here *)
Section lists.

(* TODO: Move *)
Require Import UniMath.SubstitutionSystems.Auxiliary.
Require Import UniMath.SubstitutionSystems.FunctorsPointwiseProduct.
Require Import UniMath.SubstitutionSystems.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Variable A : HSET.

(* *)
(* F(X) = A * X *)
(* *)
Definition streamFunctor : functor HSET HSET :=
  product_functor HSET HSET ProductsHSET
                  (constant_functor HSET HSET A)
                  (functor_identity HSET).


(* Definition unitHSET : HSET. *)
(* Proof. *)
(* exists unit. *)
(* apply isasetaprop. *)
(* apply isapropifcontr. *)
(* apply iscontrunit. *)
(* Defined. *)

(* F(X) = 1 + (A * X) *)
Definition listFunctor : functor HSET HSET :=
  coproduct_functor HSET HSET CoproductsHSET
                    (constant_functor HSET HSET (TerminalObject TerminalHSET))
                    streamFunctor.

(* Let ColimCoconeF F := ColimCocone *)
(*          (Fdiagram F (InitialObject InitialHSET) *)
(*             (InitialArrow InitialHSET (F (InitialObject InitialHSET)))). *)

(* Definition temp : ColimCoconeF listFunctor := ColimCoconeHSET _ _. *)


Let good F := chain_cocontinuous has_homsets_HSET F
    (InitialObject InitialHSET) (InitialArrow InitialHSET _) (ColimCoconeHSET _ _).
(* TODO: *)
(* good(F), good(G) |- good(F * G) *)
(* good(F), good(G) |- good(F + G) *)
(*                  |- good(constant_functor A) *)
(*                  |- good(identity_functor) *)

Lemma goodIdentity : good (functor_identity _).
Proof.
  unfold good, chain_cocontinuous.
  unfold from_colim_shift.
  set (X1 := ColimCoconeHSET _ _).
  set (X3 := Fcocone _ _ _ _).
  apply (isColim_is_iso _ X1).
  intros a ca.
  refine (tpair _ _ _).
  - refine (tpair _ _ _).
    + apply colimArrow.
      apply ca.
    + intro n; induction n.
      * unfold X3.
        unfold Fcocone.
        rewrite unshift_cocone_coconeIn_O.
        simpl.
        assert (T:= ArrowsFromInitial InitialHSET).
        match goal with [T : _ |- ?e = ?f ] =>
                        assert (T':= T _ e f) end.
        apply T'.
      * unfold X3.
        rewrite Fcocone_coconeIn_S.
        simpl.
        assert (H:=colimArrowCommutes X1 a ca ).
        eapply pathscomp0.
        apply H.
        assert (T:= coconeInCommutes ca n (S n) (idpath _ )).
        simpl in T.
        (* NOW USE HYPOTHESIS T, EXCEPT THAT THERE IS AN IDENTITY
           MORPHISM *)
        match goal with [|- ?e = ?f ] =>
                        set (E:=e); set (F:=f) end.
        simpl in E,F.
        (* now use lemma that says that
             iter_functor (Id) (a) = a
             here a is initial object
           then use lemma ArrowsFromInitial, that is,
           both E and F start in initial object, hence E = F
        *)
Admitted.

Lemma goodConstant (B : HSET) : good (constant_functor _ _ B).
Admitted.

Lemma goodProduct (F G : functor HSET HSET) :
  good F -> good G -> good (product_functor _ _ ProductsHSET F G).
Admitted.

Lemma goodCoproduct (F G : functor HSET HSET) :
  good F -> good G -> good (coproduct_functor _ _ CoproductsHSET F G).
Admitted.

Lemma listFunctor_chain_cocontinuous : good listFunctor.
Proof.
unfold listFunctor, streamFunctor.
apply goodCoproduct; [ apply goodConstant |].
apply goodProduct; [ apply goodConstant | apply goodIdentity].
Defined.

Lemma listFunctor_Initial :
  Initial (precategory_FunctorAlg listFunctor has_homsets_HSET).
Proof.
refine (colimAlgInitial _ _ _ _ _ _).
- apply InitialHSET.
- apply ColimCoconeHSET.
- apply listFunctor_chain_cocontinuous.
Defined.

(* Get recursion/iteration scheme: *)

(*    x : X           f : A × X -> X *)
(* ------------------------------------ *)
(*       iter x f : List A -> X *)

(* Get induction as well? *)

End lists.
