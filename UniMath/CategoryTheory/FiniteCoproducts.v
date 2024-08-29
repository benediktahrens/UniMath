(** * Functor (pre)categories

Authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman (January 2013)

*)

(** ** Contents

  - Isomorphisms in functor category are pointwise isomorphisms

  - Isomorphic Functors are equal if target precategory is univalent_category
    [functor_eq_from_functor_iso]

  - Functor precategory is univalent_category if target precategory is
    [is_univalent_functor_category]
 *)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Univalence.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Binproducts.
Local Open Scope cat.

Hypothesis joker : forall T : UU, T.


  Definition skeletalfinset : category.
  Proof.
    use makecategory.
    - exact nat.
    - intros m n. exact (stn m -> stn n).
    - intros a b.
      simpl.
      apply Propositions.funspace_isaset.
      apply isasetstn.
    - intro i. exact (λ k, k).
    - intros i j k f g x. exact (g (f x)).
    - intros. apply idpath.
    - intros. apply idpath.
    - intros. apply idpath.
    - intros. apply idpath.
  Defined.

  Definition bincoprod_skeletalfinset (m n : skeletalfinset)
    : BinCoproduct m n.
  Proof.
    unfold BinCoproduct.
    repeat (use tpair).
    - apply (m + n).
    - simpl.
      exact (stn_left _ _).
    - simpl.
      exact (stn_right _ _).
    - simpl.
      unfold isBinCoproduct.
      intros k f g.
      use unique_exists.
      + exact (concatenate' f g).
      + split; simpl.
        * apply funextsec.
          intro i.
          apply stn_eq.
          simpl.
          apply joker.
        * apply joker.
      + intro i.
        apply isapropdirprod; apply homset_property.
      + intro l.
        simpl.
        intros [Hlm Hln].
        apply funextsec.
        intro i.
        apply joker.
  Defined.

  Definition bincoprods_skeletalfinset : BinCoproducts skeletalfinset.
  Proof.
    intros m n.
    apply bincoprod_skeletalfinset.
  Defined.




Section finitestrictcoprod.

  Variable C : category.

  Definition fsc_disp_cat_ob_mor : disp_cat_ob_mor skeletalfinset.
  Proof.
    use tpair.
    - intro n.
      exact (stn n -> C).
    - simpl.
      intros m n x y f.
      exact (∏ i, C⟦ x i, y (f i) ⟧).
  Defined.


  Definition fsc_disp_cat_id_comp : disp_cat_id_comp _ fsc_disp_cat_ob_mor.
  Proof.
    use tpair.
    - intros m x.
      intro i.
      exact (identity _ ).
    - simpl.
      intros k m n f g x y z ff gg.
      intro i.
      apply (@compose C _ _ _ (ff _)).
      exact (gg _).
  Defined.

  Definition fsc_disp_cat_data : disp_cat_data skeletalfinset
    := tpair _ _ fsc_disp_cat_id_comp.


  Lemma fsc_disp_cat_axioms : disp_cat_axioms _ fsc_disp_cat_data.
  Proof.
    apply joker.
  Qed.

  Definition fsc_disp_cat : disp_cat skeletalfinset := tpair _ _ fsc_disp_cat_axioms.

  Definition fsc_bin_coprod
    (m n : skeletalfinset)
    (aa : fsc_disp_cat m)
    (bb : fsc_disp_cat n)
    : disp_BinCoproduct _ aa bb (bincoprod_skeletalfinset m n).
  Proof.
    unfold disp_BinCoproduct.
    repeat (use tpair); simpl.
    - apply (concatenate' aa bb).
    - intro i.
      simpl in aa.
      apply joker.
    - apply joker.
    - apply joker.
  Defined.

  Definition fsc_bin_coprods : disp_BinCoproducts fsc_disp_cat bincoprods_skeletalfinset.
  Proof.
    intros m n aa bb.
    apply fsc_bin_coprod.
  Defined.

  Definition finitecoprodcompletion
    : category
    := total_category fsc_disp_cat.

  Definition BinCoproducts_finitecoprodcompletion
    : BinCoproducts finitecoprodcompletion.
  Proof.
    use total_BinCoproducts.
    - apply bincoprods_skeletalfinset.
    - apply fsc_bin_coprods.
  Defined.



End finitestrictcoprod.
















Section fix_a_category.

  Variable C : category.

  Definition list : UU := ∑ n : nat, stn n -> C.

  Definition n_of (X : list) : nat := pr1 X.
  Definition tuple_of (X : list) : stn (n_of X) → C := pr2 X.

  Definition mor_of_lists (X Y : list) : UU
    := ∑ (f : stn (n_of X) → stn (n_of Y)), ∏ i : stn (n_of X), C⟦ tuple_of X i, tuple_of Y (f i) ⟧.
  Definition map_of {X Y : list} (ϕ : mor_of_lists X Y)
    : stn (n_of X) → stn (n_of Y)
    := pr1 ϕ.
  Definition img_of {X Y : list} (ϕ : mor_of_lists X Y)
    : ∏ i : stn (n_of X), C⟦ tuple_of X i, tuple_of Y (map_of ϕ i) ⟧
    := λ i, pr2 ϕ i.

  Definition comp {X Y Z : list} (ϕ : mor_of_lists X Y) (ξ : mor_of_lists Y Z)
    : mor_of_lists X Z.
  Proof.
    unfold mor_of_lists in *.
    use tpair.
    - exact (λ i, map_of ξ (map_of ϕ i)).
    - intro i.
      use (@compose C).
      + exact (tuple_of Y (map_of ϕ i)).
      + exact (img_of ϕ _ ).
      + simpl. exact (img_of ξ _ ).
  Defined.

  Definition id (X : list) : mor_of_lists X X.
  Proof.
    use tpair.
    - exact (λ i, i).
    - simpl. intro i. exact (identity _).
  Defined.




  Definition finitecoproductcompletion : category.
  Proof.
    use makecategory.
    - exact list.
    - exact mor_of_lists.
    - apply joker.
    - exact id.
    - exact @comp.
    - intros X Y ϕ.
      use total2_paths_f.
      + apply idpath.
      + simpl.
        rewrite idpath_transportf.
        apply funextsec.
        intro i.
        apply id_left.
    - apply joker.
    - apply joker.
    - apply joker.
  Defined.


  Definition initial_obj : finitecoproductcompletion.
  Proof.
    use tpair.
    - exact 0.
    - simpl.
      intro i.
      apply fromempty.
      apply (negstn0 i).
  Defined.

  Definition univ_from_initial (X : list) : finitecoproductcompletion ⟦ initial_obj, X ⟧.
  Proof.
    use tpair.
    - intro i. apply fromempty. apply (negstn0 i).
    - simpl. intro i. apply fromempty. apply (negstn0 i).
  Defined.

  Lemma unique_from_initial (X : list) (f g : finitecoproductcompletion ⟦ initial_obj, X ⟧) : f = g.
  Proof.
    use total2_paths_f.
    - apply funextsec.
      intro i.
      apply fromempty. apply (negstn0 i).
    - apply funextsec. intro i. apply fromempty. apply (negstn0 i).
  Qed.


  Definition embedding_data : functor_data C finitecoproductcompletion.
  Proof.
    use tpair.
    + intro c.
      use tpair.
      * exact 1.
      * simpl. intro i. exact c.
      + simpl.
        intros c c' f.
        use tpair.
        * simpl.
          exact (idfun _).
        * simpl.
          intro i.
          exact f.
  Defined.

  Lemma is_functor_embedding_data : is_functor embedding_data.
  Proof.
    use tpair.
    + unfold functor_idax.
      intro c.
      simpl.
      use total2_paths_f.
      * simpl.
        apply idpath.
      * simpl.
        rewrite idpath_transportf.
        apply idpath.
    + unfold functor_compax.
      intros a b c f g.
      simpl.
      use total2_paths_f.
      * simpl.
        apply idpath.
      * simpl.
        rewrite idpath_transportf.
        apply idpath.
  Qed.

  Definition embedding : functor C finitecoproductcompletion
    := make_functor embedding_data is_functor_embedding_data.


  Section fix_two_objects.

    Variables (X Y : finitecoproductcompletion).


  Definition bincoprod : finitecoproductcompletion.
  Proof.
    use tpair.
    - exact (n_of X + n_of Y).
    - simpl.
      intro i.
      set (i' := weqfromcoprodofstn_invmap (n_of X) (n_of Y) i).
      induction i' as [a | b].
      + apply (tuple_of X a).
      + apply (tuple_of Y b).
  Defined.

  Definition bincoprod_in1 : finitecoproductcompletion⟦ X, bincoprod ⟧.
  Proof.
    use tpair.
    - intro i.
      apply weqfromcoprodofstn_map.
      Search coprod.
      apply ii1.
      apply i.
    - simpl. intro i.
      admit.
  Admitted.

  End fix_two_objects.














End fix_a_category.

Check foo.
