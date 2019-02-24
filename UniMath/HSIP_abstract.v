Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.categories.Types.

Open Scope cat.

Definition fam_precat_data (X : UU) : precategory_data.
Proof.
  use tpair.
  - use tpair.
    + exact (X -> UU).
    + intros L1 L2.
      exact (∏ x, L1 x -> L2 x).
  - use tpair.
    + intros. exact (λ _ , idfun _ ).
    + cbn. intros L1 L2 L3 f g.
      exact (λ x, funcomp (f x) (g x)).
Defined.

Definition is_precategory_fam_precat_data (X : UU) : is_precategory (fam_precat_data X).
Proof.
  repeat split.
Qed.

Definition fam_precat (X : UU) : precategory
  := _ ,, is_precategory_fam_precat_data X.


Definition fam_functor_data {X Y : UU} (f : X -> Y)
  : functor_data (fam_precat_data Y) (fam_precat_data X).
Proof.
  use tpair.
  - cbn. intros r x. exact (r (f x)).
  - cbn. intros r s α x. exact (α (f x)).
Defined.

Lemma is_functor_fam_functor_data {X Y : UU} (f : X -> Y)
  : is_functor (fam_functor_data f).
Proof.
  split; [ intro a | intros a b c r s]; apply idpath.
Qed.

Definition fam_functor {X Y : UU} (f : X -> Y)
  : functor (fam_precat Y) (fam_precat X)
  := _ ,, is_functor_fam_functor_data f.

(*
Definition catcat_data (D : precategory_data) : precategory_data.
Proof.
  use tpair.
  - use tpair.
    + exact (∑ X : UU, functor (fam_precat X) D).
    + cbn. intros X1 X2. cbn in X1 , X2.
      exact (∑ ζ : pr1 X1 -> pr1 X2,
                   ∏ x : X1, C⟦ pr2 X2 (ζ x)
*)


Definition Signature (n : nat) : precategory.
Proof.
  induction n.
  - exact type_precat.
  - use mk_precategory_one_assoc.
    + use tpair.
      * use tpair.
        -- exact (∑ X : UU, functor (fam_precat X) IHn).
        -- cbn. intros A B.
           set (Z1 := pr1 A).
           set (D1 := pr2 A).
           set (Z2 := pr1 B).
           set (D2 := pr2 B).
           cbn in *.
           exact (∑ (ζ : Z1 -> Z2),
                  nat_trans (functor_composite (fam_functor ζ) D1) D2).
      * split; cbn in *.
        -- intros [X F]; cbn.
           exists (idfun _ ).
           intros. exact (nat_trans_id _ ).
        -- intros [X1 F1] [X2 F2] [X3 F3] [ζ1 f1] [ζ2 f2].
           cbn in *.
           exists (funcomp ζ1 ζ2).
           use (nat_trans_comp _ _ _ _ f2).
           use mk_nat_trans.
           ++ intro M.
              apply (f1 (funcomp ζ2 M)).
           ++ cbn. intros a b f. cbn.
              set (XX:= nat_trans_ax f1).
              cbn in XX.
              set (YY:= nat_trans_ax f2).
              cbn in YY.
              apply (XX _ _ (λ x : X2, f (ζ2 x))).
    + repeat split.
      * cbn. intros a b [f fh].
        use total2_paths2_f.
        -- apply idpath.
        -- use total2_paths2_f.
           cbn.
           apply funextsec.
           intro. apply id_left.
           cbn.
           Search (transportf _ _ _ = _ ).
           set (X:= @transportf_funextfun).

           etrans. apply transportf_funextfun.
      * cbn. intros a b [f fh].
        use total2_paths2_f.
        -- apply idpath.
        -- apply funextsec.
           intro. apply id_right.
      * cbn. intros a b c d.
        intros f g h.
        use total2_paths2_f.
        -- apply idpath.
        -- apply funextsec.
           intro. cbn. unfold idfun.
           apply assoc.
Defined.


  match n with
  | 0 => type_precat
  | S m => ∑ (X : UU), functor (fam_precat X) (Signature m)
  end.