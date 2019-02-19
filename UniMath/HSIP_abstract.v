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
           exact (∑ (ζ : Z1 -> Z2),
                    ( ∏ M : Z2 -> UU, IHn ⟦(D1 (funcomp ζ M)), (D2 M) ⟧)).
      * split; cbn in *.
        -- intros [X F]; cbn.
           exists (idfun _ ).
           intros. exact (identity _ ).
        -- intros [X1 F1] [X2 F2] [X3 F3] [ζ1 f1] [ζ2 f2].
           cbn in *.
           exists (funcomp ζ1 ζ2).
           intro M.
           use ( _ · f2 _ ).
           apply (f1 (funcomp ζ2 M)).
    + repeat split.
      * cbn. intros a b [f fh].
        use total2_paths2_f.
        -- apply idpath.
        -- apply funextsec.
           intro. apply id_left.
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