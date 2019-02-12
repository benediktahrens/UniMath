
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Open Scope cat.

Print precategory_ob_mor.




Notation "'SigLevel'" := precategory (at level 0).

Definition SigSystem : nat -> SigLevel.
Proof.
  induction 1 as [ | n].
  - use mk_precategory.
    + use tpair.
      *  use tpair.
         -- exact UU.
         -- intros X Y. exact (X -> Y).
      * use tpair.
        -- cbn. exact idfun.
        -- cbn. intros X Y Z f g. exact (funcomp f g).
    +  abstract (repeat split).
  -
    (*
    set (obSig := pr1 IHn).
    set (homSig := pr1 (pr2 IHn)).
    set (compSig := pr1 (pr2 (pr2 IHn))).
    set (idSig := pr1 (pr2 (pr2 (pr2 IHn)))).
    set (assocSig := pr1 (pr2 (pr2 (pr2 (pr2 IHn))))).
    set (idrSig := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 IHn)))))).
    set (idlSig := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 IHn)))))).
     *)

    use mk_precategory_one_assoc.
    + use tpair.
      * use tpair.
        -- exact (∑ (Z : UU)
                    (D : (Z -> UU) -> ob IHn),
                  ∏ (M N : Z -> UU), (∏ z, M z -> N z) ->  IHn ⟦(D M), (D N) ⟧).
        -- intros A B.
           set (Z1 := pr1 A).
           set (D1 := pr12 A).
           set (F1 := pr22 A).
           set (Z2 := pr1 B).
           set (D2 := pr12 B).
           set (F2 := pr22 B).
           exact (∑ (ζ : Z1 -> Z2)
                    (δ : ∏ M : Z2 -> UU, IHn ⟦(D1 (funcomp ζ M)), (D2 M) ⟧),
                  ∏ (M N : Z2 -> UU) (α : ∏ z : Z2, M z -> N z),
                  ∥compose (δ M) (F2 M N α) = compose  (F1 _ _ (λ z : Z1, α (ζ z))) (δ N)∥).
      * use tpair.
        -- intro A;
             repeat use tpair ;
             [
               exact (idfun _ )
             |
             intro M; exact (identity _ )
             |
             abstract (
                 intros M N α;
                 apply hinhpr;
                 etrans; [ apply id_left |];
                 apply (!id_right _  )
               )
             ]
           .
        -- intros A B C.
           intros [ζ1 [δ1 φ1]] [ζ2 [δ2 φ2]];
           repeat use tpair;
             [
               exact (funcomp ζ1 ζ2)
             |
               intro M; exact (compose (δ1 _ ) (δ2 _ ))
             |
               abstract (
                   intros M N α;
                   set (phi2 := φ2 _ _ α);
                   use (squash_to_prop phi2);
                   [ apply propproperty |];
                   clear phi2; intro phi2;
                   set (phi1 := φ1 _ _ (λ z : _, α (ζ2 z)));
                   use (squash_to_prop phi1);
                   [ apply propproperty |];
                   clear phi1; intro phi1;
                   apply hinhpr;
                   etrans; [apply (!assoc (C:=IHn) _ _ _ ) |];
                   etrans; [apply maponpaths; apply phi2 |];
                   etrans; [apply (assoc _ _ _  ) |];
                   etrans; [apply maponpaths_2; apply phi1 |];
                   apply (! (assoc _ _ _ ))
                 )
             ]
           .
    + intros; repeat split.
      * abstract (
            intros A B;
            intros [ζ1 [δ1 φ1]];
            use total2_paths2_f;
            [
              apply idpath
            |
            apply subtypeEquality;
            [
              intro x;
              apply impred; intro t;
              apply impred; intro tt;
              apply impred; intro ttt;
              apply propproperty
            |
            cbn;
            apply funextsec;
            intro M;
            apply id_left
            ]
            ]
          ).
      *
        abstract (
            intros A B ;
            intros [ζ1 [δ1 φ1]];
            use total2_paths2_f;
            [
              apply idpath
            |
            abstract (
                apply subtypeEquality;
                [
                  intro x;
                  apply impred; intro t;
                  apply impred; intro tt;
                  apply impred; intro ttt;
                  apply propproperty
          |

          cbn;
          apply funextsec;
          intro M;
          apply id_right
             ]
              )
            ]
          ).
      *
        abstract (
            intros A B C D;
            intros [ζ1 [δ1 φ1]] [ζ2 [δ2 φ2]] [ζ3 [δ3 φ3]];
            use total2_paths2_f;
            [
              apply idpath
            |
            apply subtypeEquality;
           [
             intro x;
              apply impred; intro t;
              apply impred; intro tt;
              apply impred; intro ttt;
              apply propproperty
           |
           cbn;
           apply funextsec;
           intro M;
           apply (assoc _ _ _ )
           ]
        ]
          ).
Defined.

(** Accessor functions *)

Notation "'SIG' n" := (pr1 (SigSystem n)) (at level 2).
Notation "'homSIG' n L1 L2" := (pr1 (pr2 (SigSystem n)) L1 L2) (at level 2).

Definition Struct : ∏ n : nat, SIG n -> UU.
Proof.
  induction n.
  - intro L.
    exact (L -> UU).
  - intro A.
    set (Z := pr1 A).
      [Z [D F]].
    exact (∑ (M : Z -> UU), IHn (D M)).
Defined.

Definition pullbackStruct
  : ∏ (n : nat) (L1 L2 : SIG n) (a : pr1 (pr2 (SigSystem n)) L1 L2),
    Struct _ L2 -> Struct _ L1.
Proof.
  intro n.
  induction n as [| n ].
  - intros L1 L2 a M. exact (funcomp a M).
  - intros L1 L2 a M.
    set (ζ := pr1 a).
    set (M2 := pr1 M).
    exists (funcomp ζ M2).
    set (δ := pr12 a).
    set (δM2 := δ M2).
    use IHn.
    + exact (pr12 L2 M2).
    + exact δM2.
    + exact (pr2 M).
Defined.

Lemma pullbackStruct_1
  : ∏ (n : nat) (L : SIG n) (M : Struct _ L),
    pullbackStruct _ L L (pr1 (pr2 (pr2 (pr2 ( (SigSystem n))))) _ ) M = M.
Proof.
  intro n; induction n as [| n ].
  - intros. apply idpath.
  - intros.
    use total2_paths2_f.
    + apply idpath.
    + apply IHn.
Defined.

Definition homStruct
  : ∏ (n : nat) (L : SIG n) (M1 M2 : Struct _ L), UU.
Proof.
  intro n; induction n as [| n ].
  - intros L M1 M2. exact (∏ l, M1 l -> M2 l).
  - intros L M1 M2.
    use (∑ (μ : ∏ (z : pr1 L), pr1 M1 z -> pr1 M2 z), _).
    use (IHn (pr12 L (pr1 M1))).
    + apply (pr2 M1).
    + use pullbackStruct.
      * apply (pr12 L (pr1 M2)).
Abort.