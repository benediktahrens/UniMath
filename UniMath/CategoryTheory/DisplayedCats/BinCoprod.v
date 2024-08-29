Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.

Local Open Scope cat.
Local Open Scope mor_disp.

Section foo.

  Variable C : category.
  Variable CP : BinCoproducts C.
  Print BinCoproduct.
  Print isBinCoproduct.

  Variable D : disp_cat C.

  Definition disp_isBinCoproduct
    (a b : C)
(*    (co : C) *)
(*    (ia : C ⟦ a, co ⟧) (ib : C ⟦ b, co ⟧) *)
    (H : BinCoproduct a b)
    (aa : D a)
    (bb : D b)
    (cco : D H)
    (iaa : aa -->[BinCoproductIn1 H] cco)
    (ibb : bb -->[BinCoproductIn2 H] cco)
    : UU
    :=
    ∏ (c : C)
      (cc : D c)
      (f : a --> c)
      (g : b --> c)
      (ff : aa -->[f] cc)
      (gg : bb -->[g] cc),
      ∃! uu : cco -->[BinCoproductArrow H f g] cc,
        (iaa ;; uu = transportb (mor_disp aa cc) (BinCoproductIn1Commutes C a b H c f g) ff)
          ×
         (ibb ;; uu = transportb (mor_disp bb cc) (BinCoproductIn2Commutes C a b H c f g) gg).



  Definition disp_BinCoproduct
    {a b : C}
    (H : BinCoproduct a b)
    (aa : D a)
    (bb : D b)
    : UU
    := ∑ ccoiaaibb : (∑ cco : D H, aa -->[BinCoproductIn1 H] cco × bb -->[BinCoproductIn2 H] cco),
      disp_isBinCoproduct _ _ H aa bb (pr1 ccoiaaibb) (pr1 (pr2 ccoiaaibb)) (pr2 (pr2 ccoiaaibb)).

  Coercion disp_BinCoproductOb
    {a b : C}
    (H : BinCoproduct a b)
    (aa : D a)
    (bb : D b)
    (HH : disp_BinCoproduct H aa bb)
      :
      D H
      := pr1 (pr1 HH).

    Definition disp_BinCoproductIn1
    {a b : C}
    (H : BinCoproduct a b)
    (aa : D a)
    (bb : D b)
    (HH : disp_BinCoproduct H aa bb)
      :
      aa -->[BinCoproductIn1 H] (disp_BinCoproductOb H aa bb HH)
      := pr1 (pr2 (pr1 HH)).

    Definition disp_BinCoproductIn2
    {a b : C}
    (H : BinCoproduct a b)
    (aa : D a)
    (bb : D b)
    (HH : disp_BinCoproduct H aa bb)
      :
      bb -->[BinCoproductIn2 H] (disp_BinCoproductOb H aa bb HH)
        := pr2 (pr2 (pr1 HH)).


    Definition disp_BinCoproductArrow
      {a b : C}
      (H : BinCoproduct a b)
      (aa : D a)
      (bb : D b)
      (HH : disp_BinCoproduct H aa bb)
      {c : C}
      {cc : D c}
      {f : a --> c}
      {g : b --> c}
      (ff : aa -->[f] cc)
      (gg : bb -->[g] cc)
      :
      disp_BinCoproductOb H aa bb HH -->[BinCoproductArrow H f g] cc
      := pr1 (pr1 (pr2 HH c cc f g ff gg)).


    Definition disp_BinCoproductIn1Commutes
      {a b : C}
      (H : BinCoproduct a b)
      (aa : D a)
      (bb : D b)
      (HH : disp_BinCoproduct H aa bb)
      {c : C}
      {cc : D c}
      {f : a --> c}
      {g : b --> c}
      (ff : aa -->[f] cc)
      (gg : bb -->[g] cc)
      :
      disp_BinCoproductIn1 H aa bb HH ;; disp_BinCoproductArrow H aa bb HH ff gg
      =
        transportb (mor_disp aa cc) (BinCoproductIn1Commutes C a b H c f g) ff
      := pr1 (pr2 (pr1 (pr2 HH c cc f g ff gg))).

    Definition disp_BinCoproductIn2Commutes
      {a b : C}
      (H : BinCoproduct a b)
      (aa : D a)
      (bb : D b)
      (HH : disp_BinCoproduct H aa bb)
      {c : C}
      {cc : D c}
      {f : a --> c}
      {g : b --> c}
      (ff : aa -->[f] cc)
      (gg : bb -->[g] cc)
      :
      disp_BinCoproductIn2 H aa bb HH ;; disp_BinCoproductArrow H aa bb HH ff gg
      =
        transportb (mor_disp bb cc) (BinCoproductIn2Commutes C a b H c f g) gg
      := pr2 (pr2 (pr1 (pr2 HH c cc f g ff gg))).

    Lemma disp_BinCoproductArrowUnique
      (a b : C)
      (H : BinCoproduct a b)
      (aa : D a)
      (bb : D b)
      (HH : disp_BinCoproduct H aa bb)
      {c : C}
      {cc : D c}
      {f : a --> c}
      {g : b --> c}
      (ff : aa -->[f] cc)
      (gg : bb -->[g] cc)
      (k : BinCoproductObject H --> c)
      (Hk1 : BinCoproductIn1 H · k = f)
      (Hk2 : BinCoproductIn2 H · k = g)
      (kk : disp_BinCoproductOb H aa bb HH -->[k] cc)
      (Hkk1 : disp_BinCoproductIn1 H _ _ HH ;; kk = transportb _ Hk1 ff)
      (Hkk2 : disp_BinCoproductIn2 H _ _ HH ;; kk = transportb _ Hk2 gg)
      :
      kk = transportb
             _
             (BinCoproductArrowUnique C _ _ H _ f g _ Hk1 Hk2)
             (disp_BinCoproductArrow H _ _ HH ff gg).
    Proof.
      set (T := pr2 HH). simpl in T.
      unfold disp_isBinCoproduct in T.
      specialize (T c cc f g ff gg).
      Search "center".
      Search (∃! _ , _).


      apply transportb_transpose_right.
      apply path_to_ctr.
      split.
      - apply transportb_transpose_right.
        set (Hkk1':= transportb_transpose_left Hkk1).
        rewrite <- Hkk1'.
        etrans.
        { apply maponpaths.
          Search ( _ ;; transportf _ _ _ = _ ).
          apply mor_disp_transportf_prewhisker. }
        etrans.
        {
          Search (transportf _ _ (transportf _ _ _ ) = _).
          apply transport_f_f. }
        unfold transportb.
        Search (transportf _ _ _ = transportf _ _ _ ).
        apply transportf_paths.
        apply homset_property.
      - apply transportb_transpose_right.
        set (Hkk2':= transportb_transpose_left Hkk2).
        rewrite <- Hkk2'.
        etrans.
        { apply maponpaths.
          Search ( _ ;; transportf _ _ _ = _ ).
          apply mor_disp_transportf_prewhisker. }
        etrans.
        {
          Search (transportf _ _ (transportf _ _ _ ) = _).
          apply transport_f_f. }
        unfold transportb.
        Search (transportf _ _ _ = transportf _ _ _ ).
        apply transportf_paths.
        apply homset_property.
      Qed.


  Definition total_BinCoproduct
    (a b : C)
    (H : BinCoproduct a b)
    (aa : D a)
    (bb : D b)
    (HH : disp_BinCoproduct H aa bb)
    :
    BinCoproduct (*total_category D*) (total_ob a aa) (total_ob b bb).
  Proof.
    repeat (use tpair); simpl.
    - apply H.
    - simpl. apply HH.
    - simpl. apply BinCoproductIn1.
    - simpl. apply disp_BinCoproductIn1.
    - simpl. apply BinCoproductIn2.
    - simpl. apply disp_BinCoproductIn2.
    - simpl. unfold isBinCoproduct.
      intros ccc fff ggg.
      use unique_exists.
      + simpl.
        use tpair.
        * apply (BinCoproductArrow H (#(pr1_category D) fff) (# (pr1_category D) ggg)).
        * simpl.
          apply (disp_BinCoproductArrow H aa bb HH (pr2 fff) (pr2 ggg)).
      + simpl.
        split; simpl.
        * use total2_paths_b.
          -- simpl.
             apply BinCoproductIn1Commutes.
          -- simpl.
             apply (disp_BinCoproductIn1Commutes H _ _ HH (pr2 fff) (pr2 ggg)).
        * use total2_paths_b.
          -- simpl.
             apply BinCoproductIn2Commutes.
          -- simpl.
             apply (disp_BinCoproductIn2Commutes H _ _ HH (pr2 fff) (pr2 ggg)).
      + intro y.
        simpl.
        Search (isaprop (_ × _ )).
        apply isapropdirprod.
        * apply (homset_property (total_category D) _ _ _ fff).
        * apply (homset_property (total_category D) _ _ _ ggg).
      + intro kkk.
        simpl.
        intros [H1 H2].
        use total2_paths_b.
        * simpl.
          apply BinCoproductArrowUnique.
          -- Search ( _ = _ -> pr1 _ = pr1 _ ).
             apply (base_paths _ _ H1).
          -- apply (base_paths _ _ H2).
        * simpl.
          destruct kkk as [k kk].
          simpl.
          apply disp_BinCoproductArrowUnique.
          -- Search ( _ = _ -> transportf _ _ (pr2 _) = pr2 _ ).
             apply transportb_transpose_right.
             apply (fiber_paths H1).
          --
             apply transportb_transpose_right.
             apply (fiber_paths H2).
  Defined.

  End foo.
