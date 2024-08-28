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
    (a b : C)
    (H : BinCoproduct a b)
    (aa : D a)
    (bb : D b)
    : UU
    := ∑ ccoiaaibb : (∑ cco : D H, aa -->[BinCoproductIn1 H] cco × bb -->[BinCoproductIn2 H] cco),
      disp_isBinCoproduct _ _ H aa bb (pr1 ccoiaaibb) (pr1 (pr2 ccoiaaibb)) (pr2 (pr2 ccoiaaibb)).



  End foo.
