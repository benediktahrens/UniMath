Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctor. Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.

Open Scope cat.

Definition TODO : ∏ X : Type, X.
  admit.
Admitted.

Section ps.

  Context (C D : bicat).

  Definition ps0 : bicat.
  Proof.
    use build_bicategory.
    - use build_prebicat_data.
      + exact (C → D).
      + intros F₀ G₀. exact (∏ x, D⟦F₀ x, G₀ x⟧).
      + cbn. intros F₀ G₀ γ₀ δ₀.
        exact (∏ x, γ₀ x ==>  δ₀ x).
      + cbn. intros. apply id₁.
      + cbn. intros. use (_ · _ ). apply Y. apply x.  apply X0.  apply X1.
      + cbn. intros. apply id₂.
      + cbn. intros. use (_ • _ ). apply g. apply X0. apply X1.
      + cbn. intros. use (_ ◃ _ ). apply X0.
      + cbn; intros. use (_ ▹ _ ). apply X0.
      + cbn; intros. apply lunitor.
      + cbn; intros. apply linvunitor.
      + cbn; intros. apply runitor.
      + cbn; intros. apply rinvunitor.
      + cbn; intros. apply lassociator.
      + cbn; intros. apply rassociator.
    - apply TODO.
    - apply TODO.
  Defined.


  Definition ps1_disp_prebicat_1_id_comp_cells :  disp_prebicat_1_id_comp_cells ps0.
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * intro F₀.  exact (∏ (x y : C), C⟦x, y⟧ → D⟦F₀ x, F₀ y⟧).
        * cbn. intros F₀ G₀ F₁ G₁ γ₀.
          exact (∏ x y (f : C⟦x, y⟧), γ₀ x · G₁ _ _ f ==> F₁ _ _ f · γ₀ y).
      + use tpair.
        * cbn. intros F₀ F₁ x y f.
          refine (_ • _ ).
(*          ** apply F₁. apply f. *)
          ** apply lunitor.
          ** apply rinvunitor.
        * cbn. intros F₀ G₀ H₀ γ₀ δ₀ F₁ G₁ H₁ η ε x y f.
          refine (_ • _ • _ • _ • _ ).
          ** apply rassociator.
          ** apply lwhisker. apply ε.
          ** apply lassociator.
          ** apply (rwhisker _ (η _ _ _ )).
          ** apply rassociator.
    - cbn. hnf. intros F₀ G₀ γ₀ δ₀ Γ F₁ G₁ γ₁ δ₁.  cbn in *.
      exact (∏ x y (f : C⟦x, y⟧), Γ _ ▹ G₁ _ _ f • δ₁ _ _ f = γ₁ _ _ f • (F₁ _ _ f ◃ Γ _ )).
  Defined.

  Definition ps1_disp_prebicat_ops : disp_prebicat_ops ps1_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat split; cbn; intros; apply TODO.
  Qed.

End ps.