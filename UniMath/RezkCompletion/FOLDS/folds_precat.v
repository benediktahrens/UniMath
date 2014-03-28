
Require Import Utf8.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.
Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.


Definition folds_ob_mor := total2 (λ a : UU, a → a → hSet).
Definition folds_ob_mor_pair (ob : UU)(mor : ob → ob → hSet) :
    folds_ob_mor := tpair _ ob mor.

Definition ob (C : folds_ob_mor) : Type := @pr1 _ _ C.
Coercion ob : folds_ob_mor >-> Sortclass.

Definition folds_morphisms {C : folds_ob_mor} : C → C → hSet := pr2 C.
Local Notation "a ⇒ b" := (folds_morphisms a b)(at level 50).

Definition folds_id_comp := total2 (λ C : folds_ob_mor,
    dirprod (∀ a : C, a ⇒ a → hProp) 
            (∀ (a b c : C), (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → hProp)).

Definition folds_ob_mor_from_folds_id_comp (C : folds_id_comp) : folds_ob_mor := pr1 C.
Coercion folds_ob_mor_from_folds_id_comp : folds_id_comp >-> folds_ob_mor.

Definition id {C : folds_id_comp} : ∀ {a : C}, a ⇒ a → hProp := pr1 (pr2 C).
Definition comp {C : folds_id_comp} :
      ∀ {a b c : C}, (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → hProp := pr2 (pr2 C).

(* the complete list of axioms will hurt *)

Definition folds_ax_id (C : folds_id_comp) := 
    dirprod (∀ a : C, ishinh (total2 (λ f : a ⇒ a, id f)))  (* there is an identity *)
     (dirprod (∀ (a b : C) (f : a ⇒ b)(i : b ⇒ b), id i → comp f i f) (* id is post neutral *)      
              (∀ (a b : C) (f : a ⇒ b)(i : a ⇒ a), id i → comp i f f)). (* id is pre neutral *)

Lemma isaprop_folds_ax_id C : isaprop (folds_ax_id C).
Proof.
 repeat (apply isapropdirprod).
 - apply impred; intro; apply isapropishinh.
 - repeat (apply impred; intro). apply pr2.  
 - repeat (apply impred; intro). apply pr2.
Qed.

Definition folds_ax_comp (C : folds_id_comp) :=
    dirprod (∀ {a b c : C} (f : a ⇒ b) (g : b ⇒ c), 
                ishinh (total2 (λ h : a ⇒ c, comp f g h))) 
            (∀ {a b c : C} {f : a ⇒ b} {g : b ⇒ c} {h k : a ⇒ c},
                  comp f g h → comp f g k → h == k ).

Lemma isaprop_folds_ax_comp C : isaprop (folds_ax_comp C).
Proof.
 repeat (apply isapropdirprod).
 - do 5 (apply impred; intro). apply isapropishinh.
 - repeat (apply impred; intro). apply (pr2 (_ ⇒ _)) .  
Qed.


Definition folds_precat := total2 (λ C : folds_id_comp,
    dirprod (folds_ax_id C) (folds_ax_comp C)).
Definition folds_id_comp_from_folds_precat (C : folds_precat) : folds_id_comp := pr1 C.
Coercion folds_id_comp_from_folds_precat : folds_precat >-> folds_id_comp.

Section some_lemmas_about_folds_precats.

Variable C : folds_precat.

Lemma id_unique : ∀ (a : C) (i i' : a ⇒ a), id i → id i' → i == i'.
Proof.
  intros a i i' Hi Hi'.
  destruct C as [CC [Cid Ccomp]]; simpl in *.
  assert (H1 : comp i i' i).
  { apply (pr1 (pr2 Cid) _ _ _ _  ).  assumption. }
  assert (H2 : comp i i' i').
  { apply (pr2 (pr2 Cid) _ _ _ _ ) . assumption. }
  apply (pr2 Ccomp _ _ _ _ _ _ _ H1 H2).
Qed.

Lemma id_contr : ∀ a : C, iscontr (total2 (λ f : a ⇒ a, id f)).  
Proof.
  intro a.
  set (H := pr1 (pr1 (pr2 C)) a).
  set (H' := hProppair (iscontr (total2 (λ f : a ⇒ a, id f)))
                      (isapropiscontr _ )).
  apply (H H'); simpl.
  intro t; exists t.
  intro t'.
  apply total2_paths_hProp.
  - intro b; apply pr2.
  - destruct t; destruct t';
    apply id_unique; assumption.
Defined.

Lemma comp_contr : ∀ (a b c : C) (f : a ⇒ b) (g : b ⇒ c), 
    iscontr (total2 (λ h, comp f g h)).
Proof.
  intros a b c f g.
  set (H' := hProppair (iscontr (total2 (λ h : a ⇒ c, comp f g h)))
                      (isapropiscontr _ )).
  apply (pr1 (pr2 (pr2 C)) a b c f g H').
  simpl; intro t; exists t.
  intro t'.
  apply total2_paths_hProp.
  - intro; apply pr2.
  - destruct t; destruct t'; simpl in *.
    apply (pr2 (pr2 (pr2 C)) _ _ _ f g ); assumption.
Defined.

End some_lemmas_about_folds_precats.

