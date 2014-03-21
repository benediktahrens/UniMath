
Require Import Utf8.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel2.hSet.

Definition folds_ob_mor := total2 (λ a : UU, a → a → hSet).
Definition folds_ob_mor_pair (ob : UU)(mor : ob → ob → hSet) :
    folds_ob_mor := tpair _ ob mor.

Definition ob (C : folds_ob_mor) : Type := @pr1 _ _ C.
Coercion ob : folds_ob_mor >-> Sortclass.

Definition precategory_morphisms {C : folds_ob_mor} : C → C → hSet := pr2 C.
Local Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).

Definition folds_id_comp := total2 (λ C : folds_ob_mor,
    dirprod (∀ a : C, a ⇒ a → hProp) 
            (∀ (a b c : C), (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → hProp)).

Definition folds_ob_mor_from_folds_id_comp (C : folds_id_comp) : folds_ob_mor := pr1 C.
Coercion folds_ob_mor_from_folds_id_comp : folds_id_comp >-> folds_ob_mor.

Definition id {C : folds_id_comp} : ∀ {a : C}, a ⇒ a → hProp := pr1 (pr2 C).
Definition comp {C : folds_id_comp} :
      ∀ {a b c : C}, (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → hProp := pr2 (pr2 C).

(* the complete list of axioms will hurt *)

Definition folds_ax := total2 (λ C : folds_id_comp,
    dirprod (∀ a : C, ishinh (total2 (λ f : a ⇒ a, id f))) 
            (∀ (a b : C) (f : a ⇒ b)(i : b ⇒ b), id i → comp f i f)).

