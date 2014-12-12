
(** hierarchy of categorical structures
    suggested by VV
*)

Require Import Foundations.hlevel2.hSet.

Definition s_0_category := UU.
Identity Coercion s_0_category_ : s_0_category >-> UU.

Definition s_1_category := total2 (fun O : s_0_category => O -> O -> UU).
Definition s_0_from_s_1_category (X : s_1_category) : s_0_category := pr1 X.
Coercion s_0_from_s_1_category : s_1_category >-> s_0_category.

Definition s_1_morphisms {X : s_1_category} (a b : X) : UU := pr2 X a b.
Coercion s_1_morphisms : s_1_category >-> Funclass.

Definition s_2_category := total2 (fun C : s_1_category => forall a b c : C, 
         C a b -> C b c -> C a c).

Definition s_2_from_s_1_category (X : s_2_category) : s_1_category := pr1 X.
Coercion s_2_from_s_1_category : s_2_category >-> s_1_category.

Definition comp {C : s_2_category}{a b c : C} : C a b -> C b c -> C a c := pr2 C a b c.

Notation "f ;; g" := (comp f g) (at level 50).

Definition s_3_category := total2 (fun C : s_2_category => forall a b c d 
   (f : C a b) (g : C b c) (h : C c d), (f ;; g) ;; h = f ;; (g ;; h)).

Definition s_3_from_s_2_category (X : s_3_category) : s_2_category := pr1 X.
Coercion s_3_from_s_2_category : s_3_category >-> s_2_category.


Definition assoc {C : s_3_category}{a b c d : C} := fun f g h =>
   (* f ;; (g ;; h) = (f ;; g) ;; h *)  pr2 C a b c d f g h.

Definition comp_1_eq {C : s_2_category}{a b c: C} (f f' : C a b) (g : C b c) (eqf : f = f'): 
   f ;; g = f' ;; g.
Proof.
  induction eqf.
  apply idpath.
Defined.

Definition comp_2_eq {C : s_2_category}{a b c: C} (f : C a b) (g g': C b c) (eqg : g = g'): 
   f ;; g = f ;; g'.
Proof.
  induction eqg.
  apply idpath.
Defined.


Definition cong {X Y : UU} (f : X -> Y) (x x': X) (p : x = x') : f x = f x' :=
  maponpaths _ p.

Definition cong2 {X Y Z : UU} (f : X -> Y -> Z) {x x': X} {y y' : Y} (pX : x = x') (pY: y = y'):
    f x y = f x' y'.
Proof.
  induction pX.
  apply cong.
  apply pY.
Defined.

Definition s_4_category := total2 (fun C : s_3_category => forall (a b c d e : C)
       (f: C a b)(g: C b c) (h: C c d) (k: C d e), assoc (f ;; g) h k @ assoc f g (h ;; k) = 
            comp_1_eq ((f;;g);;h) (f;;(g;;h)) k (assoc f g h) @ assoc f (g;;h) k @ 
                   comp_2_eq f ((g;;h);;k) (g;;(h;;k)) (assoc g h k)).

Definition s_4_category' := total2 (fun C : s_3_category => forall (a b c d e : C)
       (f: C a b)(g: C b c) (h: C c d) (k: C d e), assoc (f ;; g) h k @ assoc f g (h ;; k) = 
            cong2 _  (*(f;;g);;h*) (*f;;(g;;h)*) (*k*) (assoc f g h) (idpath _ ) @ assoc f (g;;h) k @ 
                   cong2 _  (*f ((g;;h);;k) (g;;(h;;k))*) (idpath _ ) (assoc g h k)).
               