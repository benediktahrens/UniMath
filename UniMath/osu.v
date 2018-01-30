Require Import UniMath.Foundations.Preamble.

Check (λ m n : nat, m = n).

Check (λ (A : UU) (a a' : A), a = a').

Check (λ (A : UU) (a : A), idpath a).
Check @idpath.

Definition path_inv (A : UU) (a b : A) : a = b → b = a.
Proof.
  intro e.
  induction e.
  apply idpath.
Defined.
Print path_inv.

Check @paths_rect.

(*
paths_rect
     : ∏ (A : UU) (a : A) (P : ∏ a0 : A, a = a0 → Type),
       P a (idpath a) → ∏ (y : A) (p : a = y), P y p
 *)

Definition paths_rect_curry :
  ∏ (A : UU) (a : A) (P : (∑ (a0 : A), a = a0) → UU),
  P (a,,idpath a) → ∏ t, P t.
Proof.
  intros A a P p t.
  induction t as [a0 e].
  induction e.
  apply p.
Defined.

Definition is_contractible (A : UU) : UU
  := ∑ (a : A), ∏ (a' : A), a' = a.

Lemma is_contractible_cone (A : UU) (a : A)
  : is_contractible (∑ a' : A, a' = a).
Proof.
  exists (a,, idpath a : ∑ a' : A, a' = a).
  intro a'e.
  induction a'e as [a' e].
  induction e.
  apply idpath.
Defined.

Definition paths_comp {A : UU} {a b c : A}
  : a = b → b = c → a = c.
Proof.
  intros e e'.
  induction e. exact e'.
  (* or
     induction e'. exact e.
     or
     induction e. induction e'. apply idpath.
   *)
Defined.

Notation " e @ e' " := (paths_comp e e').

Definition paths_comp_id_1 {A : UU} {a c : A}
           (e' : a = c)
  : idpath a @ e' = e'.
Proof.
  apply idpath.
Defined.

Definition paths_comp_id_2 {A : UU} {a c : A}
           (e : a = c)
  : e @ idpath c = e.
Proof.
  Fail apply idpath.
  induction e.
  apply idpath.
Defined.
