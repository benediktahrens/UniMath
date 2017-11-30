
(** Imports *)

Require Export UniMath.Foundations.Propositions.

(** *The type of sets i.e. of types of h-level 2 in [UU] *)

Definition hSet : UU := total2 (λ X : UU, isaset X).
Definition hSetpair (X : UU) (i : isaset X) := tpair isaset X i : hSet.
Definition pr1hSet : hSet -> UU := @pr1 UU (λ X : UU, isaset X).
Coercion pr1hSet: hSet >-> UU.

Definition setproperty (X : hSet) := pr2 X.


(** * The type of subtypes of a given type *)
Definition hsubtype (X : UU) : UU := X -> hProp.
Identity Coercion id_hsubtype :  hsubtype >-> Funclass.
Definition carrier {X : UU} (A : hsubtype X) := total2 A.
Coercion carrier : hsubtype >-> Sortclass.

Lemma isasethsubtype (X : UU) : isaset (hsubtype X).
Proof.
  change (isofhlevel 2 (hsubtype X)).
  apply impred; intro x.
  exact isasethProp.
Defined.


(** *** A subtype with paths between any two elements is an [hProp]. *)


Lemma isapropsubtype {X : UU} (A : hsubtype X)
      (is : ∏ (x1 x2 : X), A x1 -> A x2 -> x1 = x2) : isaprop (carrier A).
Proof.
  intros. apply invproofirrelevance.
  intros x x'.
  assert (X0 : isincl (@pr1 _ A)).
  {
    apply isinclpr1.
    intro x0.
    apply (pr2 (A x0)).
  }
  apply (invmaponpathsincl (@pr1 _ A) X0).
  destruct x as [ x0 is0 ].
  destruct x' as [ x0' is0' ].
  simpl.
  apply (is x0 x0' is0 is0').
Defined.



(** * Relations *)

Definition hrel (X : UU) : UU := X -> X -> hProp.

Definition istrans {X : UU} (R : hrel X) : UU
  := ∏ (x1 x2 x3 : X), R x1 x2 -> R x2 x3 -> R x1 x3.
Definition isrefl {X : UU} (R : hrel X) : UU
  := ∏ x : X, R x x.
Definition issymm {X : UU} (R : hrel X) : UU
  := ∏ (x1 x2 : X), R x1 x2 -> R x2 x1.

Definition ispreorder {X : UU} (R : hrel X) : UU := istrans R × isrefl R.

Definition iseqrel {X : UU} (R : hrel X) := ispreorder R × issymm R.

Definition iseqrelconstr {X : UU} {R : hrel X}
           (trans0 : istrans R)
           (refl0 : isrefl R)
           (symm0 : issymm R)
  : iseqrel R
  := dirprodpair (dirprodpair trans0 refl0) symm0.



(** *** Eqivalence relations and associated types. *)

Definition eqrel (X : UU) : UU
  := ∑ R : hrel X, iseqrel R.
Definition eqrelpair {X : UU} (R : hrel X) (is : iseqrel R)
  : eqrel X
  := tpair (λ R : hrel X, iseqrel R) R is.
Definition eqrelconstr {X : UU} (R : hrel X)
           (is1 : istrans R) (is2 : isrefl R) (is3 : issymm R) : eqrel X
  := eqrelpair R (dirprodpair (dirprodpair is1 is2) is3).

Definition pr1eqrel (X : UU) : eqrel X -> (X -> (X -> hProp)) := @pr1 _ _.
Coercion pr1eqrel : eqrel >-> Funclass.

Definition eqreltrans {X : UU} (R : eqrel X) : istrans R := pr1 (pr1 (pr2 R)).
Definition eqrelrefl {X : UU} (R : eqrel X) : isrefl R := pr2 (pr1 (pr2 R)).
Definition eqrelsymm {X : UU} (R : eqrel X) : issymm R := pr2 (pr2 R).



(** *** Equivalence classes with respect to a given relation *)



Definition iseqclass {X : UU} (R : hrel X) (A : hsubtype X) : UU
  :=
    (ishinh (carrier A))
      ×
      ((∏ x1 x2 : X, R x1 x2 -> A x1 -> A x2)
         ×
         (∏ x1 x2 : X, A x1 ->  A x2 -> R x1 x2)).
Definition iseqclassconstr {X : UU} (R : hrel X) {A : hsubtype X}
           (ax0 : ishinh (carrier A))
           (ax1 : ∏ x1 x2 : X, R x1 x2 -> A x1 -> A x2)
           (ax2 : ∏ x1 x2 : X, A x1 ->  A x2 -> R x1 x2)
  : iseqclass R A
  := dirprodpair ax0 (dirprodpair ax1 ax2).

Definition eqax0 {X : UU} {R : hrel X} {A : hsubtype X}
  : iseqclass R A -> ishinh (carrier A)
  := λ is : iseqclass R A, pr1 is.
Definition eqax1 {X : UU} {R : hrel X} {A : hsubtype X}
  : iseqclass R A -> ∏ x1 x2 : X, R x1 x2 -> A x1 -> A x2
  := λ is : iseqclass R A, pr1 (pr2 is).
Definition eqax2 {X : UU} {R : hrel X} {A : hsubtype X}
  : iseqclass R A -> ∏ x1 x2 : X, A x1 -> A x2 -> R x1 x2
  := λ is : iseqclass R A, pr2 (pr2 is).


Lemma isapropiseqclass {X : UU} (R : hrel X) (A : hsubtype X)
  : isaprop (iseqclass R A).
Proof.
  apply isofhleveldirprod.
  - exact (isapropishinh (carrier A)).
  - apply isofhleveldirprod.
    + repeat (apply impred; intro).
      exact (pr2 (A t0)).
    + repeat (apply impred; intro).
      exact (pr2 (R t t0)).
Defined.



(** ** Set quotients of types.

In this file we study the set quotients of types by equivalence relations. While
the general notion of a quotient of a type by a relation is complicated due to
the existence of different kinds of quotients (e.g. homotopy quotients or
categorical quotients in the homotopy category which are usually different from
each other) there is one particular class of quotients which is both very
important for applications and semantically straightforward. These quotients are
the universal functions from a type to an hset which respect a given relation.
Some of the proofs in this section depend on the proerties of the hinhabited
construction and some also depend on the univalence axiom for [hProp] which
allows us to prove that the type of monic subtypes of a type is a set.

Our main construction is analogous to the usual construction of quotient as a
set of equivalence classes. Wev also consider another construction of [setquot]
which is analogous (on the next h-level) to our construction of [ishinh]. Both
have generalizations to the "higher" quotients (i.e. groupoid quotients etc.)
which will be considered separately. In particular, the quotients the next
h-level appear to be closely related to the localizations of categories and will
be considered in the section about types of h-level 3.
*)



(** *** Setquotient defined in terms of equivalence classes *)


Definition setquot {X : UU} (R : hrel X) : UU
  := ∑ A : hsubtype X, iseqclass R A.
Definition setquotpair {X : UU} (R : hrel X) (A : hsubtype X)
           (is : iseqclass R A)
  : setquot R
  := A ,, is.
Definition pr1setquot {X : UU} (R : hrel X)
  : setquot R -> (hsubtype X)
  := @pr1 _ (λ A : _, iseqclass R A).
Coercion pr1setquot : setquot >-> hsubtype.

Lemma isinclpr1setquot {X : UU} (R : hrel X) : isincl (pr1setquot R).
Proof.
  apply isinclpr1. intro x0. apply isapropiseqclass.
Defined.

Definition setquottouu0 {X : UU} (R : hrel X) (a : setquot R)
  := carrier (pr1 a).
Coercion setquottouu0 : setquot >-> Sortclass.

Theorem isasetsetquot {X : UU} (R : hrel X) : isaset (setquot R).
Proof.
  apply (isasetsubset (@pr1 _ _) (isasethsubtype X)).
  apply isinclpr1; intro x.
  apply isapropiseqclass.
Defined.

Theorem setquotpr {X : UU} (R : eqrel X) : X -> setquot R.
Proof.
  intro x.
  set (rax := eqrelrefl R).
  set (sax := eqrelsymm R).
  set (tax := eqreltrans R).
  apply (tpair _ (λ x0 : X, R x x0)).
  split.
  - exact (hinhpr (tpair _ x (rax x))).
  - split; intros x1 x2 X1 X2.
    + exact (tax x x1 x2 X2 X1).
    + exact (tax x1 x x2 (sax x x1 X1) X2).
Defined.


Lemma setquotl0 {X : UU} (R : eqrel X) (c : setquot R) (x : c) :
  setquotpr R (pr1 x) = c.
Proof.
  apply (invmaponpathsincl _ (isinclpr1setquot R)).
  apply funextsec; intro x0.
  apply hPropUnivalence; intro r.
  - exact (eqax1 (pr2 c) (pr1 x) x0 r (pr2 x)).
  - exact (eqax2 (pr2 c) (pr1 x) x0 (pr2 x) r).
Defined.

(*
Theorem issurjsetquotpr {X : UU} (R : eqrel X) : issurjective (setquotpr R).
Proof.
  intros. unfold issurjective.
  intro c. apply (@hinhuniv (carrier (pr1 c))).
  intro x. apply hinhpr.
  split with (pr1 x).
  - apply setquotl0.
  - apply (eqax0 (pr2 c)).
Defined.
*)
Lemma iscompsetquotpr {X : UU} (R : eqrel X) (x x' : X) (a : R x x') :
  setquotpr R x = setquotpr R x'.
Proof.
  intros. apply (invmaponpathsincl _ (isinclpr1setquot R)).
  simpl. apply funextsec.
  intro x0. apply hPropUnivalence.
  intro r0. apply (eqreltrans R _ _ _ (eqrelsymm R _ _ a) r0).
  intro x0'. apply (eqreltrans R _ _ _ a x0').
Defined.




(** *** Universal property of [seqtquot R] for functions to sets satisfying compatibility condition [iscomprelfun] *)


Definition iscomprelfun {X Y : UU} (R : hrel X) (f : X -> Y) : UU
  := ∏ x x' : X, R x x' -> f x = f x'.

Lemma isapropimeqclass {X : UU} (R : hrel X) (Y : hSet) (f : X -> Y)
      (is : iscomprelfun R f) (c : setquot R) :
  isaprop (image (λ x : c, f (pr1 x))).
Proof.
  apply isapropsubtype.
  intros y1 y2. simpl.
  apply (@hinhuniv2 _ _ (hProppair (y1 = y2) (pr2 Y y1 y2))).
  intros x1 x2. simpl.
  destruct c as [ A iseq ].
  destruct x1 as [ x1 is1 ]. destruct x2 as [ x2 is2 ].
  destruct x1 as [ x1 is1' ]. destruct x2 as [ x2 is2' ].
  simpl in is1. simpl in is2. simpl in is1'. simpl in is2'.
  assert (r : R x1 x2) by apply (eqax2 iseq _ _ is1' is2').
  apply (pathscomp0 (pathsinv0 is1) (pathscomp0 (is _ _ r) is2)).
Defined.
Global Opaque isapropimeqclass.

Theorem setquotuniv {X : UU} (R : hrel X) (Y : hSet) (f : X -> Y)
        (is : iscomprelfun R f) (c : setquot R) : Y.
Proof.
  intros.
  apply (pr1image (λ x : c, f (pr1 x))).
  apply (@hinhuniv (pr1 c) (hProppair _ (isapropimeqclass R Y f is c))
                   (prtoimage (λ x : c, f (pr1 x)))).
  apply (eqax0 (pr2 c)).
Defined.


(** Note : the axioms rax, sax and trans are not used in the proof of
  setquotuniv. If we consider a relation which is not an equivalence relation
  then setquot will still be the set of subsets which are equivalence classes.
  Now however such subsets need not to cover all of the type. In fact their set
  can be empty. Nevertheless setquotuniv will apply. *)


Theorem setquotunivcomm {X : UU} (R : eqrel X) (Y : hSet) (f : X -> Y)
        (is : iscomprelfun R f) :
  ∏ x : X, setquotuniv R Y f is (setquotpr R x) = f x.
Proof.
  intros. unfold setquotuniv. unfold setquotpr.
  simpl. apply idpath.
Defined.


Theorem weqpathsinsetquot {X : UU} (R : eqrel X) (x x' : X) :
  R x x' ≃ setquotpr R x = setquotpr R x'.
Proof.
  intros. split with (iscompsetquotpr R x x').
  apply isweqimplimpl.
  - intro e.
    set (e' := maponpaths (pr1setquot R) e).
    unfold pr1setquot in e'. unfold setquotpr in e'. simpl in e'.
    set (e'' := maponpaths (λ f : _, f x') e'). simpl in e''.
    apply (eqweqmaphProp (pathsinv0 e'') (eqrelrefl R x')).
  - apply (pr2 (R x x')).
  - set (int := isasetsetquot R (setquotpr R x) (setquotpr R x')). assumption.
Defined.

(* End of the file Set_level_mathematics.v *)
