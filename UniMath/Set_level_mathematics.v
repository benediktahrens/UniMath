
(** Imports *)

Require Export UniMath.Foundations.Propositions.




(** ** The type of sets i.e. of types of h-level 2 in [UU] *)

Definition hSet : UU := total2 (λ X : UU, isaset X).
Definition hSetpair (X : UU) (i : isaset X) := tpair isaset X i : hSet.
Definition pr1hSet : hSet -> UU := @pr1 UU (λ X : UU, isaset X).
Coercion pr1hSet: hSet >-> UU.

Definition eqset {X : hSet} (x x' : X) : hProp
  := hProppair (x = x') (pr2 X x x').
Notation "a = b" := (eqset a b) (at level 70, no associativity) : set.

Delimit Scope set with set.

Definition setproperty (X : hSet) := pr2 X.




(** ** Types [X] which satisfy "weak" axiom of choice for all families [P : X -> UU]

Weak axiom of choice for [X] is the condition that for any family [P : X -> UU]
over [X] such that all members of the family are inhabited the space of sections
of the family is inhabited. Equivalently one can formulate it as an assertion
that for any surjection (see below) [p : Y -> X] the space of sections of this
surjection i.e. functions [s : X -> Y] together with a homotopy from
[funcomp s p] to [idfun X] is inhabited. It does not provide a choice of a
section for such a family or a surjection. In topos-theoretic semantics this
condition corresponds to "local projectivity" of [X]. It automatically holds
for the point [unit] but need not hold for sub-objects of [unit] i.e. for types
of h-level 1 (propositions). In particular it does not have to hold for general
types with decidable equality.

Intuition based on standard univalent models suggests that any type satisfying
weak axiom of choice is a set. Indeed it seems to be possible to show that if
both a type and the set of connected components of this type (see below)
satisfy weak  axiom of choice then the type is a set. In particular, if one
imposes weak axiom of choice for sets as an axiom then it would follow that
every type satisfying weak axiom of choice is a set. I do not know however if
there are models which would validate a possibility of types other than sets
to satisfy weak axiom of choice.
*)

Definition ischoicebase_uu1 (X : UU)
  := ∏ P : X -> UU, (∏ x : X, ishinh (P x)) -> ishinh (∏ x : X, P x).








(** ** The type of monic subtypes of a type (subsets of the set of connected components) *)


(** *** General definitions *)

Definition hsubtype (X : UU) : UU := X -> hProp.
Identity Coercion id_hsubtype :  hsubtype >-> Funclass.
Definition carrier {X : UU} (A : hsubtype X) := total2 A.
Coercion carrier : hsubtype >-> Sortclass.
Definition carrierpair {X : UU} (A : hsubtype X) :
   ∏ t : X, A t → ∑ x : X, A x := tpair A.
Definition pr1carrier {X : UU} (A : hsubtype X) := @pr1 _ _  : carrier A -> X.

Lemma isaset_carrier_subset (X : hSet) (Y : hsubtype X) : isaset (∑ x, Y x).
Proof.
  intros. apply isaset_total2.
  - apply setproperty.
  - intro x. apply isasetaprop, propproperty.
Defined.

Definition carrier_subset {X : hSet} (Y : hsubtype X) : hSet
  := hSetpair (∑ x, Y x) (isaset_carrier_subset X Y).


Delimit Scope subset with subset.

Lemma isinclpr1carrier {X : UU} (A : hsubtype X) : isincl (@pr1carrier X A).
Proof.
  intros. apply (isinclpr1 A (λ x : _, pr2 (A x))).
Defined.

Lemma isasethsubtype (X : UU) : isaset (hsubtype X).
Proof.
  change (isofhlevel 2 (hsubtype X)).
  apply impred; intro x.
  exact isasethProp.
Defined.

Definition totalsubtype (X : UU) : hsubtype X := λ x, htrue.

Definition weqtotalsubtype (X : UU) : totalsubtype X ≃ X.
Proof.
  apply weqpr1. intro. apply iscontrunit.
Defined.

Definition weq_subtypes {X Y : UU} (w : X ≃ Y)
           (S : hsubtype X) (T : hsubtype Y) :
           (∏ x, S x <-> T (w x)) -> carrier S ≃ carrier T.
Proof.
  intros eq. apply (weqbandf w). intro x. apply weqiff.
  - apply eq.
  - apply propproperty.
  - apply propproperty.
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

Definition squash_pairs_to_set {Y : UU} (F : Y -> UU) :
  (isaset Y) -> (∏ y y', F y -> F y' -> y = y') -> (∃ y, F y) -> Y.
Proof.
  intros is e.
  set (P := ∑ y, ∥ F y ∥).
  assert (iP : isaprop P).
  {
    apply isapropsubtype. intros y y' f f'.
    apply (squash_to_prop f). apply is. clear f; intro f.
    apply (squash_to_prop f'). apply is. clear f'; intro f'.
    apply e.
    - assumption.
    - assumption.
  }
  intros w.
  assert (p : P).
  {
    apply (squash_to_prop w). exact iP. clear w; intro w.
    exact (pr1 w,,hinhpr (pr2 w)).
  }
  clear w.
  exact (pr1 p).
Defined.

Definition squash_to_set {X Y : UU} (is : isaset Y) (f : X -> Y) :
          (∏ x x', f x = f x') -> ∥ X ∥ -> Y.
Proof.
  intros e w.
  set (P := ∑ y, ∃ x, f x = y).
  assert (j : isaprop P).
  {
    apply isapropsubtype; intros y y' j j'.
    apply (squash_to_prop j). apply is. clear j; intros [j k].
    apply (squash_to_prop j'). apply is. clear j'; intros [j' k'].
    intermediate_path (f j). exact (!k).
    intermediate_path (f j'). apply e. exact k'.
  }
  assert (p : P).
  {
    apply (squash_to_prop w). exact j. intro x0.
    exists (f x0). apply hinhpr. exists x0. apply idpath.
  }
  exact (pr1 p).
Defined.

(* End of "the type of monic subtypes of a type". *)







(** ** Relations on types (or equivalently relations on the sets of connected components) *)


(** *** Relations and boolean relations *)

Definition hrel (X : UU) : UU := X -> X -> hProp.
Identity Coercion idhrel : hrel >-> Funclass.

Definition brel (X : UU) : UU := X -> X -> bool.
Identity Coercion idbrel : brel >-> Funclass.

(** *** Standard properties of relations *)



Definition istrans {X : UU} (R : hrel X) : UU
  := ∏ (x1 x2 x3 : X), R x1 x2 -> R x2 x3 -> R x1 x3.

Definition isrefl {X : UU} (R : hrel X) : UU
  := ∏ x : X, R x x.

Definition issymm {X : UU} (R : hrel X) : UU
  := ∏ (x1 x2 : X), R x1 x2 -> R x2 x1.

Definition ispreorder {X : UU} (R : hrel X) : UU := istrans R × isrefl R.

Definition iseqrel {X : UU} (R : hrel X) := ispreorder R × issymm R.
Definition iseqrelconstr {X : UU} {R : hrel X}
           (trans0 : istrans R) (refl0 : isrefl R) (symm0 : issymm R) :
  iseqrel R := dirprodpair (dirprodpair trans0 refl0) symm0.

Definition isirrefl {X : UU} (R : hrel X) : UU := ∏ x : X, ¬ R x x.

Definition isasymm {X : UU} (R : hrel X) : UU
  := ∏ (x1 x2 : X), R x1 x2 -> R x2 x1 -> empty.

Definition iscoasymm {X : UU} (R : hrel X) : UU := ∏ x1 x2, ¬ R x1 x2 -> R x2 x1.

Definition istotal {X : UU} (R : hrel X) : UU := ∏ x1 x2, R x1 x2 ∨ R x2 x1.

Definition isdectotal {X : UU} (R : hrel X) : UU := ∏ x1 x2, R x1 x2 ⨿ R x2 x1.

Definition iscotrans {X : UU} (R : hrel X) : UU
  := ∏ x1 x2 x3, R x1 x3 -> R x1 x2 ∨ R x2 x3.

Definition isdeccotrans {X : UU} (R : hrel X) : UU
  := ∏ x1 x2 x3, R x1 x3 -> R x1 x2 ⨿ R x2 x3.

Definition isdecrel {X : UU} (R : hrel X) : UU := ∏ x1 x2, R x1 x2 ⨿ ¬ R x1 x2.

Definition isnegrel {X : UU} (R : hrel X) : UU
  := ∏ x1 x2, ¬ ¬ R x1 x2 -> R x1 x2.

(** Note that the property of being (co-)antisymmetric is different from other
  properties of relations which we consider due to the presence of [paths] in
  its formulation. As a consequence it behaves differently relative to the
  quotients of types - the quotient relation can be (co-)antisymmetric while
  the original relation was not. *)

Definition isantisymm {X : UU} (R : hrel X) : UU
  := ∏ (x1 x2 : X), R x1 x2 -> R x2 x1 -> x1 = x2.

Definition isPartialOrder {X : UU} (R : hrel X) : UU
  := ispreorder R × isantisymm R.

Ltac unwrap_isPartialOrder i :=
  induction i as [transrefl antisymm]; induction transrefl as [trans refl].

Definition isantisymmneg {X : UU} (R : hrel X) : UU
  := ∏ (x1 x2 : X), ¬ R x1 x2 -> ¬ R x2 x1 -> x1 = x2.

Definition iscoantisymm {X : UU} (R : hrel X) : UU
  := ∏ x1 x2, ¬ R x1 x2 -> R x2 x1 ⨿ (x1 = x2).

(** Note that the following condition on a relation is different from all the
  other which we have considered since it is not a property but a structure,
  i.e. it is in general unclear whether [isaprop (neqchoice R)] is provable. *)

Definition neqchoice {X : UU} (R : hrel X) : UU
  := ∏ x1 x2, x1 != x2 -> R x1 x2 ⨿ R x2 x1.

(** proofs that the properties are propositions  *)

Lemma isaprop_istrans {X : hSet} (R : hrel X) : isaprop (istrans R).
Proof.
  intros. repeat (apply impred;intro). apply propproperty.
Defined.

Lemma isaprop_isrefl {X : hSet} (R : hrel X) : isaprop (isrefl R).
Proof.
  intros. apply impred; intro. apply propproperty.
Defined.

Lemma isaprop_istotal {X : hSet} (R : hrel X) : isaprop (istotal R).
Proof.
  intros. unfold istotal.
  apply impred; intro x.
  apply impred; intro y.
  apply propproperty.
Defined.

Lemma isaprop_isantisymm {X : hSet} (R : hrel X) : isaprop (isantisymm R).
Proof.
  intros. unfold isantisymm. apply impred; intro x. apply impred; intro y.
  apply impred; intro r. apply impred; intro s. apply setproperty.
Defined.

Lemma isaprop_ispreorder {X : hSet} (R : hrel X) : isaprop (ispreorder R).
Proof.
  intros.
  unfold ispreorder.
  apply isapropdirprod.
  { apply isaprop_istrans. }
  { apply isaprop_isrefl. }
Defined.

Lemma isaprop_isPartialOrder {X : hSet} (R : hrel X) :
  isaprop (isPartialOrder R).
Proof.
  intros.
  unfold isPartialOrder.
  apply isapropdirprod.
  { apply isaprop_ispreorder. }
  { apply isaprop_isantisymm. }
Defined.

(** the relations on a set form a set *)

Definition isaset_hrel (X : hSet) : isaset (hrel X).
  intros. unfold hrel.
  apply impred_isaset; intro x.
  apply impred_isaset; intro y.
  exact isasethProp.
Defined.



(** *** Standard properties of relations and logical equivalences *)

Definition hrellogeq {X : UU} (L R : hrel X) : UU
  := ∏ x1 x2, (L x1 x2 <-> R x1 x2).

Definition istranslogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : istrans L) : istrans R.
Proof.
  intros. intros x1 x2 x3 r12 r23.
  apply ((pr1 (lg _ _)) (isl _ _ _ ((pr2 (lg _ _)) r12) ((pr2 (lg _ _)) r23))).
Defined.

Definition isrefllogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : isrefl L) : isrefl R.
Proof.
  intros. intro x. apply (pr1 (lg _ _) (isl x)).
Defined.

Definition issymmlogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : issymm L) : issymm R.
Proof.
  intros. intros x1 x2 r12.
  apply (pr1 (lg _ _) (isl _ _ (pr2 (lg _ _) r12))).
Defined.

Definition ispologeqf {X : UU} {L R : hrel X} (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2)
           (isl : ispreorder L) : ispreorder R.
Proof.
  intros.
  apply (dirprodpair (istranslogeqf lg (pr1 isl)) (isrefllogeqf lg (pr2 isl))).
Defined.








(** *** Eqivalence relations and associated types. *)

Definition eqrel (X : UU) : UU := total2 (λ R : hrel X, iseqrel R).
Definition eqrelpair {X : UU} (R : hrel X) (is : iseqrel R) : eqrel X
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
  := dirprod (ishinh (carrier A))
             (dirprod (∏ x1 x2 : X, R x1 x2 -> A x1 -> A x2)
                      (∏ x1 x2 : X, A x1 ->  A x2 -> R x1 x2)).
Definition iseqclassconstr {X : UU} (R : hrel X) {A : hsubtype X}
           (ax0 : ishinh (carrier A))
           (ax1 : ∏ x1 x2 : X, R x1 x2 -> A x1 -> A x2)
           (ax2 : ∏ x1 x2 : X, A x1 ->  A x2 -> R x1 x2) : iseqclass R A
  := dirprodpair ax0 (dirprodpair ax1 ax2).

Definition eqax0 {X : UU} {R : hrel X} {A : hsubtype X} :
  iseqclass R A -> ishinh (carrier A) := λ is : iseqclass R A, pr1 is.
Definition eqax1 {X : UU} {R : hrel X} {A : hsubtype X} :
  iseqclass R A -> ∏ x1 x2 : X, R x1 x2 -> A x1 -> A x2
  := λ is : iseqclass R A, pr1 (pr2 is).
Definition eqax2 {X : UU} {R : hrel X} {A : hsubtype X} :
  iseqclass R A -> ∏ x1 x2 : X, A x1 -> A x2 -> R x1 x2
  := λ is : iseqclass R A, pr2 (pr2 is).

Lemma isapropiseqclass {X : UU} (R : hrel X) (A : hsubtype X) :
  isaprop (iseqclass R A).
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
  := total2 (λ A : _, iseqclass R A).
Definition setquotpair {X : UU} (R : hrel X) (A : hsubtype X)
           (is : iseqclass R A) : setquot R := tpair _ A is.
Definition pr1setquot {X : UU} (R : hrel X) : setquot R -> (hsubtype X)
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

Definition setquotinset {X : UU} (R : hrel X) : hSet :=
  hSetpair _ (isasetsetquot R).

Theorem setquotpr {X : UU} (R : eqrel X) : X -> setquot R.
Proof.
  intro x0.
  set (rax := eqrelrefl R).
  set (sax := eqrelsymm R).
  set (tax := eqreltrans R).
  apply (tpair _ (λ x : X, R x0 x)).
  split.
  - exact (hinhpr (tpair _ x0 (rax x0))).
  - split; intros x1 x2 X1 X2.
    + exact (tax x0 x1 x2 X2 X1).
    + exact (tax x1 x0 x2 (sax x0 x1 X1) X2).
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

Theorem issurjsetquotpr {X : UU} (R : eqrel X) : issurjective (setquotpr R).
Proof.
  intros. unfold issurjective.
  intro c. apply (@hinhuniv (carrier (pr1 c))).
  intro x. apply hinhpr.
  split with (pr1 x).
  - apply setquotl0.
  - apply (eqax0 (pr2 c)).
Defined.

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

Lemma iscomprelfunlogeqf {X Y : UU} {R L : hrel X} (lg : hrellogeq L R)
      (f : X -> Y) (is : iscomprelfun L f) : iscomprelfun R f.
Proof.
  intros. intros x x' r. apply (is _ _ (pr2 (lg  _ _) r)).
Defined.

Lemma isapropimeqclass {X : UU} (R : hrel X) (Y : hSet) (f : X -> Y)
      (is : iscomprelfun R f) (c : setquot R) :
  isaprop (image (λ x : c, f (pr1 x))).
Proof.
  intros. apply isapropsubtype.
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




(* End of the file hSet.v *)
