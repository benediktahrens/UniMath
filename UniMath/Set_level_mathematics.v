(** * Generalities on [hSet].  Vladimir Voevodsky. Feb. - Sep. 2011

In this file we introduce the type [hSet] of h-sets, i.e., of types of h-level 2
as well as a number of constructions such as type of (monic) subtypes, images,
surjectivity etc. which, while they formally apply to functions between
arbitrary types actually only depend on the behavior of the function on the sets
of connected components of these types.

While it is possible to write a part of this file in a form which does not
require RR1 it seems like a waste of effort since it would require to repeat a
lot of things twice. Accordingly we assume RR1 from the start in dealing with
sets. The drawback is that all the subsequent files will not compile at the
moment without the Type in Type patch.
*)

(** ** Contents
- The type of sets i.e. of types of h-level 2 in [UU]
 - [hProp] as a set
 - Booleans as a set
- Types [X] which satisfy "weak" axiom of choice for all families
  [P : X -> UU]
- The type of monic subtypes of a type (subsets of the set of connected
  components)
 - General definitions
 - Direct product of two subtypes
 - A subtype with paths between any two elements is an [hProp]
- Relations on types (or equivalently relations on the sets of connected
  components)
 - Relations and boolean relations
 - Standard properties of relations
 - Elementary implications between properties of relations
 - Standard properties of relations and logical equivalences
 - Preorderings, partial orderings, and associated types
 - Equivalence relations and associated types
 - Direct product of two relations
 - Negation of a relation and its properties
 - Boolean representation of decidable equality
 - Boolean representation of decidable relations
 - Restriction of a relation to a subtype
 - Equivalence classes with respect to a given relation
 - Direct product of equivalence classes
- Surjections to sets are epimorphisms
- Epimorphisms are surjections
- Universal property enjoyed by surjections
- Set quotients of types
 - Set quotients defined in terms of equivalence classes
 - Universal property of [setquot R] for functions to sets satisfying
   compatibility condition [iscomprelfun]
 - Functoriality of [setquot] for functions mapping one relation to another
 - Universal property of [setquot] for predicates of one and several variables
 - The case when the function between quotients defined by [setquotfun] is a
   surjection, inclusion or a weak equivalence
 - [setquot] with respect to the product of two relations
 - Universal property of [setquot] for functions of two variables
 - Functoriality of [setquot] for functions of two variables mapping one
   relation to another
 - Set quotients with respect to decidable equivalence relations have decidable
   equality
 - Relations on quotient sets
 - Subtypes of quotients and quotients of subtypes
 - The set of connected components of a type
- Set quotients. Construction 2 (Unfinished)
 - Functions compatible with a relation
 - The quotient set of a type by a relation
 - Universal property of [setquot2 R] for functions to sets satisfying
   compatibility condition [iscomplrelfun]
 - Weak equivalence from [R x x'] to [paths (setquot2pr R x) (setquot2pr R x')]
- Consequences of univalence
*)


(** ** Preamble *)

(** Settings *)

(** The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.


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

Definition neqset {X : hSet} (x x' : X) : hProp
  := hProppair (x != x') (isapropneg _). (* uses funextemptyAxiom *)
Notation "a != b" := (neqset a b) (at level 70, no associativity) : set.
Delimit Scope set with set.

Definition setproperty (X : hSet) := pr2 X.

Definition setdirprod (X Y : hSet) : hSet.
Proof.
  intros. exists (X × Y).
  apply (isofhleveldirprod 2); apply setproperty.
Defined.

Definition setcoprod (X Y : hSet) : hSet.
Proof.
  intros. exists (X ⨿ Y). apply isasetcoprod; apply setproperty.
Defined.

Lemma isaset_total2_hSet (X : hSet) (Y : X -> hSet) : isaset (∑ x, Y x).
Proof.
  intros. apply isaset_total2.
  - apply setproperty.
  - intro x. apply setproperty.
Defined.

Definition total2_hSet {X : hSet} (Y : X -> hSet) : hSet
  := hSetpair (∑ x, Y x) (isaset_total2_hSet X Y).

Definition hfiber_hSet {X Y : hSet} (f : X → Y) (y : Y) : hSet
  := hSetpair (hfiber f y) (isaset_hfiber f y (pr2 X) (pr2 Y)).

Delimit Scope set with set.

Notation "'∑' x .. y , P" := (total2_hSet (λ x,.. (total2_hSet (λ y, P))..))
  (at level 200, x binder, y binder, right associativity) : set.
  (* type this in emacs in agda-input method with \sum *)

Lemma isaset_forall_hSet (X : UU) (Y : X -> hSet) : isaset (∏ x, Y x).
Proof.
  intros. apply impred_isaset. intro x. apply setproperty.
Defined.

Definition forall_hSet {X : UU} (Y : X -> hSet) : hSet
  := hSetpair (∏ x, Y x) (isaset_forall_hSet X Y).

Notation "'∏' x .. y , P" := (forall_hSet (λ x,.. (forall_hSet (λ y, P))..))
  (at level 200, x binder, y binder, right associativity) : set.
  (* type this in emacs in agda-input method with \sum *)

Definition unitset : hSet := hSetpair unit isasetunit.

Definition dirprod_hSet (X Y : hSet) : hSet.
Proof.
  intros X Y. exists (X × Y).
  abstract (exact (isasetdirprod _ _ (setproperty X) (setproperty Y))).
Defined.

Notation "A × B" := (dirprod_hSet A B) (at level 75, right associativity) : set.

(** *** [hProp] as a set *)

Definition hPropset : hSet := tpair _ hProp isasethProp.
(* Canonical Structure hPropset. *)

Definition hProp_to_hSet (P : hProp) : hSet
  := hSetpair P (isasetaprop (propproperty P)).

Coercion hProp_to_hSet : hProp >-> hSet.

(** *** Booleans as a set *)

Definition boolset : hSet := hSetpair bool isasetbool.
(* Canonical Structure boolset. *)

(* properties of functions between sets *)

Definition isInjectiveFunction {X Y : hSet} (f : X -> Y) : hProp.
Proof.
  intros. exists (∏ (x x': X), f x = f x' -> x = x').
  abstract (
      intros; apply impred; intro x; apply impred; intro y;
      apply impred; intro e; apply setproperty)
           using isaprop_isInjectiveFunction.
Defined.


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

(** Uses RR1 *)
Lemma isapropischoicebase (X : UU) : isaprop (ischoicebase_uu1 X).
Proof.
  intro. apply impred.
  intro P. apply impred.
  intro fs. apply (pr2 (ishinh _)).
Defined.

Definition ischoicebase (X : UU) : hProp := hProppair _ (isapropischoicebase X).

Lemma ischoicebaseweqf {X Y : UU} (w : X ≃ Y) (is : ischoicebase X) :
  ischoicebase Y.
Proof.
  intros. unfold ischoicebase.
  intros Q fs.
  apply (hinhfun (invweq (weqonsecbase Q w))).
  apply (is (funcomp w Q) (λ x : X, fs (w x))).
Defined.

Lemma ischoicebaseweqb {X Y : UU} (w : X ≃ Y) (is : ischoicebase Y) :
  ischoicebase X.
Proof.
  intros. apply (ischoicebaseweqf (invweq w) is).
Defined.

Lemma ischoicebaseunit : ischoicebase unit.
Proof.
  unfold ischoicebase. intros P fs.
  apply (hinhfun (tosecoverunit P)).
  apply (fs tt).
Defined.

Lemma ischoicebasecontr {X : UU} (is : iscontr X) : ischoicebase X.
Proof.
  intros.
  apply (ischoicebaseweqb (weqcontrtounit is) ischoicebaseunit).
Defined.

Lemma ischoicebaseempty : ischoicebase empty.
Proof.
  unfold ischoicebase. intros P fs.
  apply (hinhpr (λ x : empty, fromempty x)).
Defined.

Lemma ischoicebaseempty2 {X : UU} (is : ¬ X) : ischoicebase X.
Proof.
  intros.
  apply (ischoicebaseweqb (weqtoempty is) ischoicebaseempty).
Defined.

Lemma ischoicebasecoprod {X Y : UU}
      (isx : ischoicebase X) (isy : ischoicebase Y) : ischoicebase (coprod X Y).
Proof.
  intros. unfold ischoicebase.
  intros P fs. apply (hinhfun (invweq (weqsecovercoprodtoprod P))).
  apply hinhand.
  apply (isx _ (λ x : X, fs (ii1 x))).
  apply (isy _ (λ y : Y, fs (ii2 y))).
Defined.








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

Notation "'∑' x .. y , P"
  := (carrier_subset (λ x,.. (carrier_subset (λ y, P))..))
  (at level 200, x binder, y binder, right associativity) : subset.
  (* type this in emacs in agda-input method with \sum *)

Delimit Scope subset with subset.

Lemma isinclpr1carrier {X : UU} (A : hsubtype X) : isincl (@pr1carrier X A).
Proof.
  intros. apply (isinclpr1 A (λ x : _, pr2 (A x))).
Defined.

Lemma isasethsubtype (X : UU) : isaset (hsubtype X).
Proof.
  intro X.
  change (isofhlevel 2 (hsubtype X)).
  apply impred; intro x.
  exact isasethProp.
Defined.

Definition totalsubtype (X : UU) : hsubtype X := λ x, htrue.

Definition weqtotalsubtype (X : UU) : totalsubtype X ≃ X.
Proof.
  intro. apply weqpr1. intro. apply iscontrunit.
Defined.

Definition weq_subtypes {X Y : UU} (w : X ≃ Y)
           (S : hsubtype X) (T : hsubtype Y) :
           (∏ x, S x <-> T (w x)) -> carrier S ≃ carrier T.
Proof.
  intros ? ? ? ? ? eq. apply (weqbandf w). intro x. apply weqiff.
  - apply eq.
  - apply propproperty.
  - apply propproperty.
Defined.

(** *** Direct product of two subtypes *)

Definition subtypesdirprod {X Y : UU} (A : hsubtype X) (B : hsubtype Y) :
  hsubtype (X × Y) := λ xy : _, hconj (A (pr1 xy)) (B (pr2 xy)).

Definition fromdsubtypesdirprodcarrier {X Y : UU}
           (A : hsubtype X) (B : hsubtype Y)
           (xyis : subtypesdirprod A B) : dirprod A B.
Proof.
  intros.
  set (xy := pr1 xyis). set (is := pr2 xyis).
  set (x := pr1 xy). set (y := pr2 xy).
  simpl in is. simpl in y.
  apply (dirprodpair (tpair A x (pr1 is)) (tpair B y (pr2 is))).
Defined.

Definition tosubtypesdirprodcarrier {X Y : UU}
           (A : hsubtype X) (B : hsubtype Y)
           (xisyis : dirprod A B) : subtypesdirprod A B.
Proof.
  intros.
  set (xis := pr1 xisyis). set (yis := pr2 xisyis).
  set (x := pr1 xis). set (isx := pr2 xis).
  set (y := pr1 yis). set (isy := pr2 yis).
  simpl in isx. simpl in isy.
  apply (tpair (subtypesdirprod A B) (dirprodpair x y) (dirprodpair isx isy)).
Defined.

Lemma weqsubtypesdirprod {X Y : UU} (A : hsubtype X) (B : hsubtype Y) :
  subtypesdirprod A B ≃ A × B.
Proof.
  intros.
  set (f := fromdsubtypesdirprodcarrier A B).
  set (g := tosubtypesdirprodcarrier A B).
  split with f.
  assert (egf : ∏ a : _, paths (g (f a)) a).
  {
    intro a.
    destruct a as [ xy is ].
    destruct xy as [ x y ].
    destruct is as [ isx isy ].
    apply idpath.
  }
  assert (efg : ∏ a : _, paths (f (g a)) a).
  {
    intro a.
    destruct a as [ xis yis ].
    destruct xis as [ x isx ].
    destruct yis as [ y isy ].
    apply idpath.
  }
  apply (gradth _ _ egf efg).
Defined.

Lemma ishinhsubtypedirprod  {X Y : UU} (A : hsubtype X) (B : hsubtype Y)
      (isa : ishinh A) (isb : ishinh B) : ishinh (subtypesdirprod A B).
Proof.
  intros.
  apply (hinhfun (invweq (weqsubtypesdirprod A B))).
  apply hinhand. apply isa. apply isb.
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
  intros ? ? is e.
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
  intros ? ? ? ? e w.
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

(** *** Elementary implications between properties of relations *)

Lemma istransandirrefltoasymm {X : UU} {R : hrel X}
      (is1 : istrans R) (is2 : isirrefl R) : isasymm R.
Proof.
  intros. intros a b rab rba. apply (is2 _ (is1 _ _ _ rab rba)).
Defined.

Lemma istotaltoiscoasymm {X : UU} {R : hrel X} (is : istotal R) : iscoasymm R.
Proof.
  intros. intros x1 x2. apply (hdisjtoimpl (is _ _)).
Defined.

Lemma isdecreltoisnegrel {X : UU} {R : hrel X} (is : isdecrel R) : isnegrel R.
Proof.
  intros. intros x1 x2.
  destruct (is x1 x2) as [ r | nr ].
  - intro. apply r.
  - intro nnr. destruct (nnr nr).
Defined.

Lemma isantisymmnegtoiscoantisymm {X : UU} {R : hrel X}
      (isdr : isdecrel R) (isr : isantisymmneg R) : iscoantisymm R.
Proof.
  intros. intros x1 x2 nrx12.
  destruct (isdr x2 x1) as [ r | nr ].
  apply (ii1 r). apply ii2. apply (isr _ _ nrx12 nr).
Defined.

Lemma rtoneq {X : UU} {R : hrel X} (is : isirrefl R) {a b : X} (r : R a b) :
  a != b.
Proof.
  intros. intro e. rewrite e in r. apply (is b r).
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

Definition iseqrellogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : iseqrel L) : iseqrel R.
Proof.
  intros.
  apply (dirprodpair (ispologeqf lg (pr1 isl)) (issymmlogeqf lg (pr2 isl))).
Defined.

Definition isirrefllogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : isirrefl L) : isirrefl R.
Proof.
  intros. intros x r. apply (isl _ (pr2 (lg x x) r)).
Defined.

Definition isasymmlogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : isasymm L) : isasymm R.
Proof.
  intros. intros x1 x2 r12 r21.
  apply (isl _ _ (pr2 (lg _ _) r12) (pr2 (lg _ _) r21)).
Defined.

Definition iscoasymmlogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : iscoasymm L) : iscoasymm R.
Proof.
  intros. intros x1 x2 r12.
  apply ((pr1 (lg _ _)) (isl _ _ (negf (pr1 (lg _ _)) r12))).
Defined.

Definition istotallogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : istotal L) : istotal R.
Proof.
  intros. intros x1 x2. set (int := isl x1 x2).
  generalize int. clear int. simpl. apply hinhfun.
  apply (coprodf (pr1 (lg x1 x2)) (pr1 (lg x2 x1))).
Defined.

Definition iscotranslogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : iscotrans L) : iscotrans R.
Proof.
  intros. intros x1 x2 x3 r13.
  set (int := isl x1 x2 x3 (pr2 (lg _ _) r13)). generalize int.
  clear int. simpl. apply hinhfun.
  apply (coprodf (pr1 (lg x1 x2)) (pr1 (lg x2 x3))).
Defined.

Definition isdecrellogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : isdecrel L) : isdecrel R.
Proof.
  intros. intros x1 x2.
  destruct (isl x1 x2) as [ l | nl ].
  - apply (ii1 (pr1 (lg _ _) l)).
  - apply (ii2 (negf (pr2 (lg _ _)) nl)).
Defined.

Definition isnegrellogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : isnegrel L) : isnegrel R.
Proof.
  intros. intros x1 x2 nnr.
  apply ((pr1 (lg _ _)) (isl _ _ (negf (negf (pr2 (lg _ _))) nnr))).
Defined.

Definition isantisymmlogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : isantisymm L) :
  isantisymm R.
Proof.
  intros. intros x1 x2 r12 r21.
  apply (isl _ _ (pr2 (lg _ _) r12) (pr2 (lg _ _) r21)).
Defined.

Definition isantisymmneglogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : isantisymmneg L) :
  isantisymmneg R.
Proof.
  intros. intros x1 x2 nr12 nr21.
  apply (isl _ _ (negf (pr1 (lg _ _)) nr12) (negf (pr1 (lg _ _)) nr21)).
Defined.

Definition iscoantisymmlogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : iscoantisymm L) :
  iscoantisymm R.
Proof.
  intros. intros x1 x2 r12.
  set (int := isl _ _ (negf (pr1 (lg _ _)) r12)). generalize int. clear int.
  simpl. apply (coprodf (pr1 (lg _ _)) (idfun _)).
Defined.

Definition neqchoicelogeqf {X : UU} {L R : hrel X}
           (lg : ∏ x1 x2, L x1 x2 <-> R x1 x2) (isl : neqchoice L) : neqchoice R.
Proof.
  intros. intros x1 x2 ne.
  apply (coprodf (pr1 (lg x1 x2)) (pr1 (lg x2 x1)) (isl _ _ ne)).
Defined.



(** *** Preorderings, partial orderings, and associated types. *)

(* preoderings *)
Definition po (X : UU) : UU := ∑ R : hrel X, ispreorder R.
Definition popair {X : UU} (R : hrel X) (is : ispreorder R) : po X
  := tpair ispreorder R is.
Definition carrierofpo (X : UU) : po X -> (X -> X -> hProp) := @pr1 _ ispreorder.
Coercion carrierofpo : po >-> Funclass.

Definition PreorderedSet : UU := ∑ X : hSet, po X.
Definition PreorderedSetPair (X : hSet) (R :po X) : PreorderedSet
  := tpair _ X R.
Definition carrierofPreorderedSet : PreorderedSet -> hSet := pr1.
Coercion carrierofPreorderedSet : PreorderedSet >-> hSet.
Definition PreorderedSetRelation (X : PreorderedSet) : hrel X := pr1 (pr2 X).

(* partial orderings *)
Definition PartialOrder (X : hSet) : UU := ∑ R : hrel X, isPartialOrder R.
Definition PartialOrderpair {X : hSet} (R : hrel X) (is : isPartialOrder R) :
  PartialOrder X
  := tpair isPartialOrder R is.
Definition carrierofPartialOrder {X : hSet} : PartialOrder X -> hrel X := pr1.
Coercion carrierofPartialOrder : PartialOrder >-> hrel.

Definition Poset : UU := ∑ X, PartialOrder X.
Definition Posetpair (X : hSet) (R : PartialOrder X) : Poset
  := tpair PartialOrder X R.
Definition carrierofposet : Poset -> hSet := pr1.
Coercion carrierofposet : Poset >-> hSet.
Definition posetRelation (X : Poset) : hrel X := pr1 (pr2 X).

Lemma isrefl_posetRelation (X : Poset) : isrefl (posetRelation X).
Proof.
  intros ? x. exact (pr2 (pr1 (pr2 (pr2 X))) x).
Defined.

Lemma istrans_posetRelation (X : Poset) : istrans (posetRelation X).
Proof.
  intros ? x y z l m. exact (pr1 (pr1 (pr2 (pr2 X))) x y z l m).
Defined.

Lemma isantisymm_posetRelation (X : Poset) : isantisymm (posetRelation X).
Proof.
  intros ? x y l m. exact (pr2 (pr2 (pr2 X)) x y l m).
Defined.

Delimit Scope poset with poset.
Notation "m ≤ n" := (posetRelation _ m n) (no associativity, at level 70) :
                      poset.
Definition isaposetmorphism {X Y : Poset} (f : X -> Y)
  := (∏ x x' : X, x ≤ x' -> f x ≤ f x')%poset.
Definition posetmorphism (X Y : Poset) : UU
  := total2 (fun f : X -> Y => isaposetmorphism f).
Definition posetmorphismpair (X Y : Poset) :
  ∏ t : X → Y, isaposetmorphism t → ∑ f : X → Y, isaposetmorphism f
  := tpair (fun f : X -> Y => isaposetmorphism f).
Definition carrierofposetmorphism (X Y : Poset) : posetmorphism X Y -> (X -> Y)
  := @pr1 _ _.
Coercion carrierofposetmorphism : posetmorphism >-> Funclass.

Definition isdec_ordering (X : Poset) : UU
  := ∏ (x y : X), decidable (x ≤ y)%poset.

Lemma isaprop_isaposetmorphism {X Y : Poset} (f : X -> Y) :
  isaprop (isaposetmorphism f).
Proof.
  intros. apply impredtwice; intros. apply impred_prop.
Defined.

(** the preorders on a set form a set *)

Definition isaset_po (X : hSet) : isaset (po X).
  intros.
  unfold po.
  apply (isofhleveltotal2 2).
  { apply isaset_hrel. }
  intros x. apply hlevelntosn. apply isaprop_ispreorder.
Defined.

(** the partial orders on a set form a set *)

Definition isaset_PartialOrder X : isaset (PartialOrder X).
  intros.
  unfold PartialOrder.
  apply (isofhleveltotal2 2).
  { apply isaset_hrel. }
  intros x. apply hlevelntosn. apply isaprop_isPartialOrder.
Defined.

(** poset equivalences *)

Definition isPosetEquivalence {X Y : Poset} (f : X ≃ Y) :=
  isaposetmorphism f × isaposetmorphism (invmap f).

Lemma isaprop_isPosetEquivalence {X Y : Poset} (f : X ≃ Y) :
  isaprop (isPosetEquivalence f).
Proof.
  intros. unfold isPosetEquivalence.
  apply isapropdirprod; apply isaprop_isaposetmorphism.
Defined.

Definition isPosetEquivalence_idweq (X : Poset) : isPosetEquivalence (idweq X).
Proof.
  intros. split.
  - intros x y le. exact le.
  - intros x y le. exact le.
Defined.

Definition PosetEquivalence (X Y : Poset) : UU
  := ∑ f : X ≃ Y, isPosetEquivalence f.

Local Open Scope poset.
Notation "X ≅ Y" := (PosetEquivalence X Y) (at level 60, no associativity) :
                      poset.
(* written \cong in Agda input method *)

Definition posetUnderlyingEquivalence {X Y : Poset} : X ≅ Y -> X ≃ Y := pr1.
Coercion posetUnderlyingEquivalence : PosetEquivalence >-> weq.

Definition identityPosetEquivalence (X : Poset) : PosetEquivalence X X.
Proof.
  intros. exists (idweq X). apply isPosetEquivalence_idweq.
Defined.

Lemma isincl_pr1_PosetEquivalence (X Y : Poset) : isincl (pr1 : X ≅ Y -> X ≃ Y).
Proof.
  intros. apply isinclpr1. apply isaprop_isPosetEquivalence.
Defined.

Lemma isinj_pr1_PosetEquivalence (X Y : Poset) :
  isInjective (pr1 : X ≅ Y -> X ≃ Y).
Proof.
  intros ? ? f g. apply isweqonpathsincl. apply isincl_pr1_PosetEquivalence.
Defined.

(** poset concepts *)

Notation "m < n" := (m ≤ n × m != n)%poset (only parsing) : poset.
Definition isMinimal {X : Poset} (x : X) : UU := ∏ y, x ≤ y.
Definition isMaximal {X : Poset} (x : X) : UU := ∏ y, y ≤ x.
Definition consecutive {X : Poset} (x y : X) : UU
  := x < y × ∏ z, ¬ (x < z × z < y).

Lemma isaprop_isMinimal {X : Poset} (x : X) : isaprop (isMaximal x).
Proof.
  intros. unfold isMaximal. apply impred_prop.
Defined.

Lemma isaprop_isMaximal {X : Poset} (x : X) : isaprop (isMaximal x).
Proof.
  intros. unfold isMaximal. apply impred_prop.
Defined.

Lemma isaprop_consecutive {X : Poset} (x y : X) : isaprop (consecutive x y).
Proof.
  intros. unfold consecutive. apply isapropdirprod.
  - apply isapropdirprod. { apply pr2. } simpl. apply isapropneg.
  - apply impred; intro z. apply isapropneg.
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



(** *** Direct product of two relations *)

Definition hreldirprod {X Y : UU} (RX : hrel X) (RY : hrel Y) :
  hrel (X × Y)
  := λ xy xy' : dirprod X Y, hconj (RX (pr1 xy) (pr1 xy'))
                                    (RY (pr2 xy) (pr2 xy')).

Definition istransdirprod {X Y : UU} (RX : hrel X) (RY : hrel Y)
           (isx : istrans RX) (isy : istrans RY) :
  istrans (hreldirprod RX RY)
  := λ xy1 xy2 xy3 : _,
       λ is12 : _ ,
         λ is23 : _,
           dirprodpair (isx _ _ _ (pr1 is12) (pr1 is23))
                       (isy _ _ _ (pr2 is12) (pr2 is23)).

Definition isrefldirprod {X Y : UU} (RX : hrel X) (RY : hrel Y)
           (isx : isrefl RX) (isy : isrefl RY) : isrefl (hreldirprod RX RY)
  := λ xy : _, dirprodpair (isx _) (isy _).

Definition issymmdirprod {X Y : UU} (RX : hrel X) (RY : hrel Y)
           (isx : issymm RX) (isy : issymm RY) : issymm (hreldirprod RX RY)
  := λ xy1 xy2 : _, λ is12 : _, dirprodpair (isx _ _ (pr1 is12))
                                              (isy _ _ (pr2 is12)).

Definition eqreldirprod {X Y : UU} (RX : eqrel X) (RY : eqrel Y) :
  eqrel (X × Y)
  := eqrelconstr (hreldirprod RX RY)
                 (istransdirprod _ _ (eqreltrans RX) (eqreltrans RY))
                 (isrefldirprod  _ _ (eqrelrefl RX) (eqrelrefl RY))
                 (issymmdirprod  _ _ (eqrelsymm RX) (eqrelsymm RY)).


(** *** Negation of a relation and its properties *)

Definition negrel {X : UU} (R : hrel X) : hrel X
  := λ x x', hProppair (¬ R x x') (isapropneg _). (* uses [funextemptyAxiom] *)

Lemma istransnegrel {X : UU} (R : hrel X) (isr : iscotrans R) :
  istrans (negrel R).
(* uses [funextfun] and [funextemptyAxiom] *)
Proof.
  intros. intros x1 x2 x3 r12 r23.
  apply (negf (isr x1 x2 x3)).
  apply (toneghdisj (dirprodpair r12 r23)).
Defined.

Lemma iscotrans_to_istrans_negReln {X : UU} {R : hrel X} (NR : negReln R) :
  isdeccotrans R -> istrans NR.
(* uses no axioms; compare to istransnegrel *)
Proof.
  intros ? ? ? i ? ? ? nxy nyz. apply neg_to_negProp.
  apply (negf (i x1 x2 x3)). intro c. induction c as [c|c].
  - exact (negProp_to_neg nxy c).
  - exact (negProp_to_neg nyz c).
Defined.

Lemma isasymmnegrel {X : UU} (R : hrel X) (isr : iscoasymm R) :
  isasymm (negrel R).
Proof.
  intros. intros x1 x2 r12 r21. apply (r21 (isr _ _ r12)).
Defined.

Lemma iscoasymmgenrel {X : UU} (R : hrel X) (isr : isasymm R) :
  iscoasymm (negrel R).
Proof.
  intros. intros x1 x2 nr12. apply (negf (isr _ _) nr12).
Defined.

Lemma isdecnegrel {X : UU} (R : hrel X) (isr : isdecrel R) :
  isdecrel (negrel R).
(* uses [funextemptyAxiom] *)
Proof.
  intros. intros x1 x2.
  destruct (isr x1 x2) as [ r | nr ].
  - apply ii2. apply (todneg _ r).
  - apply (ii1 nr).
Defined.

Lemma isnegnegrel {X : UU} (R : hrel X) : isnegrel (negrel R).
Proof.
  intros. intros x1 x2.
  apply (negf (todneg (R x1 x2))).
Defined.

Lemma isantisymmnegrel {X : UU} (R : hrel X) (isr : isantisymmneg R) :
  isantisymm (negrel R).
Proof.
  intros. apply isr.
Defined.

(** *** Boolean representation of decidable equality *)

Definition eqh {X : UU} (is : isdeceq X) : hrel X
  := λ x x', hProppair (booleq is x x' = true)
                        (isasetbool (booleq is x x') true).

Definition neqh {X : UU} (is : isdeceq X) : hrel X
  := λ x x', hProppair (booleq is x x' = false)
                        (isasetbool (booleq is x x') false).

Lemma isrefleqh {X : UU} (is : isdeceq X) : isrefl (eqh is).
Proof.
  intros. unfold eqh. unfold booleq.
  intro x. destruct (is x x) as [ e | ne ].
  - simpl. apply idpath.
  - destruct (ne (idpath x)).
Defined.

Definition weqeqh {X : UU} (is : isdeceq X) (x x' : X) :
  (x = x') ≃ (eqh is x x').
Proof.
  intros. apply weqimplimpl.
  - intro e. destruct e. apply isrefleqh.
  - intro e. unfold eqh in e. unfold booleq in e.
    destruct (is x x') as [ e' | ne' ].
    + apply e'.
    + destruct (nopathsfalsetotrue e).
  - unfold isaprop. unfold isofhlevel. apply (isasetifdeceq X is x x').
  - unfold eqh. simpl. unfold isaprop. unfold isofhlevel.
    apply (isasetbool _ true).
Defined.

Definition weqneqh {X : UU} (is : isdeceq X) (x x' : X) :
  (x != x') ≃ (neqh is x x').
Proof.
  intros. unfold neqh. unfold booleq. apply weqimplimpl.
  - destruct (is x x') as [ e | ne ].
    + intro ne. destruct (ne e).
    + intro ne'. simpl. apply idpath.
  - destruct (is x x') as [ e | ne ].
    + intro tf. destruct (nopathstruetofalse tf).
    + intro. exact ne.
  - apply (isapropneg).
  - simpl. unfold isaprop. unfold isofhlevel. apply (isasetbool _ false).
Defined.






(** *** Restriction of a relation to a subtype *)

Definition resrel {X : UU} (L : hrel X) (P : hsubtype X) : hrel P
  := λ p1 p2, L (pr1 p1) (pr1 p2).

Definition istransresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : istrans L) : istrans (resrel L P).
Proof.
  intros. intros x1 x2 x3 r12 r23.
  apply (isl _ (pr1 x2) _ r12 r23).
Defined.

Definition isreflresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : isrefl L) : isrefl (resrel L P).
Proof.
  intros. intro x. apply isl.
Defined.

Definition issymmresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : issymm L) : issymm (resrel L P).
Proof.
  intros. intros x1 x2 r12. apply isl. apply r12.
Defined.

Definition isporesrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : ispreorder L) : ispreorder (resrel L P).
Proof.
  intros.
  apply (dirprodpair (istransresrel L P (pr1 isl))
                     (isreflresrel L P (pr2 isl))).
Defined.

Definition iseqrelresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : iseqrel L) : iseqrel (resrel L P).
Proof.
  intros.
  apply (dirprodpair (isporesrel L P (pr1 isl)) (issymmresrel L P (pr2 isl))).
Defined.

Definition isirreflresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : isirrefl L) : isirrefl (resrel L P).
Proof.
  intros. intros x r. apply (isl _ r).
Defined.

Definition isasymmresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : isasymm L) : isasymm (resrel L P).
Proof.
  intros. intros x1 x2 r12 r21. apply (isl _ _ r12 r21).
Defined.

Definition iscoasymmresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : iscoasymm L) : iscoasymm (resrel L P).
Proof.
  intros. intros x1 x2 r12. apply (isl _ _ r12).
Defined.


Definition istotalresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : istotal L) : istotal (resrel L P).
Proof.
  intros. intros x1 x2. apply isl.
Defined.

Definition iscotransresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : iscotrans L) : iscotrans (resrel L P).
Proof.
  intros. intros x1 x2 x3 r13. apply (isl _ _ _ r13).
Defined.

Definition isdecrelresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : isdecrel L) : isdecrel (resrel L P).
Proof.
  intros. intros x1 x2. apply isl.
Defined.

Definition isnegrelresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : isnegrel L) : isnegrel (resrel L P).
Proof.
  intros. intros x1 x2 nnr. apply (isl _ _ nnr).
Defined.

Definition isantisymmresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : isantisymm L) : isantisymm (resrel L P).
Proof.
  intros. intros x1 x2 r12 r21.
  apply (invmaponpathsincl _ (isinclpr1carrier _) _ _ (isl _ _ r12 r21)).
Defined.

Definition isantisymmnegresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : isantisymmneg L) : isantisymmneg (resrel L P).
Proof.
  intros. intros x1 x2 nr12 nr21.
  apply (invmaponpathsincl _ (isinclpr1carrier _) _ _ (isl _ _ nr12 nr21)).
Defined.

Definition iscoantisymmresrel {X : UU} (L : hrel X) (P : hsubtype X)
           (isl : iscoantisymm L) : iscoantisymm (resrel L P).
Proof.
  intros. intros x1 x2 r12. destruct (isl _ _ r12) as [ l | e ].
  - apply (ii1 l).
  - apply ii2. apply (invmaponpathsincl _ (isinclpr1carrier _) _ _ e).
Defined.

Definition  neqchoiceresrel {X : UU} (L : hrel X) (P : hsubtype X)
            (isl : neqchoice L) : neqchoice (resrel L P).
Proof.
  intros. intros x1 x2 ne.
  set (int := negf (invmaponpathsincl _ (isinclpr1carrier P) _ _) ne).
  apply (isl _ _ int).
Defined.



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
intros X R A.
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
  intros X R. apply isinclpr1. intro x0. apply isapropiseqclass.
Defined.

Definition setquottouu0 {X : UU} (R : hrel X) (a : setquot R)
  := carrier (pr1 a).
Coercion setquottouu0 : setquot >-> Sortclass.

Theorem isasetsetquot {X : UU} (R : hrel X) : isaset (setquot R).
Proof.
  intros X R.
  apply (isasetsubset (@pr1 _ _) (isasethsubtype X)).
  apply isinclpr1; intro x.
  apply isapropiseqclass.
Defined.

Definition setquotinset {X : UU} (R : hrel X) : hSet :=
  hSetpair _ (isasetsetquot R).

Theorem setquotpr {X : UU} (R : eqrel X) : X -> setquot R.
Proof.
  intros X R X0.
  set (rax := eqrelrefl R).
  set (sax := eqrelsymm R).
  set (tax := eqreltrans R).
  apply (tpair _ (λ x : X, R X0 x)).
  split.
  - exact (hinhpr (tpair _ X0 (rax X0))).
  - split; intros x1 x2 X1 X2.
    + exact (tax X0 x1 x2 X2 X1).
    + exact (tax x1 X0 x2 (sax X0 x1 X1) X2).
Defined.

Lemma setquotl0 {X : UU} (R : eqrel X) (c : setquot R) (x : c) :
  setquotpr R (pr1 x) = c.
Proof.
  intros X R c x.
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
