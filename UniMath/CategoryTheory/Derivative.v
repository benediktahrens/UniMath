(** **********************************************************
Contents:
        - "maybe" monad (binary coproduct with a fixed object)
        - distributive laws for pairs of monads
          - in particular: the distributive law for the maybe monad and any monad
        - composition of two monads with a distributive law
          - in particular: derivative of a monad (composing with maybe)
        - monad morphism from the first composand to the composition of monads
          - in particular: monad morphism from a monad to its derivative
        - left module over a monad T obtained by composing a monad having a distributive law with T
          - in particular: the derivative of a left module over a monad

Written by: Joseph Helfer (May 2017)

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.LModules.

Local Open Scope cat.

(** * Definition of distributive laws for Monads and composition of Monads
 cf. Beck "Distributive laws" (1969) *)
Section comp_def.

Context {C : precategory} {S T : Monad C}.

(** distributivity law for a pair of monads *)
Definition monad_dist_laws (a : T ∙ S ⟹ S ∙ T) :=
  (((∏ x : C, η S (T x) · a x = #T (η S x)) ×
    (∏ x : C, #S (η T x) · a x = η T (S x))) ×
    (∏ x : C, a (T x) · #T (a x) · μ T (S x) = #S (μ T x) · a x)) ×
    (∏ x : C, #S (a x) · a (S x) · #T (μ S x) = μ S (T x) · a x).

Definition monad_dist_law1 {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) := (pr1 (pr1 (pr1 l))).
Definition monad_dist_law2 {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) := (pr2 (pr1 (pr1 l))).
Definition monad_dist_law3 {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) := (pr2 (pr1 l)).
Definition monad_dist_law4 {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) := pr2 l.

(** composition of monads with a distributive law *)
Definition monad_comp_mu (a : T ∙ S ⟹ S ∙ T) : (S ∙ T ∙ S ∙ T) ⟹ (S ∙ T) :=
  nat_trans_comp _ _ _ (post_whisker (pre_whisker S a) T)
                       (nat_trans_comp _ _ _ (pre_whisker (S ∙ S) (μ T)) (post_whisker (μ S) T)).

Definition monad_comp_eta (a : T ∙ S ⟹ S ∙ T): functor_identity C ⟹ S ∙ T :=
  nat_trans_comp _ _ _ (η S) (pre_whisker S (η T)).

Definition monad_comp_data (a : T ∙ S ⟹ S ∙ T) : Monad_data C :=
  (tpair _ (tpair _ (S ∙ T) (monad_comp_mu a)) (monad_comp_eta a)).

(** Below are the proofs of the monad laws for the composition of monads. We prove them as separate
    lemmas not only because they are somewhat lengthy, but also for the following reason: the μ and
    η for this monad are defined via operations on natural transformations, rather than their value
    being given explicitly at each object. However, for the proofs, it is desirable to have these
    explicit expressions; the easiest way to accomplish this is to write out the statements by hand
    in the desired form (as ugly as they may be).

    This is also done for the same reason later in the file, where the proofs of the individual
    lemmas are not as lengthy.
*)

(**
Here is the diagram corresponding to this proof. The outside of the diagram represents the equation
to be proved. The numbers indicate the order in which the sub-diagrams are used.
TSTSx ---------------> TTSSx ----------->  TSSx  ------------> TSx
  ^     #T (a (Sx))     ^     μ T (SSx)     ^     #T (μ S x)   ^
  |                     |                  /                  /
  |η T (STSx)           |η T (TSSx)       /id                /
  |                 1   |            3   /                  /
           a (Sx)                       /                  /
 STSx  --------------> TSSx ------------         4        /
  ^                     ^                                /
  |             2      /#T (η S (Sx))                   /
  |η S (TSx)          /                                /
  | _________________/                                /
  |/                               id                /
 TSx ------------------------------------------------
*)
Local Lemma monad_comp_law1 {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) : ∏ x : C,
  (η S (T (S x))) · (η T (S (T (S x)))) · (#T (a (S x)) · (μ T (S (S x)) · #T (μ S x))) =
  identity (T (S x)).
Proof.
  intro x.
  (* 1 *)
  rewrite <- assoc.
  rewrite !(assoc ((η T) (S (T (S x))))).
  rewrite <- (nat_trans_ax (η T) (S (T (S x)))).
  (* 2 *)
  simpl.
  rewrite !assoc.
  change ((η S) (T (S x)) · a (S x) · (η T) (T (S (S x))) · (μ T) (S (S x)) · # T ((μ S) x)
          = identity (T (S x))).
  rewrite (monad_dist_law1 l).
  (* 3 *)
  rewrite <- (assoc (# T ((η S) (S x)))).
  change (# T ((η S) (S x)) · ((η T) (T (S (S x))) · (μ T) (S (S x))) · # T ((μ S) x)
          = identity (T (S x))).
  rewrite Monad_law1.
  (* 4 *)
  rewrite id_right.
  rewrite <- functor_comp.
  rewrite <- functor_id.
  change (# T ((η S) (S x) · (μ S) x) = # T (identity (S x))).
  now rewrite Monad_law1.
Defined.

(**
The diagram for this proof (see above for explanation):
TSTSx ---------------> TTSSx ----------->  TSSx  ------------> TSx
  ^     #T (a (Sx))     ^     μ T (SSx)     ^     #T (μ S x)   ^
  |                 1  /             2     /                  /
  |#T #S (η T (Sx))   /                   /id                /
  |                  /#T (η T (SSx))     /                  /
  |  _______________/                   /                  /
  | /                                  /                  /
 TSSx  --------------------------------         3        /
  ^                                                     /
  |                                                    /
  |#T #S (η S x)                                      /
  |                                      id          /
 TSx ------------------------------------------------
*)
Local Lemma monad_comp_law2 {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) : ∏ x : C,
  #T (#S ((η S x) · (η T (S x)))) · (#T (a (S x)) · (μ T (S (S x)) · #T (μ S x))) =
  identity (T (S x)).
Proof.
  intro x.
  (* 1 *)
  rewrite !assoc.
  rewrite <- functor_comp.
  rewrite (functor_comp S).
  rewrite <- !assoc.
  change (# T (# S ((η S) x) · (# S ((η T) (S x)) · a (S x))) · ((μ T) (S (S x)) · # T ((μ S) x))
          = identity (T (S x))).
  rewrite (monad_dist_law2 l).
  (* 2 *)
  rewrite functor_comp.
  rewrite <- assoc.
  rewrite (assoc (# T ((η T) (S (S x))))).
  rewrite Monad_law2.
  (* 3 *)
  rewrite id_left.
  rewrite <- functor_comp.
  rewrite <- functor_id.
  change (# T (# S ((η S) x) · (μ S) x) = # T (identity (S x))).
  now rewrite (@Monad_law2 C S x).
Defined.

(** Here, more enlightening than a diagram is just the "strategy" of the proof: each side of the
    equation consists of some applications of the monad multiplications μ T and μ S and the
    distributive law 'a'. The strategy is - (1) using repeated applications of the third and fourth
    axioms for the distributive law and the naturality of μ T, μ S, and 'a' - to arrange for all the
    applications of 'a' to come first, and then the applications μ T and μ S. Thus, both sides are
    transformed to a composite TSTSTSx --> TTTSSSx -> TSx; then (2) the first composands are equal
    by the naturality of 'a', and the second composands are equal by the naturality and
    associativity of μ T and μ S.
*)
Local Lemma monad_comp_law3 {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) : ∏ x : C,
  #T (#S (#T (a (S x)) · (μ T (S (S x)) · #T (μ S x)))) ·
   (#T (a (S x)) · (μ T (S (S x)) · #T (μ S x))) =
  #T (a (S (T (S x)))) · (μ T (S (S (T (S x)))) · #T (μ S (T (S x)))) ·
   (#T (a (S x)) · (μ T (S (S x)) · #T (μ S x))).
Proof.
  intro x.
  (* 1 *)
  rewrite assoc.
  rewrite <- functor_comp.
  rewrite <- nat_trans_ax.
  do 2 rewrite (functor_comp S).
  rewrite (assoc _ _ (#S ((μ T) (S x)))).
  rewrite <- (assoc _ (#S ((μ T) (S x))) _).
  rewrite <- (monad_dist_law3 l).
  rewrite <- assoc.
  rewrite <- (assoc (a (T (S x)))).
  rewrite (assoc _ (a (T (S x)))).
  simpl.
  change(
      # T (# S (# T (a (S x))) · (# (T ∙ S) (# T ((μ S) x)) ·
                                    a (T (S x)) · (# T (a (S x)) · (μ T) (S (S x))))) ·
        (# T (# T ((μ S) x)) · (μ T) (S x)) =
      # T (a (S (T (S x)))) · ((μ T) (S (S (T (S x)))) · # T ((μ S) (T (S x)))) ·
                                             (# T (a (S x)) · (# T (# T ((μ S) x)) · (μ T) (S x)))).
  rewrite nat_trans_ax.
  rewrite <- assoc.
  rewrite (assoc _ (# T (a (S x)))).
  change (# T (# S (# T (a (S x))) · (a (T (S (S x))) · (# T (# S (# T ((μ S) x))) ·
                                               # T (a (S x)) · (μ T) (S (S x))))) ·
            (# T (# T ((μ S) x)) · (μ T) (S x)) =
          # T (a (S (T (S x)))) · ((μ T) (S (S (T (S x)))) · # T ((μ S) (T (S x)))) ·
            (# T (a (S x)) · (# T (# T ((μ S) x)) · (μ T) (S x)))).
  rewrite <- (functor_comp T).
  change (# T (# S (# T (a (S x))) · (a (T (S (S x))) · (# T (# (T ∙ S) ((μ S) x) ·
                                                 a (S x)) ·
                                               (μ T) (S (S x))))) ·
  (# T (# T ((μ S) x)) · (μ T) (S x)) =
  # T (a (S (T (S x)))) · ((μ T) (S (S (T (S x)))) · # T ((μ S) (T (S x)))) ·
  (# T (a (S x)) · (# T (# T ((μ S) x)) · (μ T) (S x)))).
  rewrite nat_trans_ax.
  rewrite <- assoc.
  rewrite <- (assoc _ (# T ((μ S) (T (S x))))).
  rewrite (assoc (# T ((μ S) (T (S x))))).
  rewrite <- functor_comp.
  rewrite <- (monad_dist_law4 l).
  rewrite (assoc ((μ T) (S (S (T (S x)))))).
  rewrite <- (nat_trans_ax (μ T)).
  (* 2 *)
  rewrite !functor_comp.
  rewrite !assoc.
  rewrite <- functor_comp.
  change (# T (# (T ∙ S) (a (S x)) · a (T (S (S x)))) · # T (# T (a ((S ∙ S) x))) ·
             # T (# T (# (S ∙ T) ((μ S) x))) · # T ((μ T) (S (S x))) ·
             # T (# T ((μ S) x)) · (μ T) (S x) =
           # T (a (S (T (S x)))) · # (T ∙ T) (# S (a (S x))) ·
             # (T ∙ T) (a (S (S x))) · # (T ∙ T) (# T ((μ S) (S x))) ·
             (μ T) ((S ∙ T) (S x)) · # T (# T ((μ S) x)) · (μ T) (S x)).
  rewrite nat_trans_ax.
  do 2 rewrite <- assoc.
  rewrite (assoc (# T ((μ T) (S (S x))))).
  rewrite <- !(functor_comp T ((μ T) (S (S x)))).
  rewrite <- (nat_trans_ax (μ T)).
  rewrite !functor_comp.
  rewrite !assoc.
  simpl.
  rewrite <- (assoc _ (# T (# T (# T (# S ((μ S) x)))))).
  rewrite <- !functor_comp.
  rewrite (@Monad_law3 C S).
  rewrite !functor_comp.
  rewrite !assoc.
  rewrite <- (assoc _ (# T ((μ T) (S x)))).
  rewrite (@Monad_law3 C T).
  apply pathsinv0.
  rewrite <- (assoc _ ((μ T) (T (S (S x))))).
  rewrite <- nat_trans_ax.
  now rewrite !assoc.
Defined.

Definition monad_comp {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) : Monad C :=
  (monad_comp_data a,,
  dirprodpair (dirprodpair (monad_comp_law1 l) (monad_comp_law2 l)) (monad_comp_law3 l)).

(** morphism from the factor T to the composite S ∙ T of two monads *)
Definition monad_to_comp_data {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) :
  T ⟹ monad_comp l := post_whisker (η S) T.

(** We prove the monad morphism laws as separate lemmas for the reason explained in the comment
    near the beginning of the file *)

(** The diagram for this proof (see above for explanation):
TTx------------------------------------------------------------------->Tx
 | \                                      μ T x                         |
 |  ¯¯¯¯¯¯¯¯¯¯¯¯¯\                                                      |
 |#T (η S (Tx))   \#T (#T (η S x)                 5           #T (η S x)|
 |              2  \                                                    |
 v    #T (a x)      v        id                     μ T (Sx)            |
TSTx----------------TTSx------------------TTSx---------------------     |
 |                    |                   ^                        \    |
 |#T #S #T (η S x)    |#T #T #S (η S x)  /                          \   |
 |                    |    _____________/ #T #T (μ S x)     3        \  |
 |         1          | 4 /                                           \ |
 v                    v  /                                            v v
TSTSx-------------->TTSSx-------------------------->TSSx-------------->TSx
      #T (a (Sx))                  μ T (SSx)               #T (μ S x)
*)
Local Lemma monad_to_comp_law1 {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) :
  ∏ x : C,
        μ T x · #T (η S x) =
        #T (η S (T x)) · #T (#S (#T (η S x))) ·
         (#T (a (S x)) · (μ T (S (S x)) · #T (μ S x))).
Proof.
  intro x.
  (* 1 *)
  rewrite <- assoc.
  rewrite (assoc (# T (# S (# T ((η S) x))))).
  rewrite <- functor_comp.
  apply pathsinv0.
  change (# T ((η S) (T x)) · (# T (# (T ∙ S) ((η S) x) · a (S x)) ·
                                 ((μ T) (S (S x)) · # T ((μ S) x))) =
          (μ T) x · # T ((η S) x)).
  rewrite nat_trans_ax.
  (* 2 *)
  rewrite functor_comp.
  rewrite !assoc.
  rewrite <- functor_comp.
  rewrite (monad_dist_law1 l).
  (* 3 *)
  rewrite <- !assoc.
  rewrite <- (nat_trans_ax (μ T) (S (S x))).
  (* 4 *)
  rewrite (assoc (# T (# T (# S ((η S) x))))).
  simpl.
  rewrite <- !functor_comp.
  change (# T (# T ((η S) x)) · (# T (# T (# S ((η S) x) · (μ S) x)) · (μ T) (S x)) =
          (μ T) x · # T ((η S) x)).
  rewrite Monad_law2.
  (* 5 *)
  rewrite !functor_id.
  rewrite id_left.
  now rewrite <- (nat_trans_ax (μ T) x).
Defined.

Local Definition monad_to_comp_law2 {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) :
  ∏ x : C, η T x · #T (η S x) = η S x · (η T (S x)).
Proof.
  intro x.
  now rewrite <- (nat_trans_ax (η T) x ).
Defined.

Definition monad_to_comp {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) :
  Monad_Mor T (monad_comp l) :=
  (monad_to_comp_data l,, dirprodpair (monad_to_comp_law1 l) (monad_to_comp_law2 l)).

End comp_def.

(** * Definition of the "Maybe" monad (coproduct with a fixed object) *)
Section maybe_def.

Context {C : precategory} (o : C) (co : BinCoproducts C).

Definition maybe_functor : functor C C :=
  constcoprod_functor2 co o.

Definition maybe_on_arrows_good {a b : C} :
  ∏ f : a --> b, #maybe_functor f =
BinCoproductOfArrows C (co a o) (co b o) f (identity o) := (λ f, idpath _).

Definition maybe_mu : maybe_functor ∙ maybe_functor ⟹ maybe_functor :=
  coproduct_nat_trans C C co maybe_functor (constant_functor C C o) maybe_functor
                      (nat_trans_id maybe_functor)
                      (coproduct_nat_trans_in2 C C co (functor_identity C)
                                               (constant_functor C C o)).

Definition maybe_eta : functor_identity C ⟹ maybe_functor :=
  coproduct_nat_trans_in1 C C co (functor_identity C) (constant_functor C C o).

Definition maybe_monad_data : Monad_data C := (maybe_functor,, maybe_mu),, maybe_eta.

(** We prove the monad laws as separate lemmas for the reason explained in the comment
    near the beginning of the file *)

Local Lemma maybe_monad_law1 : ∏ c : C,
BinCoproductIn1 C (co (co c o) o) ·
BinCoproductArrow C _ (identity (co c o)) (BinCoproductIn2 C (co c o)) =
identity (co c o).
Proof.
  intro c.
  now rewrite BinCoproductIn1Commutes.
Defined.

Local Lemma maybe_monad_law2 : ∏ c : C,
BinCoproductOfArrows C (co c o) (co (co c o) o)
 (BinCoproductIn1 C (co c o)) (identity o) ·
BinCoproductArrow C _ (identity (co c o)) (BinCoproductIn2 C (co c o)) =
identity (co c o).
Proof.
  intro c.
  now rewrite precompWithBinCoproductArrow, id_left,
              <- (id_right (BinCoproductIn2 C (co c o))), <- BinCoproductArrowEta.
Defined.

Local Lemma maybe_monad_law3 : ∏ c : C,
BinCoproductOfArrows C (co (co (co c o) o) o) (co (co c o) o)
 (BinCoproductArrow C (co (co c o) o) (identity (co c o)) (BinCoproductIn2 C (co c o)))
 (identity o) ·
BinCoproductArrow C _ (identity (co c o)) (BinCoproductIn2 C (co c o)) =
BinCoproductArrow C _ (identity (co (co c o) o)) (BinCoproductIn2 C (co (co c o) o)) ·
 BinCoproductArrow C _ (identity (co c o)) (BinCoproductIn2 C (co c o)).
Proof.
  intro c.
  now rewrite precompWithBinCoproductArrow, postcompWithBinCoproductArrow,
              !id_right, postcompWithBinCoproductArrow,
              !id_left, BinCoproductIn2Commutes.
Defined.

Definition maybe_monad : Monad C :=
  (maybe_monad_data,,
  dirprodpair (dirprodpair maybe_monad_law1 maybe_monad_law2) maybe_monad_law3).

(** Definition of the derivative of a monad, i.e. precomposing with the maybe monad *)
Section deriv_def.

Definition functor_deriv {D : precategory}
           (T : functor C D) : functor C D := maybe_monad ∙ T.

(** The distributive law for any monad with the Maybe monad. This is the obvious map
    (TX + Y) -> T (X + Y) - i.e., T(in1) on the first component and (in2 · η T)
    on the second component *)
Definition deriv_dist (T : Monad C) : (T ∙ maybe_monad) ⟹ (maybe_monad ∙ T) :=
  coproduct_nat_trans C C co T (constant_functor C C o) (functor_deriv T)
                             (post_whisker (coproduct_nat_trans_in1 C C co (functor_identity C)
                                                                    (constant_functor C C o)) T)
                             (nat_trans_comp _ _ _
                                             (coproduct_nat_trans_in2 C C co (functor_identity C)
                                                                      (constant_functor C C o))
                                             (pre_whisker maybe_monad (η T))).

(** We prove the distributive law axioms as separate lemmas for the reason explained in the comment
    near the beginning of the file *)

Local Lemma deriv_dist_law1 (T : Monad C) : ∏ x : C,
  BinCoproductIn1 C (co (T x) o) ·
  BinCoproductArrow C _ (#T (BinCoproductIn1 C _)) (BinCoproductIn2 C _ · η T _) =
  #T (BinCoproductIn1 C (co x o)).
Proof.
  intro x.
  now rewrite BinCoproductIn1Commutes.
Defined.

Local Lemma deriv_dist_law2 (T : Monad C) : ∏ x : C,
  BinCoproductOfArrows C (co x o) (co (T x) o) (η T x) (identity o) ·
  BinCoproductArrow C _ (#T (BinCoproductIn1 C _)) (BinCoproductIn2 C _ · η T (co x o)) =
  η T (co x o).
Proof.
  intro x.
  rewrite precompWithBinCoproductArrow.
  rewrite id_left.
  change (BinCoproductArrow C (co x o) ((η T) x · # T (BinCoproductIn1 C (co x o)))
    (BinCoproductIn2 C (co x o) · (η T) (co x o)) = (η T) (co x o)).
  rewrite <- nat_trans_ax.
  now rewrite <- BinCoproductArrowEta.
Defined.

Local Lemma deriv_dist_law3 (T : Monad C) : ∏ x : C,
  BinCoproductArrow C _ (#T (BinCoproductIn1 C _)) (BinCoproductIn2 C _ · η T (co (T x) o)) ·
  #T (BinCoproductArrow C _ (#T (BinCoproductIn1 C _)) (BinCoproductIn2 C _ · η T (co x o))) ·
  μ T (co x o) =
  BinCoproductOfArrows C (co (T (T x)) o) (co (T x) o) (μ T x) (identity o) ·
  BinCoproductArrow C _ (#T (BinCoproductIn1 C _)) (BinCoproductIn2 C _ · η T (co x o)).
Proof.
  intro x.
  rewrite postcompWithBinCoproductArrow.
  rewrite postcompWithBinCoproductArrow.
  rewrite <- functor_comp.
  rewrite BinCoproductIn1Commutes.
  rewrite <- (assoc (BinCoproductIn2 C (co (T x) o))).
  rewrite <- (nat_trans_ax (η T) (co (T x) o)).
  rewrite (assoc (BinCoproductIn2 C (co (T x) o))).
  rewrite <- (assoc _ ((η T) (T (co x o)))).
  rewrite Monad_law1.
  simpl.
  rewrite BinCoproductIn2Commutes.
  rewrite precompWithBinCoproductArrow.
  rewrite id_left.
  rewrite id_right.
  now rewrite <- (nat_trans_ax (μ T) x).
Defined.

Local Lemma deriv_dist_law4 (T : Monad C) : ∏ x : C,
  BinCoproductOfArrows C (co (co (T x) o) o) (co (T (co x o)) o)
                         (BinCoproductArrow C _ (#T (BinCoproductIn1 C _))
                         (BinCoproductIn2 C _ · η T (co x o))) (identity o) ·
  BinCoproductArrow C _ (#T (BinCoproductIn1 C _)) (BinCoproductIn2 C _ · η T (co (co x o) o)) ·
  #T (BinCoproductArrow C _ (identity _) (BinCoproductIn2 C _)) =
  BinCoproductArrow C (co (co (T x) o) o) (identity (co (T x) o)) (BinCoproductIn2 C _) ·
  BinCoproductArrow C (co (T x) o) (#T (BinCoproductIn1 C _))
                      (BinCoproductIn2 C (co x o) · η T (co x o)).
Proof.
  intro x.
  rewrite precompWithBinCoproductArrow.
  rewrite postcompWithBinCoproductArrow.
  rewrite <- (assoc _ (# T (BinCoproductIn1 C (co (co x o) o)))).
  rewrite <- functor_comp.
  rewrite BinCoproductIn1Commutes.
  rewrite functor_id.
  rewrite id_right.
  rewrite id_left.
  rewrite <- assoc.
  rewrite <- (nat_trans_ax (η T) (co (co x o) o)).
  simpl.
  rewrite assoc.
  rewrite BinCoproductIn2Commutes.
  rewrite postcompWithBinCoproductArrow.
  rewrite id_left.
  now rewrite BinCoproductIn2Commutes.
Defined.

Definition deriv_dist_is_monad_dist (T : Monad C) : monad_dist_laws (deriv_dist T) :=
  dirprodpair (dirprodpair (dirprodpair (deriv_dist_law1 T) (deriv_dist_law2 T))
                           (deriv_dist_law3 T))
              (deriv_dist_law4 T).

Definition monad_deriv (T: Monad C) : Monad C := monad_comp (deriv_dist_is_monad_dist T).

(** the morphism from a monad to its derivative *)
Definition monad_to_deriv (T : Monad C) : Monad_Mor T (monad_deriv T) :=
  monad_to_comp (deriv_dist_is_monad_dist T).

(** derivative of a left module over a monad *)
Lemma LModule_comp_law1 {D : precategory} {T : Monad C} {S : Monad C}
      {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) (L : LModule T D) : ∏ x : C,
  #L (#S (η T x)) · (#L (a x) · lm_mult T L (S x)) = identity (L (S x)).
Proof.
  intro x.
  now rewrite assoc, <- functor_comp, (monad_dist_law2 l), (LModule_law1 T (S x)).
Defined.

Lemma LModule_comp_law2 {D : precategory} {T : Monad C} {S : Monad C}
      {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) (L : LModule T D) : ∏ x : C,
  #L (#S (μ T x)) · (#L (a x) · lm_mult T L (S x)) =
  (#L (a (T x)) · lm_mult T L (S (T x))) · (#L (a x) · lm_mult T L (S x)).
Proof.
  intro x.
  rewrite assoc.
  rewrite <- functor_comp.
  rewrite <- (monad_dist_law3 l).
  rewrite !functor_comp.
  rewrite <- assoc.
  rewrite (LModule_law2 T (S x)).
  rewrite assoc.
  rewrite <- (assoc _ (#L (#T (a x)))).
  change(# L (a (T x)) · (# (T ∙ L) (a x) · (lm_mult T L) (T (S x))) ·
           (lm_mult T L) (S x) =
         # L (a (T x)) · (lm_mult T L) (S (T x)) · (# L (a x) · (lm_mult T L) (S x))).
  rewrite (nat_trans_ax (lm_mult T L) _ _ _).
  now rewrite !assoc.
Defined.

Definition LModule_comp_data {D : precategory} {T : Monad C} {S : Monad C} (a : T ∙ S ⟹ S ∙ T)
                                                  (L : LModule T D) : LModule_data T D :=
  (S ∙ L,, nat_trans_comp _ _ _ (post_whisker a L) (pre_whisker S (lm_mult T L))).

Definition LModule_comp_laws {D : precategory} {T : Monad C} {S : Monad C}
      {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a) (L : LModule T D) :
  (LModule_laws T (LModule_comp_data a L)) := dirprodpair (LModule_comp_law1 l L)
                                                          (LModule_comp_law2 l L).

Definition LModule_deriv {D : precategory} {T : Monad C} (L : LModule T D) : LModule T D :=
  (LModule_comp_data (deriv_dist T) L,, LModule_comp_laws (deriv_dist_is_monad_dist T) L).

End deriv_def.

End maybe_def.
