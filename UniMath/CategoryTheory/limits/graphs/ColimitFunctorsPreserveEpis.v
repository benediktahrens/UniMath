
(** *************************************************

Contents:

- Definitions of graphs and diagrams
- Formalization of colimits on this basis
- Rules for pre- and post-composition
- Proof that colimits form a property in a (saturated/univalent) category ([isaprop_Colims])
- Pointwise construction of colimits in functor precategories ([ColimsFunctorCategory])

Written by Benedikt Ahrens and Anders Mörtberg, 2015-2016

*****************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Local Open Scope cat.

(* Taken from largecatmodules/Modules/Prelims/lib.v *)
Definition preserves_Epi {B C : precategory} (F : functor B C) : UU :=
  ∏ a b (f : B ⟦a , b⟧), isEpi  f -> isEpi (# F f)%Cat.


Section colimit_functor_preserves_epis.

  Context (C : precategory)
          (D : category)
          (F : chain [C, D]).

(* The decomposed data. However, most definitions are taking
   the whole triple (a [ColimCocone]) as an argument

  Context (F_infty : [C, D])
          (ι : cocone F F_infty)
          (isCol : isColimCocone F F_infty ι).
 *)

  Context (FCC : ColimCocone F).
  Let F_infty : [C, D] := colim FCC.
  Let ι : cocone F F_infty := colimCocone FCC.
  Let isCol : isColimCocone F F_infty ι := isColimCocone_from_ColimCocone FCC.

  Hypothesis F_presv_epi : ∏ i, preserves_Epi (dob F i).

  Lemma Colim_Functor_Preserves_Epi: preserves_Epi F_infty.
  Abort.



End colimit_functor_preserves_epis.
