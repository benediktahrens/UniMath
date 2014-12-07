Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Definition propproperty ( X : hProp ) := pr2 X . 

(** * Paths in total spaces are equivalent to pairs of paths *)

(** proofs are inspired by HoTT library, http://github.com/HoTT/HoTT *)

(** some of the lemmas are proved for similar fibrations twice:
    once we consider fibrations over a type in universe [UU], 
    once we consider fibrations over the universe [UU] itself *)


Lemma total2_paths {A : UU} {B : A -> UU} {s s' : total2 (fun x => B x)} 
    (p : pr1 s = pr1 s') 
    (q : transportf (fun x => B x) p (pr2 s) = pr2 s') : s = s'.
Proof.
  induction s as [a b].
  induction s' as [a' b']; simpl in *.
  induction p.
  induction q.
  apply idpath.
Defined.


Lemma total2_paths_hProp (A : UU) (B : A -> UU) (is : forall a, isaprop (B a))
    (s s' : total2 (fun x => B x)) : pr1 s = pr1 s' -> s = s'.
Proof.
  intro h.
  apply (total2_paths h).
  apply proofirrelevance.
  apply is.
Defined.

Lemma total2_paths_UU  {B : UU -> UU} {s s' : total2 (fun x => B x)} 
    (p : pr1 s = pr1 s') 
    (q : transportf (fun x => B x) p (pr2 s) = pr2 s') : 
               s = s'.
Proof.
  induction s as [a b].
  induction s' as [a' b']; simpl in *.
  induction p.
  induction q.
  apply idpath.
Defined.

Lemma total2_paths2 {A : UU} {B : A -> UU} {a1 : A} {b1 : B a1} 
    {a2 : A} {b2 : B a2} (p : a1 = a2) 
    (q : transportf (fun x => B x) p b1 = b2) : 
    tpair (fun x => B x) a1 b1 = tpair (fun x => B x) a2 b2.
Proof.
  apply (@total2_paths _ _  
    (tpair (fun x => B x) a1 b1)(tpair (fun x => B x) a2 b2) p q).
Defined.

Lemma total2_paths2_UU {B : UU -> UU} {A A': UU} {b : B A} 
     {b' : B A'} (p : A = A') (q : transportf (fun x => B x) p b = b') : 
    tpair (fun x => B x) A b = tpair (fun x => B x) A' b'.
Proof.
  apply (@total2_paths _ _  
     (tpair (fun x => B x) A b)(tpair (fun x => B x) A' b') p q).
Defined.

Lemma base_paths {A : UU}{B : A -> UU}(a b : total2 B) : a = b -> pr1 a = pr1 b.
Proof.
  apply maponpaths.
Defined.

Lemma base_paths_UU {B : UU -> UU}(a b : total2 B) : a = b -> pr1 a = pr1 b.
Proof.
  apply maponpaths.
Defined.

Definition fiber_paths {A : UU} {B : A -> UU} {u v : total2 (fun x => B x)}
  (p : u = v) : transportf (fun x => B x) (base_paths _ _ p) (pr2 u) = pr2 v.
Proof.
  induction p.
  apply idpath.
Defined.

Definition fiber_paths_UU {B : UU -> UU} {u v : total2 (fun x => B x)}
  (p : u = v) : transportf (fun x => B x) (base_paths_UU _ _ p) (pr2 u) = pr2 v.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma total2_fiber_paths {A : UU} {B : A -> UU} {x y : total2 (fun x => B x)} 
 (p : x = y) : total2_paths  _ (fiber_paths p) = p.
Proof.
  induction p.
  induction x.
  apply idpath.
Defined.

Lemma total2_fiber_paths_UU {B : UU -> UU} {x y : total2 (fun x => B x)} 
 (p : x = y) : total2_paths_UU  _ (fiber_paths_UU p) = p.
Proof.
  induction p.
  induction x.
  apply idpath.
Defined.

Lemma base_total2_paths {A : UU} {B : A -> UU} {x y : total2 (fun x => B x)}
  {p : pr1 x = pr1 y} (q : transportf _ p (pr2 x) = pr2 y) :
  (base_paths _ _ (total2_paths _ q)) = p.
Proof.
  induction x as [x H]. 
  induction y as [y K].
  simpl in *. 
  induction p.  
  induction q.
  apply idpath.
Defined.

Lemma base_total2_paths_UU {B : UU -> UU} {x y : total2 (fun x => B x)}
  {p : pr1 x = pr1 y} (q : transportf _ p (pr2 x) = pr2 y) :
  (base_paths_UU _ _ (total2_paths_UU _ q)) = p.
Proof.
  induction x as [x H]. induction y as [y K].
  simpl in *. 
  induction p. 
  induction q.
  apply idpath.
Defined.


Lemma transportf_fiber_total2_paths {A : UU} (B : A -> UU) (x y : total2 (fun x => B x))
  (p : pr1 x = pr1 y) (q : transportf _ p (pr2 x) = pr2 y) :
  transportf (fun p' : pr1 x = pr1 y => transportf _ p' (pr2 x) = pr2 y)
  (base_total2_paths q)  (fiber_paths (total2_paths _ q)) = q.
Proof.
  induction x as [x H]. 
  induction y as [y K].
  simpl in *. 
  induction p. 
  induction q.
  apply idpath.
Defined.

Lemma transportf_fiber_total2_paths_UU (B : UU -> UU) (x y : total2 (fun x => B x))
  (p : pr1 x = pr1 y) (q : transportf _ p (pr2 x) = pr2 y) :
  transportf (fun p' : pr1 x = pr1 y => transportf _ p' (pr2 x) = pr2 y)
  (base_total2_paths_UU q)  (fiber_paths_UU (total2_paths_UU _ q)) = q.
Proof.
  induction x as [x H]. 
  induction y as [y K].
  simpl in *.
  induction p. 
  induction q.
  apply idpath.
Defined.


Theorem total2_paths_equiv {A : UU} (B : A -> UU) (x y : total2 (fun x => B x)) :
  weq (x = y) (total2 (fun p : pr1 x = pr1 y => transportf _ p (pr2 x) = pr2 y )).
Proof.
  exists (fun r : x = y =>  
               tpair (fun p : pr1 x = pr1 y => 
             transportf _ p (pr2 x) = pr2 y) (base_paths _ _ r) (fiber_paths r)).
  apply (gradth _
    (fun pq : total2 (fun p : pr1 x = pr1 y => transportf _ p (pr2 x) = pr2 y) => 
                         total2_paths (pr1 pq) (pr2 pq))).
  - intro p.
    apply total2_fiber_paths. 
  - intros [p q]. simpl in *.
    apply (total2_paths2 (base_total2_paths q)).
    apply transportf_fiber_total2_paths.
Defined.


Theorem total2_paths_hProp_equiv {A : UU} (B : A -> hProp) 
   (x y : total2 (fun x => B x)): weq (x = y) (pr1 x = pr1 y).
Proof.
  set (t := total2_paths_equiv B x y).
  simpl in *.
  set (t':= isweqpr1 
     (fun p : pr1 x = pr1 y => transportf (fun x : A => B x) p (pr2 x) = pr2 y)).
  simpl in *.
  assert (H : forall z : pr1 x = pr1 y, 
        iscontr (transportf (fun x : A => B x) z (pr2 x) = pr2 y)).
  intro p.
  set (H := pr2 (B (pr1 y))).
  simpl in H.
  apply (H _ (pr2 y)).
  simpl in *.
  set (Ht := t' H).
  set (ht := tpair _ _ Ht).
  set (HHH := weqcomp t ht).
  exact HHH.
Defined.

(** * Lemmas about transport *)

Definition transportD {A : UU} (B : A -> UU) (C : forall a : A, B a -> UU)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y) : C x2 (transportf _ p y).
Proof.  
  induction p. 
  exact z.
Defined.


Definition transportf_total2 {A : UU} {B : A -> UU} {C : forall a:A, B a -> UU}
  {x1 x2 : A} (p : x1 = x2) (yz : total2 (fun y : B x1 => C x1 y )): 
 transportf (fun x => total2 (fun y : B x => C x y)) p yz = 
 tpair (fun y => C x2 y) (transportf _ p  (pr1 yz)) (transportD _ _ p (pr1 yz) (pr2 yz)).
Proof.
  induction p. 
  induction yz. 
  apply idpath.
Defined.

Definition transportf_dirprod (A : UU) (B B' : A -> UU) 
  (x x' : total2 (fun a => dirprod (B a) (B' a)))  (p : pr1 x = pr1 x') :
  transportf (fun a => dirprod (B a) (B' a)) p (pr2 x) = 
                            dirprodpair (transportf (fun a => B a) p (pr1 (pr2 x))) 
                                        (transportf (fun a => B' a) p (pr2 (pr2 x))) .
Proof.
  induction p.
  apply tppr.
Defined.

Lemma eq_equalities_between_pairs (A : UU)(B : A -> UU)(x y : total2 (fun x => B x))
    (p q : x = y) (H : base_paths _ _ p = base_paths _ _ q) 
    (H2 : transportf (fun p : pr1 x = pr1 y =>  transportf _ p (pr2 x) = pr2 y )
         H (fiber_paths p) = fiber_paths q) :  p = q.
Proof.
  apply (invmaponpathsweq (total2_paths_equiv _ _ _ )).
  apply (total2_paths (B:=(fun p : pr1 x = pr1 y =>
          transportf (fun x : A => B x) p (pr2 x) = pr2 y))
          (s:=(total2_paths_equiv B x y) p)
          (s':=(total2_paths_equiv B x y) q) H).
  assumption.
Defined.
