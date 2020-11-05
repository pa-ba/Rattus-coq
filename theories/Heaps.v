(** This module defines heaps based on finite maps of the coq-std++
library. *)

From stdpp Require Import gmap fin_maps fin_sets.
From Coq Require Import Lia.

From Rattus Require Import RawSyntax.




Definition heap : Set := gmap loc term.

Definition heap_dom_set (h : heap) : (gset loc) := dom _ h.

Definition heap_empty : heap := empty.
Definition heap_cons (h : heap) (l : loc) (t: term) : heap := insert l t h.

Definition heap_delete (h : heap) (l : loc) : heap := delete l h.
  
Definition heap_mapsto (l : loc) (t : term) (h : heap) : Prop :=
  h !! l = Some t.

Definition alloc_fresh (h : heap) : loc :=
  S(set_fold (fun k k' => max k k') 0 (heap_dom_set h)).


Definition heap_dom (l : loc) (h : heap) : Prop := exists t, heap_mapsto l t h.
Definition heap_fresh (l : loc) (h : heap) : Prop := not (exists t, heap_mapsto l t h).

Lemma heap_empty_fresh l : heap_fresh l heap_empty.
Proof.
  apply lookup_empty_is_Some.
Qed.
  


Lemma alloc_fresh_max h l : l ∈ heap_dom_set h -> alloc_fresh h > l.
Proof.
  remember (fun f (s : gset loc) => l ∈ s -> S f > l) as P.

  assert (forall s, P (set_fold (fun k k' => max k k') 0 s) s) as IP.
  apply set_fold_ind;subst;simpl;intros.
  - intros n n' En s s' Es. split.
    + intros I E. subst. apply I. apply Es. auto.
    + intros I E. subst. apply I. apply Es. auto.
  - apply not_elem_of_empty in H. contradiction.
  - rewrite elem_of_union in H1. destruct H1.
    + apply elem_of_singleton_1 in H1. subst. zify;lia.
    + apply H0 in H1. zify;lia.
  - subst. eauto.
Qed.

Lemma heap_fresh_alloc h : heap_fresh (alloc_fresh h) h.
Proof.
  intros F. unfold heap_mapsto in *. destruct F.

  assert (alloc_fresh h ∈ heap_dom_set h).
  eapply elem_of_dom_2. eassumption.
  apply alloc_fresh_max in H0. lia.
Qed.
  
Lemma heap_mapsto_determ l t t' h : heap_mapsto l t h -> heap_mapsto l t' h -> t = t'.
Proof.
  unfold heap_mapsto. intros M1 M2. rewrite M1 in M2. inversion M2. auto.
Qed.

Lemma max_proper : Proper (equiv ==> eq)
                          (set_fold (fun (k k' : nat) => k `max` k') 0 : gset loc -> nat).
Proof.
  apply set_fold_proper.
  - apply Eqsth.
  - intros n n' En m m' Em. subst. auto.
  - intros. do 2 rewrite Nat.max_assoc.
    f_equal. apply Nat.max_comm.
Qed.

Lemma alloc_dom  l h t : heap_dom l h -> alloc_fresh (heap_cons h l t) = alloc_fresh h.
Proof.
  intros D. unfold alloc_fresh, heap_cons.
  f_equal. apply max_proper.
  assert (heap_dom_set (<[l:=t]> h) ≡ {[l]} ∪ heap_dom_set h) as R.
  apply dom_insert.
  rewrite R. clear R.
  assert (l ∈ heap_dom_set h). unfold heap_dom in D.
  destruct D as (u & D). eapply elem_of_dom_2. apply D.
  set_solver.
Qed.
  
Lemma heap_cons_mapsto_neq  l l' t u h :
  l <> l' -> heap_mapsto l t (heap_cons h l' u) <-> heap_mapsto l t h.
Proof.
  unfold heap_mapsto, heap_cons. intros LNeq. split.
  - intros M. rewrite <- M. symmetry. apply lookup_insert_ne. auto.
  - intros L. rewrite <- L. apply lookup_insert_ne. auto.
Qed.

Lemma heap_cons_comm l l' t u h :
  l <> l' -> heap_cons (heap_cons h l u) l' t = heap_cons (heap_cons h l' t) l u.
Proof.
  intros LNeq. unfold heap_cons. apply insert_commute. auto.
Qed.

Lemma heap_cons_eq l t u h : heap_cons (heap_cons h l u) l t = heap_cons h l t.
Proof.
  apply insert_insert.
Qed.
  
Lemma heap_cons_mapsto_eq l t u h : heap_mapsto l t (heap_cons h l u) <-> t = u.
Proof.
  unfold heap_mapsto, heap_cons. split.
  - intros M. assert (<[l:=u]> h !! l = Some u) as E by apply lookup_insert.
    rewrite E in M. inversion M. reflexivity.
  - intros E. subst. apply lookup_insert.
Qed.

  

Lemma heap_overwrite h1 h2 l t u :
  heap_mapsto l t h2 ->  heap_cons h1 l u = heap_cons h2 l u -> heap_cons h1 l t = h2.
Proof.
  unfold heap_mapsto, heap_cons. intros L C.
  apply map_eq. intros.
  destruct (Nat.eq_decidable l i).
  - subst. assert (<[i:=t]> h1 !! i = Some t) as E by apply lookup_insert.
    rewrite <- L in E. auto.
  - assert (<[l:=t]> h1 !! i = h1 !! i) as E by (apply lookup_insert_ne; auto).
    assert (<[l:=u]> h1 !! i = h1 !! i) as E1 by (apply lookup_insert_ne; auto).
    assert (<[l:=u]> h2 !! i = h2 !! i) as E2 by (apply lookup_insert_ne; auto).
    unfold lookup, insert in *. rewrite E.
    rewrite C in E1. rewrite E1 in E2. auto.
Qed.


Lemma heap_overwrite' h l t :
  heap_mapsto l t h -> heap_cons h l t = h.
Proof.
  unfold heap_mapsto, heap_cons. intros L.
  apply map_eq. intros.
  destruct (Nat.eq_decidable l i).
  - subst. assert (<[i:=t]> h !! i = Some t) as E by apply lookup_insert.
    rewrite <- L in E. auto.
  - assert (<[l:=t]> h !! i = h !! i) as E by (apply lookup_insert_ne; auto).
    unfold lookup, insert in *. assumption.
Qed.



Lemma heap_cons_delete h l t : heap_delete (heap_cons h l t) l = heap_delete h l.
Proof.
  unfold heap_delete, heap_cons. apply delete_insert_delete.
Qed.


Lemma heap_cons_delete' h l t : heap_cons (heap_delete h l) l t = heap_cons h l t.
Proof.
  unfold heap_delete, heap_cons. apply insert_delete.
Qed.

