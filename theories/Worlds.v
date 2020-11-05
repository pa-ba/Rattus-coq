From Rattus Require Export Heaps ClosedTerms.

From Rattus Require Import Tactics.

From Coq Require Import Lia Program.Equality.

From stdpp Require Import gmap fin_maps fin_sets.


(* Definition of heaps *)
Definition store : Type := option heap * heap.

Declare Scope heap_scope.
Bind Scope heap_scope with heap. 
Open Scope heap_scope.

Definition gc (s : store) : store :=
  match s with
  |  (_, h) => (None , h)
  end.

Definition store_tick (s : store) (h : heap) : store :=
  match s with
  | (_, h') => (Some h', h)
  end.

Inductive store_mapsto : loc -> term -> store -> Prop :=
| store_mapsto_heap l t h h' : heap_mapsto l t h -> store_mapsto l t (h', h).

Hint Constructors store_mapsto : core.

(* freshness for heaps *)
    

(* orders on heaps and stores *)

Definition heap_le (h1 h2 : heap) : Prop := forall x e, heap_mapsto x e h1 -> heap_mapsto x e h2
.
Inductive store_le : store -> store -> Prop :=
| store_le_lock h h' : heap_le h h' -> store_le (None, h) (None, h')
| store_le_tick h1 h1' h2 h2' : heap_le h1 h1' -> heap_le h2 h2' ->
                                store_le (Some h1, h2) (Some h1', h2').

Inductive tick_le : store -> store -> Prop :=
| tick_le_store s s' : store_le s s' -> tick_le s s'
| tick_le_tick h1 h2 h2' : heap_le h2 h2' ->
                           tick_le (None, h2) (Some h1, h2').

Hint Constructors store_le tick_le : core.


Definition heapseq := nat -> heap.

Definition cons {A} (h : A) (hs : nat -> A) : nat -> A :=
  fun n => match n with
           | O => h
           | S m => hs m
           end.

Definition tl {A} (hs : nat -> A) : nat -> A :=
  fun n => hs (S n).

Definition hd {A} (hs : nat -> A) : A := hs 0.


Definition heapseq_le hs1 hs2  := forall (n : nat), heap_le (hs1 n) (hs2 n).

(* reflexivity and transitivity of the above orders *)

Lemma heap_le_refl h : heap_le h h.
Proof.
  unfold heap_le. intros. auto.
Qed. 


Lemma heapseq_le_refl Hs : heapseq_le Hs Hs.
Proof.
  intros n. eauto using heap_le_refl.
Qed. 



Lemma store_le_refl s : store_le s s.
Proof.
  destruct s;try destruct o;eauto using heap_le_refl.
Qed.

Lemma tick_le_refl s : tick_le s s.
Proof.
  destruct s;eauto using store_le_refl.
Qed. 

Lemma heap_le_trans s1 s2 s3 : heap_le s1 s2 -> heap_le s2 s3 -> heap_le s1 s3.
Proof.
  unfold heap_le. intros. eauto.
Qed. 

Lemma store_le_trans s1 s2 s3 : store_le s1 s2 -> store_le s2 s3 -> store_le s1 s3.
Proof.
  intros T1 T2. destruct T1; inversion T2;eauto using heap_le_trans.
Qed.
  
Lemma tick_le_trans s1 s2 s3 : tick_le s1 s2 -> tick_le s2 s3 -> tick_le s1 s3.
Proof.
  intros T1 T2. destruct T1;inversion T2;subst;eauto using store_le_trans.
  -  inversion H. subst. apply tick_le_tick. eauto using heap_le_trans.
  - inversion H0. subst. apply tick_le_tick. eauto using heap_le_trans.
Qed .
                                
Lemma heapseq_le_trans Hs1 Hs2 Hs3 : heapseq_le Hs1 Hs2 -> heapseq_le Hs2 Hs3 -> heapseq_le Hs1 Hs3.
Proof.
  intros S1 S2 n. eauto using heap_le_trans. 
Qed.


Lemma tick_le_lock hn hl s : tick_le (hn, hl) s ->
                             exists hn' hl', s = (hn', hl').
Proof.
  intros L. dependent destruction L.
  - dependent destruction H; eauto.
  - eauto.
Qed.



Lemma tick_le_none hl hl' hn :
  heap_le hl hl' -> tick_le (None, hl) (hn, hl').
Proof.
  intros. destruct hn;eauto.
Qed.



Lemma skipn_skipn A n n' (l : list A) : skipn n (skipn n' l) = skipn (n' + n) l.
Proof.
  generalize dependent l. induction n'; intros; simpl; eauto. destruct l.
  + destruct n;reflexivity.
  + eauto.
Qed.


(* Other properties of the orderings *)

Lemma heap_le_dom h h' l : heap_le h h' -> heap_dom l h -> heap_dom l h'.
Proof.
  intros L D. destruct D as (t & D). apply L in D. eexists. eauto.
Qed.





Lemma store_le_mapsto l t s s' : store_le s s' -> store_mapsto l t s -> store_mapsto l t s'.
Proof.
  intros SL SM. destruct SL;inversion SM; autodest.
Qed.

Lemma tick_le_mapsto l t s s' : tick_le s s' -> store_mapsto l t s -> store_mapsto l t s'.
Proof.
  intros SL SM; destruct SL.
  - eauto using store_le_mapsto.
  - inversion SM; autodest. 
Qed. 


Lemma heap_cons_mono l h x: heap_fresh l h -> heap_le h (heap_cons h l x).
Proof.
  unfold heap_le, heap_fresh. intros.
  pose (Nat.eq_decidable l x0) as EQ. destruct EQ. subst.
  assert (exists e,heap_mapsto x0 e h) by eauto. contradiction.
  apply heap_cons_mapsto_neq;eauto.
Qed.


Lemma mapsto_heap_cons l t h : heap_mapsto l t (heap_cons h l t).
Proof.
  rewrite heap_cons_mapsto_eq. auto.
Qed.


Lemma store_mapsto_cons l t h h' : store_mapsto l t (h', (heap_cons h l t)).
Proof.
  eauto using mapsto_heap_cons.
Qed.

Lemma tick_le_store_tick s s' h h' : tick_le s s' -> heap_le h h' -> tick_le (store_tick s h) (store_tick s' h').
Proof.
  intros. destruct s. destruct o.
  - inversion H. subst. inversion H1. subst. constructor. constructor; eauto.
  - inversion H; subst. inversion H1; subst; simpl; eauto.
    simpl. eauto.
Qed. 


Lemma tick_le_gc s s' : tick_le s s' -> store_le (gc s) (gc s').
Proof.
  intros. destruct H.
  - destruct H;simpl;eauto.
  - simpl. eauto.
Qed.




Hint Resolve tick_le_refl store_le_refl heap_le_refl heapseq_le_refl : core.


Lemma tick_le_gc': forall s : store, tick_le (gc s) s.
Proof.
  intros. destruct s;simpl;eauto. destruct o; eauto. 
Qed.


Lemma tick_le_tick' s hn hl  : tick_le (Some hn, hl) s ->
                              exists hn' hl', s = (Some hn', hl') /\
                                              heap_le hn hn' /\ heap_le hl hl'.
Proof.
  intros T. inversion T. subst. inversion H. subst. eauto.
Qed.


Lemma heap_le_empty h : heap_le heap_empty h.
Proof.
  intros l t M. assert (exists t, heap_mapsto l t heap_empty) as C by eauto.
  apply heap_empty_fresh in C. contradiction.
Qed.

Hint Resolve heap_le_empty : core.

Lemma tick_le_empty s : tick_le (None, heap_empty) s.
Proof.
  destruct s as [h h']. destruct h; eauto.
Qed.

Lemma tick_le_cons hn hl l t :
  heap_fresh l hl ->
  tick_le (hn, hl) (hn, (heap_cons hl l t)).
Proof.
  intro. constructor. destruct hn ;econstructor; eauto using heap_cons_mono.
Qed.




(* Other properties of heaps and stores *)

Lemma heap_dom_cons' l h t : heap_dom l (heap_cons h l t).
Proof.
  exists t. apply heap_cons_mapsto_eq. auto.
Qed.

Lemma heap_dom_cons l l' h t : heap_dom l h -> heap_dom l (heap_cons h l' t).
  unfold heap_dom. intro H. destruct H as (u & H).
  pose (Nat.eq_decidable l l') as D. destruct D.
  - subst. apply heap_dom_cons'.
  - exists u. rewrite heap_cons_mapsto_neq; auto. 
Qed.


Lemma heap_dom_alloc_fresh l h : heap_dom l h -> l <> alloc_fresh h.
Proof.
  intros D.
  pose (heap_fresh_alloc h).
  destruct (Nat.eq_decidable l (alloc_fresh h)). subst. contradiction. assumption.
Qed.


Lemma store_mapsto_gc l t s : store_mapsto l t s -> store_mapsto l t (gc s).
Proof.
  intros. destruct H; simpl; autodest.
Qed.
  

Lemma store_tick_gc s h : store_tick (gc s) h = store_tick s h.
Proof.
  destruct s; auto.
Qed.


Lemma gc_idem s : gc (gc s) = gc s.
Proof.
  destruct s;auto.
Qed.


(* Lemma store_bot_gc s : s <> store_bot <-> gc s <> store_bot. *)
(* Proof. *)
(*   split; intros; destruct s; intro C;subst;simpl in *; try contradiction; inversion C. *)
(* Qed.  *)


Lemma length_skipn n A  : forall (Hs : list A), n <= length Hs -> length (skipn n Hs) = length Hs - n.
Proof.
  induction n;intros.
  - unfold skipn. simpl. zify;lia.
  - destruct Hs. inversion H. simpl in *. apply IHn. lia.
Qed.

(* Closed heaps *)

Definition closed_heap (h : heap) := forall l t, heap_mapsto l t h -> closed_term t.

Inductive closed_store : store -> Prop :=
| closed_store_lock h : closed_heap h -> closed_store (None, h)
| closed_store_tick h h' : closed_heap h -> closed_heap h' -> closed_store (Some h, h').

Definition closed_heapseq  (hs : heapseq) := forall n, closed_heap (hs n).



Lemma closed_heapseq_cons hs : closed_heap (hd hs) -> closed_heapseq (tl hs) -> closed_heapseq hs.
Proof.
  intros HP HS n. destruct n; eauto.
Qed.

Lemma closed_heap_cons_rev u h l t : closed_term u -> heap_mapsto l u h -> closed_heap (heap_cons h l t) -> closed_heap h.
Proof.
  intros CT M CH.
  intros l' t' M'.
  destruct (Nat.eq_decidable l l').
  - subst. eapply heap_mapsto_determ in M;eauto. subst. auto.
  - eapply CH. rewrite heap_cons_mapsto_neq; eauto.
Qed.


Hint Constructors closed_store : core.

Lemma closed_store_gc s: closed_store s -> closed_store (gc s).
Proof.
  intros CS. destruct CS;simpl;eauto.
Qed.

Lemma closed_heap_empty : closed_heap heap_empty.
Proof.
    intros l t M. assert (exists t, heap_mapsto l t heap_empty) as C by eauto.
  apply heap_empty_fresh in C. contradiction.
Qed. 

Hint Resolve closed_heap_empty : core.

Lemma closed_heapseq_tail hs : closed_heapseq hs -> closed_heapseq (tl hs).
Proof.
  intros HS n. destruct n; eauto.
Qed.

Lemma closed_heapseq_head hs : closed_heapseq hs -> closed_heap (hd hs).
Proof.
  intros HS. eauto.
Qed.

Lemma closed_store_now hn hl : closed_store (hn, hl) -> closed_heap hl.
Proof.
  intros CS. inversion CS;subst;auto.
Qed.

Lemma closed_heap_alloc h t l : closed_heap h -> closed_term t -> closed_heap (heap_cons h l t).
Proof.
  intros. intros l' t' M.
  pose (Nat.eq_decidable l l') as EQ. 
  destruct EQ as [EQ | EQ].
  - subst. rewrite heap_cons_mapsto_eq in M. subst. eauto. 
  - rewrite heap_cons_mapsto_neq in M by auto. eauto.
Qed.

Lemma closed_heap_delete h l : closed_heap h -> closed_heap (heap_delete h l).
Proof.
  unfold closed_heap, heap_mapsto, heap_delete. intros Ch l' t D.
  apply Ch with (l:=l'). eapply lookup_weaken. apply D. apply delete_subseteq.
Qed.
  

Lemma closed_store_cons hn hl l t : closed_term t -> closed_store (hn, hl) -> closed_store (hn, heap_cons hl l t).
Proof.
  intros CT CS. inversion CS;subst;eauto using closed_heap_alloc.
Qed.
