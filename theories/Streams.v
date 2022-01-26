(** This module defines the operational semantics for streams and
stream transducers (cf. Figure 6 in the paper). In addition, we
provide lemmas that are used to prove productivity and causality. *)


From Coq Require Import Omega Program.Equality.
From Rattus Require Import Tactics FundamentalProperty.
From Rattus Require Export LogicalRelationAux.


Open Scope type.


Notation "'Str' x" := (Fix (Times x (TypeVar 0))) (at level 0).

Notation "x ∷ y" := (into (pair x y))  (at level 100).

Notation "'head' x" := (pr1 (out x)) (at level 0).

Notation "'tail' x" := (pr2 (out x)) (at level 0).

(* state for the stream reduction semantics *)
Definition state := term * heap.


(* reduction semantics for streams *)
Inductive sred : state -> term -> state -> Prop :=
  sred_step t h v l hn hl :
    red t (Some h, heap_empty) (v ∷ l) (Some hn, hl) ->
    sred (t, h) v (adv l, hl).
  

Notation empty_heaps := (fun _ : nat => heap_empty).


(* Logical relation on streams *)

Inductive strel nu (A : type) (Hs : heapseq) : state -> Prop :=
  strel_intro t h :
    closed_heap h -> closed_term t ->
    trel nu (Str A) Hs (Some h, heap_empty) t ->
    strel nu A Hs (t,h).



Lemma empty_heaps_closed : closed_heapseq empty_heaps.
Proof.
  intros n. auto.
Qed. 

#[global] Hint Resolve empty_heaps_closed : core.

Definition thel : loc := 0.

Notation heap_single := (heap_cons heap_empty).

(* reduction semantics for stream transducers *)
Inductive tred : state -> term -> term -> state -> Prop :=
  tred_step t h v v' l hn hl :
    red t (Some (heap_cons h thel (v ∷ ref thel)), heap_single thel unit)
        (v' ∷ l) (Some hn,hl) -> 
    tred (t, h) v v' (adv l, heap_delete hl thel).



Definition str_heapseq (ts : nat -> term) : heapseq :=
  fun n => (heap_single thel (ts n ∷ ref thel)).



Lemma str_heapseq_closed ts : (forall n, closed_term (ts n)) -> closed_heapseq (str_heapseq ts).
Proof.
  unfold str_heapseq. intros C n. eauto using closed_heap_alloc, closed_heap_empty.
Qed.

(* Notation "'str_heapseq' A" := (repeat (str_heaps A)) (at level 0). *)


(* Logical relation on stream transducers *)

Inductive trrel (A : type) (k : nat) (vs : nat -> term) : state -> Prop :=
  trrel_intro t h :
    closed_heap h -> closed_term t ->
    (trel k (Str A) (str_heapseq (tl (tl vs)))
                      (Some (heap_cons h thel (vs 0 ∷ ref thel)),
                                  heap_single thel (vs 1 ∷ ref thel)) t) ->
    trrel A k vs (t,h).


Lemma red_lock  t hn hl h' v l :
  heap_dom l hl -> 
  {t, (hn, hl)} ⇓ {v, h'} -> exists hn' hl', h' = (hn', hl') /\ heap_dom l hl'.
Proof.
  intros I R. apply red_extensive in R. inversion R;subst;
  eauto using heap_le_dom.
Qed.



Ltac red_lock := match goal with
                 | [ H : red _ (_, ?hl) _ _ , I : heap_dom _ ?hl |- _] =>
                   eapply red_lock in H;auto;autodest;red_lock
                 | _ => eauto
                 end.

Lemma red_not_later hn hl hn' hl' l t u v :
  heap_dom l hl ->
  {t, (hn, hl)} ⇓ {v, (hn', hl')} ->
  {t, (hn, heap_cons hl l u)} ⇓ {v,(hn', heap_cons hl' l u)}.
Proof.
  intros I R. dependent induction R;eauto;try solve[red_lock].
  - pose (red_delay t (heap_cons hl l u) hn') as R. rewrite alloc_dom in R by assumption.
    rewrite heap_cons_comm in R by (apply heap_dom_alloc_fresh;auto).
    apply R.
Qed.

Lemma tl_str_heapseq vs : heapseq_le (str_heapseq (tl vs)) (tl (str_heapseq vs)).
Proof.
  intros n. apply heap_le_refl.
Qed.

Definition vrel_vtype A v := vrel 0 A empty_heaps (None, heap_empty) v.


Lemma thel_vrel v A nu vs Hs s :
  closed_type A -> hastype ctx_empty v A -> isvalue v -> closed_heapseq Hs -> closed_store s ->
  (forall n, hastype ctx_empty (vs n) A) -> (forall n, isvalue (vs n)) ->
  vrel nu (Delay (Str A)) (str_heapseq vs)
                  (None, heap_single thel (v ∷ ref thel)) (ref thel).
Proof.
  intros CTA Ty V CHs Cs TVs Vs.
  generalize dependent CHs. generalize dependent Cs.
  generalize dependent vs. generalize dependent v.
  induction nu;intros.
  - autorewrite with vrel'. eauto.
  - autorewrite with vrel'. exists thel. exists (v ∷ ref thel).
    split. auto. split. eauto using store_mapsto_cons.
    apply vrel_trel. autorewrite with vrel'. eexists. split. eauto.
    simpl. rewrite closed_tsubst by assumption. autorewrite with vrel'.
    eexists. eexists. split. eauto. split.
    + apply trel_vrel;auto.
      constructor; eauto using closed_heap_alloc, typed_closed, str_heapseq_closed,
                   closed_heapseq_head.
      apply fund_prop_closed;auto.
      eauto using closed_heapseq_tail, str_heapseq_closed, typed_closed.
      constructor; eauto using closed_heapseq_head, closed_heap_alloc,
                   str_heapseq_closed, typed_closed.
    + eapply vrel_mono; try eapply IHnu with (vs:= tl vs) (v:= vs 0);eauto.
Qed.
      

  

