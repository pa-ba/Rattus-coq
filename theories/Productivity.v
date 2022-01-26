(** This module proves Theorem 4.2 from the paper. *)

From Rattus Require Export Streams FundamentalProperty Tactics.

From Coq Require Import Program.Equality Init.Specif.

(* We start with the two central lemmas that prove the essence of the
productivity property. *)

Lemma productivity1 nu A t : ctx_empty ⊢ t ∶ Str A -> strel nu A empty_heaps (t,heap_empty).
Proof.
  intros T. constructor; eauto using closed_heap_empty, typed_closed.
  erewrite <- sub_empty_app.
  eapply fund_prop;eauto. auto.
Qed.


Lemma productivity2 A k s :
  vtype A -> strel (S k) A empty_heaps s ->
  exists s' v, ctx_empty ⊢ v ∶ A  /\ sred s v s' /\ strel k A empty_heaps s'.
Proof.
  intros VT SR. destruct SR as [t h CH CT TR].
  assert (exists v s'', {t, (Some h, heap_empty)}⇓ {v, s''}
                        /\ vrel (S k) Str A empty_heaps s'' v) as RV.
  apply TR;eauto using empty_heaps_closed, closed_heap_empty.
  destruct RV as (v' & s'' & R & V).
  assert (closed_store s'') as CS.
  eapply red_closed;try eassumption;eauto using closed_heap_empty.
  pose (red_extensive _ _ _ _ R) as RL.
  inversion RL. subst.
  inversion CS. subst.

  autorewrite with vrel in *. simpl in V. rewrite vtype_tsubst in V by assumption.
  destruct V as (v'' & E & V). subst. autorewrite with vrel in *. simpl in V.
  destruct V as (v & v''' & E & V1 & V2);subst.
  autorewrite with vrel in *. simpl in V2.
  destruct V2 as (l & u & E & M & TR');subst.

  
  eexists. eexists. 
  split. eapply vtype_typing; eassumption.

  split.
  econstructor. apply R.

  constructor;eauto. dependent destruction M. eapply trel_adv. eauto.
  unfold trel in *. intros.
  eapply TR';eauto using empty_heaps_closed, closed_heap_empty.                                     
Qed.

(* Finally we use the above two lemmas to prove the productivity
property. In particular, we construct infinite reduction sequences of
the form

  (t0,h0) --[v0]--> (t1,h1) --[v1]--> (t2,h2) --[v2]--> ...

where each v_i is a closed value of type A. Such infinite reduction
sequences are represented by the coinductive type [Sred A (t0,h0)]
defined below.  *)


(* [Sred A s] represents an infinite reduction sequence starting with
state s that produces well-typed output of type A. *)

CoInductive Sred (A : type) (s : state) : Prop :=
  mkSred (nextState : state) (output : term) :
      ctx_empty ⊢ output ∶ A ->
      sred s output nextState ->
      Sred A nextState -> Sred A s.


(* [Sred' A n s] represents finitary approximations of [Sred A s] of
length n, i.e. the first n reductions. This type is used for
constructing the proof of [Sred]. *)

Inductive Sred' (A : type) : nat -> state -> Prop :=
| mkSred' n s (nextState' : state)
          (output' : term) :
    ctx_empty ⊢ output' ∶ A ->
    sred s output' nextState' ->
    Sred' A n nextState' -> Sred' A (S n) s
| doneSred' s : Sred' A 0 s.

#[global] Hint Constructors Sred' : core.

Lemma sred_determ s v1 v2 s1 s2 : sred s v1 s1 -> sred s v2 s2 -> v1 = v2 /\ s1 = s2.
Proof.
  intros SR1. intros SR2. dependent destruction SR1. dependent destruction SR2.
  eapply red_determ in H; eauto. destruct H as (H1 & H2).
  inversion H1. inversion H2. subst. eauto.
Qed.

Lemma sred'_sred A s :
  (forall n, Sred' A n s) -> Sred A s.
Proof.
  generalize dependent s. cofix IH. intros s SR. 

  pose (SR 1) as S1. dependent destruction S1. econstructor; try eassumption.
  apply IH. intros n.

  pose (SR (S n)) as Sn. dependent destruction Sn.
  eapply sred_determ in H0;eauto. destruct H0; subst. assumption.
Qed.


Lemma productivity' A t :
  vtype A -> ctx_empty ⊢ t ∶ Str A -> forall n, Sred' A n (t, heap_empty).
Proof.
  intros VT Ty n.
  apply productivity1 with (nu := n) in Ty. generalize dependent (t,heap_empty).
  clear t. induction n;intros.
  - constructor.
  - apply productivity2 in Ty. autodest. assumption.
Qed.


(* Theorem 4.1 from the paper *)
Theorem productivity A t :
  vtype A -> ctx_empty ⊢ t ∶ Str A -> Sred A (t, heap_empty).
Proof.
  intros. eauto using sred'_sred, productivity'.
Qed.
