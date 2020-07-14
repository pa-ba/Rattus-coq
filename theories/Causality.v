(** This module proves Theorem 4.2 from the paper. *)

From Coq Require Import Program.Equality Omega.
From Rattus Require Export Streams FundamentalProperty.



From Rattus Require Import Tactics.

Import ListNotations.


(* We start with the two central lemmas that prove the essence of the
causality property. *)


Lemma causality1 A B nu t vs :
  closed_type A -> (forall n, isvalue (vs n)) -> (forall n, ctx_empty ⊢ (vs n) ∶ A) -> 
  ctx_empty ⊢ t ∶ Arrow (Str A) (Str B) ->
  trrel B nu vs (app t (adv (ref thel)),heap_empty).
Proof.
  intros CTA VT' Cvs' Ty.
  assert (forall n, vrel_vtype A (vs n)) as VT
      by (intros; apply trel_vrel;eauto using fund_prop_closed).
  assert (forall n, closed_term (vs n)) as Cvs
      by (intros n; eapply typed_closed;eauto).
  constructor; eauto using closed_heap_empty, typed_closed, heap_empty_fresh.
  intros s Ts Cs.
  pose Ty as Ty'.
  eapply fund_prop with (g:= nil) (Hs := (str_heapseq (tl (tl vs))))
                        (s := (Some (heap_single thel (vs 0 ∷ ref thel)),
                                         heap_single thel (vs 1 ∷ ref thel)))
    in Ty';eauto. rewrite sub_empty_app in Ty' by auto.
  eapply trel_app; eauto using typed_closed. eauto using str_heapseq_closed.
  eapply trel_adv. auto using mapsto_heap_cons.
  apply vrel_trel. autorewrite with vrel. eexists. split. reflexivity. simpl.
  autorewrite with vrel. do 2 eexists. split. reflexivity. split.
  rewrite closed_tsubst by auto. eauto using vtype_vrel.
  apply trel_vrel;eauto.  constructor; eauto using closed_heap_alloc, typed_closed.

  apply  fund_prop_closed;eauto.
  eauto using str_heapseq_closed, closed_heapseq_tail.
  constructor; eauto using closed_heap_alloc, typed_closed.

  eapply vrel_mono; try eapply thel_vrel;eauto.
  eauto using str_heapseq_closed.
  eauto using str_heapseq_closed.
  constructor;  eauto using vtype_vrel_closed,closed_heap_alloc, closed_heap_empty.
Qed.

(** This is part (ii) of Theorem 3.2 in the paper. *)
Lemma causality2 A B nu s vs :
  vtype B -> (forall n, isvalue (vs n)) -> (forall n, ctx_empty ⊢ (vs n) ∶ A) -> 
  trrel B (S nu) vs s -> exists v' s', tred s (vs 0) v' s' /\ trrel B nu (tl vs) s' /\ ctx_empty ⊢ v' ∶ B.
Proof.
  intros VTB V Ty TR. inversion TR;subst.
  assert (vrel_vtype A (vs 0))  as Ty' by (apply trel_vrel;eauto using fund_prop_closed).

  assert (exists (v' : term) (s : store),
  {t, (Some (heap_cons h thel (vs 0 ∷ ref thel)), heap_single thel (vs 1 ∷ ref thel))}⇓ {v', s} /\
  vrel (S nu) (Str B) (str_heapseq (tl (tl vs))) s v') as Red.
  eapply H1; try eassumption;eauto using tick_le_refl,str_heapseq_closed, tick_le_refl. 
  constructor; eauto using vtype_vrel_closed,closed_heap_alloc,closed_heap_empty,typed_closed.
  destruct Red as (v'& s&R&VR).
  
  pose (red_extensive _ _ _ _ R) as SL. dependent destruction SL. 
  eapply red_not_later with (u:=unit) in R; eauto using heap_dom_cons'.
  rewrite heap_cons_eq in R.
  autorewrite with vrel in VR. simpl in VR. destruct VR as (v'' & E & VR). subst.
  autorewrite with vrel in VR. simpl in VR. destruct VR as (v1 & v2 & E & VR). subst.

  destruct VR as (VR1 & VR2). autorewrite with vrel' in VR2.
  destruct VR2 as (l & u & E & M & LR). subst. 
  
  do 2 eexists. split. econstructor. apply R. split. constructor.
  - assert (heap_mapsto thel (vs 1 ∷ ref thel) h2') by eauto using mapsto_heap_cons.
    assert (closed_term (vs 1 ∷ ref thel)) by eauto using vtype_vrel_closed, typed_closed.
    assert (closed_heap (heap_cons h2' thel unit)). apply red_closed in R;eauto.
    destruct R as [C1 C2]. inversion C2. auto.
    constructor;eauto using closed_heap_empty,
                closed_heap_alloc,vtype_vrel_closed.
    eauto using closed_heap_alloc, typed_closed.
    eauto using closed_heap_delete, closed_heap_cons_rev.
  - eauto using vrel_delay_closed. 
  - rewrite heap_cons_delete'. rewrite heap_cons_eq.
    inversion M. subst. simpl in LR.
    rewrite heap_overwrite'; eauto using mapsto_heap_cons.
    eapply trel_adv; try eassumption.
  - rewrite tsubst_vtype in VR1. eauto using vtype_typing. assumption.
Qed.

(* Finally we use the above two lemmas to prove the causality
property. In particular we construct infinite reduction sequences of
the form

  (t0,h0) --[v0/v'0]--> (t1,h1) --[v1/v'1]--> (t2,h2) --[v2/v'2]-->
  ...

where vi is the input value (of type A) given at the ith step and
each v'i is the corresponding output value (of type B). Such infinite
reduction sequences are represented by the coinductive type [Sred B vs
(t0,h0)] defined below, where vs maps i to vi.  *)


(* [Tred A vs s] indicates that there is an infinite stream transducer
reduction that takes inputs [vs], starts with state [s], and produces
well-typed output of type A. *)


CoInductive Tred (A : type) (vs : nat -> term) (s : state) : Prop :=
  mkSred (nextState : state) (output : term) :
         ctx_empty ⊢ output ∶ A ->
         tred s (vs 0) output nextState ->
         Tred A (tl vs) nextState -> Tred A vs s.


(* [Tred' A vs n s] represents finitary approximations of [Tred A vs
s] of length n, i.e. the first n reductions. This type is used for
constructing the proof of [Tred]. *)


Inductive Tred' (A : type) (vs : nat -> term) :  nat -> state -> Prop :=
| mkSred' n s (nextState' : state)
          (output' : term) :
    ctx_empty ⊢ output' ∶ A ->
    tred s (vs 0) output' nextState' ->
    Tred' A (tl vs) n nextState' -> Tred' A vs (S n) s
| doneSred' s : Tred' A vs 0 s.

Hint Constructors Tred' : core.

Lemma tred_determ s v v1 v2 s1 s2 : tred s v v1 s1 -> tred s v v2 s2 -> v1 = v2 /\ s1 = s2.
Proof.
  intros SR1. intros SR2. dependent destruction SR1. dependent destruction SR2.
  eapply red_determ in H; eauto. destruct H as (H1 & H2).
  inversion H1. inversion H2. subst. eauto.
Qed.

Lemma tred'_tred' A s vs :
  (forall n vs, Tred' A vs n s) -> Tred A vs s.
Proof.
  generalize dependent s. generalize dependent vs. cofix IH. intros vs s SR. 

  pose (SR 1 vs) as S1. dependent destruction S1. subst.
  econstructor;try eassumption.
  apply IH. intros n vs'.

  pose (SR (S n) (cons (vs 0) vs')) as Sn. dependent destruction Sn.
  eapply tred_determ in H0;eauto. destruct H0; subst. assumption.
Qed.

Lemma tred'_tred A s vs P : (forall n, P (vs n)) ->
  (forall n vs, (forall n, P (vs n)) -> Tred' A vs n s) ->  Tred A vs s.
Proof.
  generalize dependent s. generalize dependent vs. cofix IH. intros vs s PS SR . 

  pose (SR 1 vs) as S1. dependent destruction S1. subst. auto.
  econstructor;try eassumption.
  apply IH. eauto. intros n vs' PS'.
  assert (forall n : nat, P (cons (vs 0) vs' n)) as PS''.
  intros. destruct n0; simpl; eauto.
  pose (SR (S n) (cons (vs 0) vs') PS'') as Sn. dependent destruction Sn.
  eapply tred_determ in H0;eauto. destruct H0; subst. assumption.
Qed.


Lemma causality' A B t vs:
  closed_type A -> vtype B -> ctx_empty ⊢ t ∶ Arrow (Str A) (Str B) ->
  (forall n, isvalue (vs n)) -> (forall n, ctx_empty ⊢ (vs n) ∶ A) -> 
  forall n, Tred' B vs n (app t (adv (ref thel)), heap_empty).
Proof.
  intros CTA VTB Ty Vs Ts n.
  apply causality1 with (nu := n) (vs :=vs) in Ty; eauto.
  generalize dependent (app t (adv (ref thel)),heap_empty).
  clear t. generalize dependent vs. induction n;intros.
  - constructor.
  - eapply causality2 in Ty;eauto. autodest. 
Qed.


(* Theorem 4.2 from the paper *)
Theorem causality A B t vs :
  closed_type A -> vtype B -> ctx_empty ⊢ t ∶ Arrow (Str A) (Str B) -> 
  (forall n, isvalue (vs n)) -> (forall n, ctx_empty ⊢ (vs n) ∶ A) -> 
  Tred B vs (app t (adv (ref thel)), heap_empty).
Proof.
  intros. remember (fun v => isvalue v /\ ctx_empty ⊢ v ∶ A) as P.
  assert (forall n, P (vs n)) as Pn by (subst;split;eauto).

  eapply tred'_tred with (P:=P). apply Pn. subst. intros.
  eapply causality'. apply H. eauto. eauto.
  intros m. pose (H4 m). tauto. intros m. pose (H4 m). tauto.
Qed.
