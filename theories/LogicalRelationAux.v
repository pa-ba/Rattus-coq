(* Here we prove properties about the logical relation such as
   monotonicity under tick_le and heapseq_le *)

From Rattus Require Export LogicalRelation. 

From Rattus Require Import Tactics.

From Coq Require Import Program.Equality Omega Lia.
From Equations Require Import Equations.

Lemma vrel_gc nu A : forall Hs s t, vrel nu A Hs s t -> vrel nu A Hs (gc s) t.
Proof.
  remember (tsize A) as N. generalize dependent A.
  induction (lt_wf N) as [N _ IH]. intros.
  destruct A; try solve[autorewrite with vrel in *;eauto].
  - simp vrel' in *.  autodest.
    exists x, x0. split. reflexivity. split.
    + eapply (IH (tsize A1));[simpl; lia|eauto|eauto].
    + eapply (IH (tsize A2));[simpl; lia|eauto|eauto].
  - rewrite vrel_plus in *. autodest.
    + left. exists x. split. reflexivity. eapply (IH (tsize A1));[simpl; lia|eauto|eauto].
    + right. exists x. split. reflexivity. eapply (IH (tsize A2));[simpl; lia|eauto|eauto].
  - rewrite vrel_arrow in *. autodest. exists x. split. reflexivity. intros.
    rewrite gc_idem in *. apply H0;eauto.
  - destruct nu;simp vrel' in *.
    autodest. exists x, x0. split. reflexivity. split. apply store_mapsto_gc; assumption.
      intros. rewrite store_tick_gc. auto.
  - rewrite vrel_mu in *. autodest. exists x. split. reflexivity.
    apply (IH (tsize (tsubst 0 A (Delay (Fix A))))). rewrite tsize_subst. auto. auto. auto.
Qed.


Definition vrel_mono_prop A nu := forall nu' Hs Hs' s s' t,
    heapseq_le Hs Hs' -> tick_le s s' -> nu' <= nu -> vrel nu A Hs s t -> vrel nu' A Hs' s' t.

Lemma trel_mono' nu nu' A Hs Hs' s s' t : vrel_mono_prop A nu -> heapseq_le Hs Hs' ->
       nu' <= nu -> tick_le s s' ->  trel nu A Hs s t -> trel nu' A Hs' s' t.
Proof.
  unfold trel in *. intros.
  assert (tick_le s s'0) as A2 by eauto using tick_le_trans.
  remember (H3  s'0 A2 H5) as A3. clear HeqA3 H2. autodest.
Qed.

Lemma heapseq_le_tl Hs Hs' : heapseq_le Hs Hs' -> heapseq_le (tl Hs) (tl Hs').
Proof.
  intros H n. unfold heapseq_le in *. apply H.
Qed.

Lemma heapseq_le_hd Hs Hs' : heapseq_le Hs Hs' -> heap_le (hd Hs) (hd Hs').
Proof.
  intros H. unfold heapseq_le in *. apply H.
Qed.


Lemma vrel_mono : forall nu A nu' Hs Hs' s s'  t,
    heapseq_le Hs Hs' -> tick_le s s' -> nu' <= nu -> vrel nu A Hs s t -> vrel nu' A Hs' s' t.
Proof.
  intros nu. induction (lt_wf nu) as [nu _ IHnu].
  intros A.
  remember (tsize A) as N. generalize dependent A.

  induction (lt_wf N) as [N _ IHN]. intros. destruct A; try solve[autorewrite with vrel in *;eauto].
  - rewrite vrel_times in *. autodest.
    exists x, x0. split. auto. split.
    + eapply (IHN (tsize A1)); eauto. simpl. lia.
    + eapply (IHN (tsize A2)); eauto. simpl. lia.
  - rewrite vrel_plus in *. autodest.
    + left. exists x. split. auto. eapply (IHN (tsize A1)); eauto. simpl. lia.
    + right. exists x. split. auto. eapply (IHN (tsize A2)); eauto. simpl. lia.
  - intros. rewrite vrel_arrow in *. autodest.
    exists x. split. auto. intros.
    apply H3; eauto using heapseq_le_trans, store_le_trans, tick_le_gc. lia.
  - destruct nu.
    + inversion H1. subst. simp vrel' in *.
    + destruct nu'; simp vrel' in *; autodest. 
      exists x, x0. split. auto. split. eauto using tick_le_mapsto.
      eapply trel_mono'; try apply H4; unfold vrel_mono_prop. apply IHnu. lia.
      eauto using heapseq_le_tl. lia.     
      eapply tick_le_store_tick. eassumption.
      eauto using heapseq_le_hd.

  - rewrite vrel_box in *. autodest. exists x.
    split. reflexivity. intros.

    apply H3 in H2. eapply trel_mono' in H2. apply H2.
    intros nu'' Hs1 Hs2 s1 s2 t1 HS TR N VL.
    eapply IHN with (y := tsize A); eauto.  eauto. eauto. eauto.
  - rewrite vrel_mu in *. autodest. exists x. split. auto.
    eapply IHN with (y := (tsize (tsubst 0 A (Delay (Fix A)))));
    try rewrite tsize_subst; eauto. 
Qed.


Lemma trel_mono nu nu' A Hs Hs' s s' t : heapseq_le Hs Hs' ->
       nu' <= nu -> tick_le s s' ->  trel nu A Hs s t -> trel nu' A Hs' s' t.
Proof.
  intros. eapply trel_mono'; try eassumption.
  intros nu1 Hs1 Hs2 s1 s2 t1 HS T N V. eapply vrel_mono; eassumption.
Qed.
  
Lemma vrel_gc_rev A : forall nu Hs s t, vrel nu A Hs (gc s) t -> vrel nu A Hs s t.
Proof.
  intros. eauto using vrel_mono, tick_le_gc'.
Qed. 


Lemma vrel_stable A : forall nu Hs Hs' s s' t, stable A -> vrel nu A Hs s t -> vrel nu A Hs' s' t.
Proof.
  remember (tsize A) as N. generalize dependent A.
  induction (lt_wf N) as [N _ IH]. intros A HN nu Hs Hs' s s' t ST VR.
  destruct A; inversion ST; try solve[autorewrite with vrel in *;eauto].
  - rewrite vrel_times in *. autodest. exists x, x0.
    split. auto. split.
    + eapply (IH (tsize A1)); simpl; eauto; try lia.
    + eapply (IH (tsize A2)); simpl; eauto; try lia.
  - rewrite vrel_plus in *. autodest.
    + left. exists x. split. auto. eapply (IH (tsize A1)); simpl; eauto; try lia.
    + right. exists x. split. auto. eapply (IH (tsize A2)); simpl; eauto; try lia.
Qed.

Lemma vrel_trel nu A Hs s t : vrel nu A Hs s t -> trel nu A Hs s t.
Proof.
  intros. assert (isvalue t) by eauto using vrel_val. unfold trel.
  intros. exists t, s'. split. apply red_value. auto. eauto using vrel_mono.
Qed.


Lemma trel_vrel nu A Hs s t : closed_store s -> isvalue t -> trel nu A Hs s t -> vrel nu A Hs s t.
Proof.
  intros Cs IV T. unfold trel in *.
  assert (exists (v : term) (s' : store), {t, s}⇓ {v, s'} /\ vrel nu A Hs s' v)
    as T' by (apply T;eauto). destruct T' as (v & s' & R & V).
  apply red_isvalue_id in R. autodest. auto.
Qed.


(* context relation *)


(* Lemma crel_init (G : ctx init) Hs s g : crel G Hs s g -> s = store_bot. *)
(* Proof. *)
(*   intros C. dependent induction C;eauto. *)
(* Qed. *)

(* Lemma crel_now (G : ctx now) Hs s g : crel G Hs s g -> s <> store_bot. *)
(* Proof. *)
(*   intros C. dependent induction C;eauto. *)
(* Qed. *)

(* Lemma crel_now' (G : ctx now) Hs s g : crel G Hs s g ->  *)
(*                                    exists hn hl, s = store_lock hn hl. *)
(* Proof. *)
(*   intros C. apply crel_now in C. destruct s; eauto. contradiction. *)
(* Qed. *)

Lemma crel_later (G : ctx later) nu Hs s g : crel nu G Hs s g ->
                                   exists hn hl, s = (Some hn, hl).
Proof.
  intros C. dependent induction C;eauto.
Qed.

Lemma crel_gc (G : ctx now) nu Hs s g : crel nu G Hs s g -> crel nu G Hs (gc s) g.
Proof.
  intros C; dependent induction C.
  - simpl. auto.
  - simpl. eauto using vrel_gc.
  - auto.
Qed.

(* Lemma heaps_single_closed h : closed_heap h -> closed_heaps (heaps_single h). *)
(* Proof. *)
(*   intro C. intros h' H. inversion H. auto. *)
(* Qed. *)

(* Hint Resolve heaps_single_closed. *)

Lemma closed_heap_le h1 h2 : heap_le h2 h1 -> closed_heap h1 -> closed_heap h2.
Proof.
  intros L C l t M. eauto.
Qed.

Lemma closed_heapseq_le h1 h2 : heapseq_le h2 h1 -> closed_heapseq h1 -> closed_heapseq h2.
Proof.
  intros L C n.
  eauto using closed_heap_le.
Qed.

Lemma heapseq_cons_tl_le hs : heapseq_le hs (cons (hd hs) (tl hs)).
Proof.
  intros n. destruct n; auto.
Qed.


Lemma heapseq_cons_tl_le' hs : heapseq_le (cons (hd hs) (tl hs)) hs.
Proof.
  intros n. destruct n; auto.
Qed.

Lemma heapseq_cons_le h1 h2 hs1 hs2 :
  heap_le h1 h2 -> heapseq_le hs1 hs2 -> heapseq_le (cons h1 hs1) (cons h2 hs2).
Proof.
  intros HL SL n. destruct n;eauto. 
Qed.

Lemma heapseq_cons_closed h hs :
  closed_heap h -> closed_heapseq hs -> closed_heapseq (cons h hs).
Proof.
  intros HL SL n. destruct n;eauto. 
Qed.


Hint Resolve heapseq_cons_tl_le  heapseq_cons_tl_le' heapseq_cons_le heapseq_cons_closed : core.
  
Lemma crel_mono ty (G : ctx ty) nu nu' Hs Hs' s s' g :
  nu' <= nu ->
  heapseq_le Hs Hs' -> closed_heapseq Hs' ->
  tick_le s s' -> closed_store s' ->  crel nu G Hs s g -> crel nu' G Hs' s' g.
Proof.
  intros N HS CL T CS C. generalize dependent Hs'. generalize dependent s'.
  generalize dependent nu'.
  induction C;intros;eauto using vrel_mono.
  - inversion T; subst. inversion H. subst. inversion CS. subst.
    constructor. eapply IHC;eauto. lia.
Qed.


(* Lemma crel_tick' nu G Hs Hs' g hn hn' : *)
(*   crel nu G Hs (None, hn) g -> *)
(*   heap_le hn' (hd Hs) -> heapseq_le Hs' (tl Hs) -> *)
(*   crel (S nu) (ctx_tick G) Hs' (Some hn, hn') g. *)
(* Proof. *)
(*   intros HL SL C. eapply crel_mono with (nu' := S nu);eauto. *)
(* Qed. *)


Lemma crel_skip_later nu g hn hl G Hs :
  crel nu G Hs (Some hn, hl) g ->
  crel (S nu) (skip_later G)
       (cons hl Hs) (None, hn) (sub_skip (skip_later_count G) g).
Proof.
  intros C. dependent induction C;simpl;eauto.
Qed.

Lemma crel_stabilize ty nu g (G : ctx ty) Hs Hs' s s' :
  closed_heapseq Hs' -> closed_store s' ->
  crel nu G Hs s g -> 
  crel nu (stabilize G) Hs' s' (sub_skipc (stabilize G) g).
Proof.
  intros CH CS C. dependent induction C;simpl;eauto.
  - remember (stableb A) as S. destruct S ;simpl.
    + constructor. symmetry in HeqS. rewrite stableb_correct in HeqS.
      eauto using vrel_stable. assumption.
    + auto.
  - eapply crel_mono in IHC; eauto.
Qed.

Lemma crel_stabilize_later nu g (G : ctx later) Hs s:
  closed_heapseq Hs -> closed_store s ->  crel nu G Hs s g -> 
  crel nu (stabilize_later G) Hs s (sub_skipc (stabilize_later G) g).
Proof.
  intros CH CS C. dependent induction C;simpl;eauto.
  eauto using crel_stabilize, crel_mono.
Qed.


Lemma crel_ground nu ty (G : ctx ty) Hs s g : crel nu G Hs s g -> ground_sub 0 g G.
Proof.
  intros CR. induction CR; eauto.
Qed.

Lemma crel_sub_closed nu ty g (G : ctx ty) Hs s A t :
      G ⊢ t ∶ A -> closed_sub g -> crel nu G Hs s g -> closed_term (sub_app g t).
Proof.
  intros. eapply ground_sub_closed;eauto using crel_ground.
Qed.


(* Lemma ctx_lookup_vrel_stable nu ty (G : ctx ty) i T Hs s g : *)
(*   closed_heapseq Hs -> closed_store s -> stable T -> *)
(*   ctx_lookup G i T -> crel nu G Hs s g -> exists t, sub_lookup g i = Some t /\ vrel nu T Hs s t. *)
(* Proof. *)

Lemma ctx_lookup_vrel nu ty (G : ctx ty) i T Hs s g :
  closed_heapseq Hs -> closed_store s ->
  ctx_lookup G i T -> crel nu G Hs s g -> exists t, sub_lookup g i = Some t /\ vrel nu T Hs s t.
Proof.
  intros CH CS L C. generalize dependent g.
  generalize dependent s. generalize dependent Hs.
  induction L;intros.
  - dependent destruction C. eexists. split. cbv. reflexivity. assumption.
  - dependent destruction C. apply IHL in C; autodest.
  - dependent destruction C. apply IHL in C; autodest.
  - dependent destruction C. inversion CS. subst.
    eapply crel_mono with (nu' := nu) (Hs' := cons h Hs) (s' := (None, hn)) in C; eauto.
    apply IHL in C; autodest. exists x. split. assumption. eauto using  vrel_stable.
 
Qed.



Lemma sub_skip_later_app nu Hs s g G t A : skip_later G ⊢ t ∶ A -> crel nu G Hs s g ->
                                      sub_app (sub_skip (skip_later_count G) g) t = sub_app g t.
Proof.
  intros. apply sub_skips_id. eapply typing_svars;try eassumption. apply skip_later_skipn.
Qed.

(* Lemma sub_skip_both_app Hs s g G t A : *)
(*   skip_now (skip_later G) ⊢ t ∶ A -> crel G Hs s g -> *)
(*   sub_app (sub_skip (skip_now_count (skip_later G)) (sub_skip (skip_later_count G) g)) t *)
(*            = sub_app g t. *)
(* Proof. *)
(*   intros. rewrite sub_skips_id. apply sub_skips_id. eapply typing_svars;try eassumption. *)
(*   apply ctx_skips_now.  apply skip_later_skipn. *)
(*   eapply typing_svars;try eassumption. apply skip_now_skipn. *)
(* Qed.     *)

(* Lemma crel_now_lock (G : ctx now) Hs s g : crel G Hs (gc s) g -> *)
(*                                            exists h, gc s = store_lock None h. *)
(* Proof. *)
(*   intros C. *)
(*   apply crel_now in C. destruct s. *)
(*   - simpl in C. contradiction. *)
(*   - simpl in *. eauto. *)
(* Qed. *)


Inductive vtype : type -> Prop :=
| vtype_unit : vtype Unit
| vtype_nat : vtype Nat
| vtype_times A B :
    vtype A ->
    vtype B ->
    vtype (Times A B)
| vtype_plus A B :
    vtype A ->
    vtype B ->
    vtype (Plus A B).

Lemma tsubst_vtype n A B : vtype A -> tsubst n A B = A.
Proof.
  intros VT. induction VT; simpl;eauto.
  - rewrite  IHVT1. rewrite  IHVT2. reflexivity.
  - rewrite  IHVT1. rewrite  IHVT2. reflexivity.
Qed.


Lemma vtype_typing nu A Hs s v : vtype A -> vrel nu A Hs s v -> ctx_empty ⊢ v ∶ A.
Proof.
  intros VT VR. generalize dependent v.
  induction VT; intros; autorewrite with vrel in VR;autodest.
Qed.

Ltac impossible := match goal with
                   | [H : _ |- _] => try solve[inversion H]; clear H;impossible
                   | _ => idtac
                   end.

Lemma typing_vtype nu A Hs s v : vtype A -> isvalue v -> ctx_empty ⊢ v ∶ A -> vrel nu A Hs s v.
Proof.
  intros VT V Ty. generalize dependent v.
  induction VT;intros;
    dependent destruction Ty;try solve[impossible];inversion V;subst; autorewrite with vrel in *;eauto.
    do 2 eexists. eauto.
Qed.


Lemma vtype_vrel nu nu' A Hs s Hs' s' v : vtype A -> vrel nu A Hs s v -> vrel nu' A Hs' s' v.
Proof.
  intros VT VR. generalize dependent v.
  induction VT; intros; autorewrite with vrel in *;autodest;
  eauto 10.
Qed.


Lemma vtype_tsubst i A B : vtype A -> tsubst i A B = A.
Proof.
  intros VT. induction VT;simpl;f_equal;eauto.
Qed.



Lemma vrel_delay_closed nu A Hs s v : vrel nu (Delay A) Hs s v -> closed_term v.
Proof.
  intros V. destruct nu; autorewrite with vrel in V; autodest.
Qed. 


Lemma vtype_vrel_closed nu A Hs s v : vtype A -> vrel nu A Hs s v -> closed_term v.
  intros VT. generalize dependent v. induction VT;intros v VR;autorewrite with vrel in VR;
                                       autodest.
Qed.
  

  

Lemma vtype_inhab nu A Hs s : vtype A -> exists v, vrel nu A Hs s v.
Proof.
  intros VT. induction VT.
  - exists unit. autorewrite with vrel in *. auto.
  - exists (natlit 0). autorewrite with vrel in *. eauto.
  - autodest. eexists. autorewrite with vrel in *. eauto.
  - autodest. eexists. autorewrite with vrel in *. eauto.
Qed.



Lemma trel_app nu T1 T2 Hs s t1 t2 :
  closed_term t1 -> closed_term t2 -> closed_heapseq Hs ->
  trel nu (Arrow T1 T2) Hs s t1 -> trel nu T1 Hs s t2 ->
  trel nu T2 Hs s (app t1 t2).
Proof.
  unfold trel in *. intros Ct1 Ct2 CHs IHT1 IHT2 s' TL CS.

  assert (exists (v : term) (s'' : store), {t1, s'}⇓ {v, s''} /\ vrel nu (Arrow T1 T2) Hs s'' v)
    as IH1 by (apply IHT1;eauto).
  destruct IH1 as (v & s''& [IH1s IH1v]).

  assert (closed_store s'') as Cs'' by (eapply red_closed_store;try eapply IH1s;eauto).
  
  assert (exists (v : term) (s''' : store), {t2, s''}⇓ {v, s'''} /\ vrel nu T1 Hs s''' v)
    as IH2 by (apply IHT2;eauto using tick_le_trans, red_extensive).

  destruct IH2 as (v' & s'''& [IH2s IH2v]).
  apply vrel_gc in IH2v.

  
  assert (closed_store s''') as Cs''' by ( eapply red_closed_store;try eapply IH2s;eauto).
  
  rewrite vrel_arrow in IH1v.
  destruct IH1v as (u & [V IH1]). subst.
  apply IH1 in IH2v;eauto using red_closed_term, closed_store_gc, red_extensive,tick_le_gc.
  unfold trel in IH2v.


  
  assert (exists (v : term) (s4 : store), {sub_term u v', s''' }⇓ {v, s4} /\ vrel nu T2 Hs s4 v)
    as IH3 by (apply IH2v;eauto using tick_le_gc').

  autodest.
Qed. 

Lemma trel_adv nu l hl hn Hs A t:
  heap_mapsto l t hn ->
  trel nu A Hs (Some hn, hl) t ->
  trel nu A Hs (Some hn, hl) (adv (ref l)).
Proof.
  intros M Tt. unfold trel in *. intros.
  assert (exists (v : term) (s'' : store), {t, s'}⇓ {v, s''} /\ vrel nu A Hs s'' v)
    as Tt' by eauto.
  autodest.
  apply tick_le_tick' in H. autodest.
  do 2 eexists. split.
  eapply red_adv. constructor. auto. eauto.  eauto. eauto.
Qed.
