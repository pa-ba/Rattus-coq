(** This module defines the logical relation (cf. Figure 7 in the
paper). *)

From Rattus Require Export Reduction.

From Rattus Require Import Tactics.

From Coq Require Import Arith Lia Program.
From Equations Require Import Equations.

Fixpoint tsize (A : type) : nat :=
  match A with
  | Unit => 1
  | Nat => 1
  | TypeVar _ => 1
  | Arrow B C => S (tsize B + tsize C)
  | Plus B C => S (tsize B + tsize C)
  | Times B C => S (tsize B + tsize C)
  | Delay B => 1
  | Box B => S (tsize B)
  | Fix B => S (tsize B)
  end.

Lemma tsize_subst i A B :  tsize (tsubst i A (Delay B)) = tsize A.
Proof.
  generalize dependent i. generalize dependent B. induction A;intros;simpl; eauto.
  - destruct (i0 =? i); eauto.
Qed.


Equations vrel (nu : nat) (A : type) : heapseq -> store ->  term -> Prop
  by wf (nu ,tsize A)  :=
vrel nu (Plus A B) Hs s t :=
    (exists v, t = in1 v /\ vrel nu A Hs s v)
    \/ (exists v, t = in2 v /\ vrel nu B Hs s v);
vrel nu (Times A B) Hs s t :=
    exists v1 v2, t = pair v1 v2 /\ vrel nu A Hs s v1
                  /\ vrel nu B Hs s v2;
                    vrel nu (Arrow A B) Hs s t :=
      exists t', t = abs t' /\
                 forall d, d <= nu -> forall Hs' s', heapseq_le Hs Hs' -> store_le (gc s) s' -> closed_heapseq Hs' -> closed_store s' ->
                                                     forall v, vrel (nu - d) A  Hs' s' v -> closed_term v ->
      forall s'', tick_le s' s'' -> closed_store s'' ->
      exists w s''', {sub_term t' v, s''} ⇓ {w, s'''} /\
                           vrel (nu-d) B Hs' s''' w;
                   
vrel 0 (Delay B) Hs s t := exists l, t = ref l;
vrel (S nu) (Delay B) Hs s t :=
         exists l , t = ref l /\
                    exists u, store_mapsto l u s /\
                    forall s', tick_le (store_tick s (hd Hs)) s' -> closed_store s' ->
                               exists w s'', {u, s'} ⇓ {w, s''} /\ vrel nu B (tl Hs) s'' w;
vrel nu (Fix B) Hs s t := exists v, t = into v /\
                                   vrel nu (tsubst 0 B (Delay (Fix B))) Hs s v;
vrel nu (Box B) Hs s t := exists t', t = box t' /\ forall Hs', closed_heapseq Hs' ->
   forall s', closed_store s' ->
      exists w s'', {t', s'} ⇓ {w, s''} /\
                     vrel nu B Hs' s'' w;
vrel nu Unit Hs s t := t = unit;
vrel nu Nat Hs s t := exists n, t = natlit n;
vrel _ _ _ _ _ := False
.

Next Obligation.
  apply Subterm.right_lex. lia.
Qed. 
Next Obligation.
  apply Subterm.right_lex. lia.
Qed.
Next Obligation.
  apply Subterm.right_lex. lia.
Qed.
Next Obligation.
  apply Subterm.right_lex. lia.
Qed.
Next Obligation.
  destruct d.
  + rewrite Nat.sub_0_r. apply Subterm.right_lex. lia.
  + destruct nu.
  - apply Subterm.right_lex. lia.
  - apply Subterm.left_lex. lia.
Qed.
Next Obligation.
  destruct d.
  + rewrite Nat.sub_0_r. apply Subterm.right_lex. lia.
  + destruct nu.
  - apply Subterm.right_lex. lia.
  - apply Subterm.left_lex. lia.
Qed.

Next Obligation.
  rewrite tsize_subst. apply Subterm.right_lex. lia.
Qed.

  
Definition trel (nu : nat) (A : type) (Hs : heapseq) (s : store) (t : term) : Prop :=
  forall s', tick_le s s' -> closed_store s' -> exists v s'',
                     {t, s'} ⇓ {v, s''} /\ vrel nu A Hs s'' v.

(* Below we give characterisations of vrel so that we don't need to
   work with vreln. *)


Lemma vrel_arrow A B nu Hs s t :
  vrel nu (Arrow A B) Hs s t <-> (exists u, t = abs u /\
     forall nu' Hs' s', nu' <= nu -> heapseq_le Hs Hs' -> store_le (gc s) s' -> closed_heapseq Hs'
                    -> closed_store s' ->
                    forall v, vrel nu' A Hs' s' v -> closed_term v -> trel nu' B Hs' s' (sub_term u v)).

Proof.
  simp vrel. split;intros.
  - autodest. exists x. split. reflexivity. intros.
    assert (nu - nu' <= nu) as D by lia.
    assert (nu - (nu - nu') = nu') as N by lia. rewrite <- N in H5.
    unfold trel. intros.
    remember (H0 (nu - nu') D Hs' s' H1 H2 H3 H4 v H5 H6 s'0 H7 H8) as As.
    clear HeqAs. autodest. exists x0. exists x1. subst. rewrite N in *. eauto.
  - autodest. exists x. split. reflexivity. intros.
    assert (nu - d <= nu) as D by lia.
    assert (nu - (nu - d) = d) as N by lia. 
    unfold trel. intros.
    remember (H0 (nu - d) Hs' s' D H1 H2 H3 H4 v H5 H6 s'' H7 H8) as As.
    clear HeqAs. autodest.
Qed.


Lemma vrel_plus A B nu Hs s t : vrel nu (Plus A B) Hs s t <->
                               (exists v, t = in1 v /\ vrel nu A Hs s v)
                               \/ (exists v, t = in2 v /\ vrel nu B Hs s v).
Proof.
  simp vrel. tauto.
Qed.



Lemma vrel_times A B nu Hs s t : vrel nu (Times A B) Hs s t <->
                                exists v1 v2, t = pair v1 v2 /\ vrel nu A Hs s v1
                                       /\ vrel nu B Hs s v2.
Proof.
    simp vrel. tauto.
Qed.


Lemma vrel_mu A nu Hs s t : vrel nu (Fix A) Hs s t <->
                           exists v, t = into v /\ vrel nu (tsubst 0 A (Delay (Fix A))) Hs s v.
Proof.
    simp vrel. tauto.
Qed.



Lemma vrel_val : forall A nu Hs s t, vrel nu A Hs s t -> isvalue t.
Proof.
  intro A. remember (tsize A) as N. generalize dependent A.
  induction (lt_wf N) as [N _ IH]. intro A.
  destruct A;intros; simp vrel in *; subst; autodest.
  - constructor.
    + eapply IH in H0;eauto. simpl. lia.
    + eapply IH in H1;eauto. simpl. lia.
  - constructor. eapply IH in H0;eauto. simpl. lia.
  - constructor. eapply IH in H0;eauto. simpl. lia.
  - destruct nu; simp vrel in *; autodest.
  - constructor. eapply IH in H0;eauto. simpl. rewrite tsize_subst. lia.
Qed.  
      

Lemma vrel_delay A nu Hs s t :
  vrel (S nu) (Delay A) Hs s t <->
  exists l u, t = ref l /\ store_mapsto l u s /\ trel nu A (tl Hs) (store_tick s (hd Hs)) u.
Proof.
  simp vrel. split;intros;autodest.
Qed.

Lemma vrel_box A nu Hs s t :
  vrel nu (Box A) Hs s t <-> (exists t', t = box t' /\
                          forall Hs', closed_heapseq Hs' -> trel nu A Hs' (None, heap_empty) t').
Proof.
  simp vrel. split;simpl;intros;autodest.
  - exists x. split. auto. unfold trel. intros. 
    remember (H0 Hs' H s' H2) as T. autodest. 
  - exists x. split. auto. unfold trel in *. intros. 
    remember (H0 Hs' H s' (tick_le_empty s') H1) as T. autodest. 
Qed.


Lemma vrel_unit Hs nu s t :
  vrel nu Unit Hs s t <-> t = unit.
Proof.
  simp vrel. auto.
Qed.


Lemma vrel_nat Hs nu s t :
  vrel nu Nat Hs s t <-> exists n, t = natlit n.
Proof.
  simp vrel. auto.
Qed.

Lemma vrel_var nu i Hs s t :
  vrel nu (TypeVar i) Hs s t <-> False.
Proof.
  simp vrel. auto.
Qed.

Lemma vrel_delay_nil A Hs s t :
  vrel 0 (Delay A) Hs s t <-> exists l, t = ref l.
Proof.
  simp vrel. auto.
Qed .

Hint Rewrite vrel_delay_nil vrel_delay vrel_var vrel_nat vrel_unit vrel_times vrel_plus vrel_arrow vrel_box vrel_mu : vrel'.


Import ListNotations.

Inductive crel : forall {ty}, nat -> ctx ty -> heapseq -> store -> sub -> Prop :=
| crel_empty nu Hs s : crel nu ctx_empty Hs s nil
| crel_var nu ty (G : ctx ty) Hs s g A t : vrel nu A Hs s t -> crel nu G Hs s g ->
                           crel nu (ctx_var G A) Hs s (Some t :: g)
| crel_skip nu ty (G : ctx ty) Hs s g : crel nu G Hs s g ->
                              crel nu (ctx_skip G) Hs s (None :: g)
| crel_tick nu G Hs g hn h: 
    crel (S nu) G (cons h Hs) (None, hn) g ->
    crel nu (ctx_tick G) Hs (Some hn, h) g
.

Hint Constructors crel : core.
