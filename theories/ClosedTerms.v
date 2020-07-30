From Coq Require Import Omega Program.

From Rattus Require Export Substitutions.
From Rattus Require Import Tactics.

Open Scope nat.

(* This module

   - gives the definition of closed terms,a

   - show that for closed u and \gamma, we have that 

        (t \gamma)[u/x] = t (\gamma[x \mapsto u]) 

   - shows that t [u/x] is closed if (abs t) and u are
*)


(* fvars b t indicates that t only contains free variables i with i < b *)

Inductive fvars : index -> term -> Prop :=
| fvars_var b i : i < b -> fvars b (var i)
| fvars_unit b : fvars b unit
| fvars_natlit b n : fvars b (natlit n)
| fvars_add b t1 t2 : fvars b t1 -> fvars b t2 -> fvars b (add t1 t2)                           
| fvars_abs b t : fvars (S b) t -> fvars b (abs t)
| fvars_letin b t1 t2 : fvars b t1 ->fvars (S b) t2 -> fvars b (letin t1 t2)                                         
| fvars_app b t1 t2 : fvars b t1 -> fvars b t2 -> fvars b (app t1 t2)
| fvars_pair b t1 t2 : fvars b t1 -> fvars b t2 -> fvars b (pair t1 t2)
| fvars_pr1 b t : fvars b t -> fvars b (pr1 t)
| fvars_pr2 b t : fvars b t -> fvars b (pr2 t)
| fvars_in1 b t : fvars b t -> fvars b (in1 t)
| fvars_in2 b t : fvars b t -> fvars b (in2 t)
| fvars_case b t t1 t2 : fvars b t ->  fvars (S b) t1 -> fvars (S b) t2 -> fvars b (case t t1 t2)
| fvars_delay b t : fvars b t -> fvars b (delay t)
| fvars_adv b t : fvars b t -> fvars b(adv t)
| fvars_ref b l : fvars b (ref l)
| fvars_box b t : fvars b t -> fvars b (box t)
| fvars_unbox b t : fvars b t -> fvars b (unbox t)
| fvars_into b t : fvars b t -> fvars b (into t)
| fvars_out b t : fvars b t -> fvars b (out t)
| fvars_fixp b t : fvars (S b) t -> fvars b (fixp t).

Hint Constructors fvars : core.

Notation closed_term := (fvars 0).

Inductive fvar_sub_none : index -> sub -> Prop :=
| fvar_sub_none_0 g : fvar_sub_none 0 g
| fvar_sub_none_succ i g : fvar_sub_none i g -> fvar_sub_none (S i) (None :: g).

Hint Constructors fvar_sub_none : core.

  

Lemma fvar_var_id i : forall b g, fvar_sub_none b g -> i < b -> sub_lookup g i = None.
Proof.
  induction i;intros.
  - inversion H;subst. inversion H0. auto.
  - simpl. inversion H. subst. inversion H0. eapply IHi. eassumption. omega.
Qed.



Lemma sub_id i g t : fvar_sub_none i g -> fvars i t -> sub_app g t = t.
Proof.
  intros N F. generalize dependent g. 
  induction F;intros;
    try solve[simpl;try first[reflexivity| erewrite IHF;eauto| erewrite IHF1,IHF2;eauto]].
  - simpl. erewrite fvar_var_id; eauto.
  - simpl. erewrite IHF1,IHF2,IHF3;eauto.
Qed.

(* Substitution application is the identity on closed terms *)

Lemma sub_closed_id g t : closed_term t -> sub_app g t = t.
Proof.
  intros C. destruct g. erewrite sub_id;eauto.
  eapply sub_id. apply fvar_sub_none_0. assumption.
Qed. 
      
  
Inductive closed_sub : sub -> Prop :=
| closed_sub_nil : closed_sub nil
| closed_sub_some t g : closed_term t -> closed_sub g -> closed_sub (Some t :: g)
| closed_sub_none g : closed_sub g -> closed_sub (None :: g).


  
(* merge two non-overlapping substitutions *)
Inductive merge_sub : sub -> sub -> sub -> Prop :=
| merge_sub_nil_left g : merge_sub nil g g
| merge_sub_nil_right g : merge_sub g nil g
| merge_sub_none g g1 g2 : merge_sub g1 g2 g -> merge_sub (None :: g1) (None :: g2) (None :: g)
| merge_sub_left g g1 g2 t :  merge_sub g1 g2 g -> merge_sub (Some t :: g1) (None :: g2) (Some t :: g)
| merge_sub_right g g1 g2 t : merge_sub g1 g2 g -> merge_sub (None :: g1) (Some t :: g2) (Some t :: g).

Hint Constructors merge_sub closed_sub : core.

Lemma closed_sub_term t g : closed_sub (Some t :: g) -> closed_term t.
Proof.
  intros C. inversion C. subst. assumption.
Qed.

Lemma merge_sub_var1 i g1 g2 g : merge_sub g1 g2 g -> sub_lookup g1 i = None ->
                                  exists t, sub_lookup g2 i = t /\ sub_lookup g i = t.
Proof.
  generalize dependent g1; generalize dependent g2; generalize dependent g.
  induction i;intros.
  - destruct H; eauto.
  - destruct H;eauto; simpl in H0; inversion H0;
      pose (IHi g g2 g1 H H0) as IH;eauto.
Qed.

Lemma sub_lookup_succ x g i : sub_lookup (x :: g) (S i) = sub_lookup g i .
Proof.
  unfold sub_lookup. auto.
Qed.

Lemma merge_sub_var2 i g1 g2 g t : merge_sub g1 g2 g -> sub_lookup g1 i = Some t ->
                                   sub_lookup g2 i = None /\ sub_lookup g i = Some t.
Proof.
  split; generalize dependent g1; generalize dependent g2; generalize dependent g.
  - induction i;intros.
    + destruct H;eauto; simpl in H0; inversion H0.
    + destruct H;eauto; simpl in H0; inversion H0;simpl;rewrite sub_lookup_succ; erewrite IHi;eauto.
  - induction i;intros.
    + destruct H;eauto; simpl in H0; inversion H0.
    + destruct H;eauto; simpl in H0; inversion H0;simpl;rewrite sub_lookup_succ; erewrite IHi;eauto.
Qed.
  


Lemma sub_lookup_closed g i t : closed_sub g -> sub_lookup g i = Some t -> closed_term t.
Proof.
  generalize dependent g. induction i;intros.
  - unfold sub_lookup in *. destruct g; simpl in H0; try destruct o; inversion H0; subst. eauto using closed_sub_term.
  - dependent destruction H; subst; simpl in H0. inversion H0. inversion H1. eauto. eauto.
Qed.



Lemma merge_sub_app t : forall g1 g2 g , closed_sub g1 -> merge_sub g1 g2 g -> sub_app g2 (sub_app g1 t) = sub_app g t.
Proof.
  induction t;intros;try solve[auto|simpl; erewrite IHt;eauto|simpl;erewrite IHt1, IHt2;eauto].
  - simpl. remember (sub_lookup g1 i) as r1.
    symmetry in Heqr1. destruct r1. 
    + remember (merge_sub_var2 i g1 g2 g t H0 Heqr1) as M. destruct M. erewrite e0.
      eauto using sub_closed_id, sub_lookup_closed.
    + remember (merge_sub_var1 i g1 g2 g H0 Heqr1) as M. destruct M as [t M].
      destruct M as [M1 M2]. simpl. rewrite M1, M2. reflexivity.
  - simpl;erewrite IHt1, IHt2, IHt3;eauto.
Qed.

(* 
The lemma below proves that
(t \gamma)[u/x] = t (\gamma[x \mapsto u])
*)

Lemma sub_term_merge g t u :
  closed_sub g -> sub_term (sub_app (None :: g) t) u = sub_app (Some u :: g) t.
Proof.
  intros C. unfold sub_term. apply merge_sub_app; eauto.
Qed.


Lemma fvars_up i j t : i <= j -> fvars i t -> fvars j t.
Proof.
  intros I F. generalize dependent j. induction F;intros j;eauto.
  - constructor. omega.
  - constructor. apply IHF. omega.
  - constructor. apply IHF1. omega. apply IHF2. omega.
  - constructor. apply IHF1. omega. apply IHF2. omega. apply IHF3. omega.
  - constructor. apply IHF. omega.
Qed.



Lemma closed_fvars i t : closed_term t -> fvars i t.
Proof.
  intros C. eapply fvars_up in C.
  eassumption. omega.
Qed.


(* Below we prove that applying a substitution with n closed terms to
   a term with n free variables (fvar n t) results in a closed term.
   *)

(* full_sub l s g indicates that g has mappings for variables i with l
<= i < l + s. *)

Inductive full_sub : index -> index -> sub -> Prop :=
| full_sub_empty : full_sub 0 0 nil
| full_sub_var_0 g t s :
    full_sub 0 s g -> full_sub 0 (S s) (Some t :: g)
| full_sub_skip l s g x :
    full_sub l s g -> full_sub (S l) s  (x :: g).

(* bvars l s b t indicates that t only contains free variables i with
 i < b or with l <= i < l + s *)

Inductive bvars : index -> index -> index -> term -> Prop :=
| bvars_var_between l s b i : l <= i < l + s -> bvars l s b (var i)
| bvars_var_below l s b i : i < b -> bvars l s b (var i)
| bvars_unit l s b : bvars l s b unit
| bvars_natlit l b s n : bvars l s b (natlit n)
| bvars_add l s b t1 t2 : bvars l s b t1 -> bvars l s b t2 -> bvars l s b (add t1 t2)
| bvars_abs l s b t : bvars (S l) s (S b) t -> bvars l s b (abs t)
| bvars_letin l s b t1 t2 : bvars l s b t1 -> bvars (S l) s (S b) t2 -> bvars l s b (letin t1 t2)
| bvars_app l s b t1 t2 : bvars l s b t1 -> bvars l s b t2 -> bvars l s b (app t1 t2)
| bvars_pair l s b t1 t2 : bvars l s b t1 -> bvars l s b t2 -> bvars l s b (pair t1 t2)
| bvars_pr1 l b s t : bvars l s b t -> bvars l s b (pr1 t)
| bvars_pr2 l s b t : bvars l s b t -> bvars l s b (pr2 t)
| bvars_in1 l s b t : bvars l s b t -> bvars l s b (in1 t)
| bvars_in2 l s b t : bvars l s b t -> bvars l s b (in2 t)
| bvars_case l s b t t1 t2 : bvars l s b t ->  bvars (S l) s (S b) t1 -> bvars (S l) s (S b) t2 -> bvars l s b (case t t1 t2)
| bvars_delay l s b t : bvars l s b t -> bvars l s b (delay t)
| bvars_adv l s b t : bvars l s b t -> bvars l s b (adv t)
| bvars_ref l s b l' : bvars l s b (ref l')
| bvars_box l s b t : bvars l s b t -> bvars l s b (box t)
| bvars_unbox l s b t : bvars l s b t -> bvars l s b (unbox t)
| bvars_into l s b t : bvars l s b t -> bvars l s b (into t)
| bvars_out l s b t : bvars l s b t -> bvars l s b (out t)
| bvars_fixp l s b t : bvars (S l) s (S b) t -> bvars l s b (fixp t).

Hint Constructors full_sub bvars : core.


Lemma full_sub_nth s i l g :
  full_sub l s g -> i < l \/ l + s <= i  \/ exists t, sub_lookup g i = Some t.
Proof.
  intros F. generalize dependent i. induction F;intros.
  - right. left. omega.
  - destruct i.
    + right. right. exists t. cbv. reflexivity.
    + pose (IHF i). autodest. inversion H.
      right. left. omega.
  - destruct i.
    + left. omega.
    + pose (IHF i). autodest. left. omega. right. left. omega.
Qed.


Lemma full_sub_bvars l s b t g : closed_sub g -> bvars l s b t -> full_sub l s g -> fvars b (sub_app g t).
Proof.
  intros C B F. generalize dependent g.
  induction B;intros;simpl;eauto 10.
  - apply full_sub_nth with (i := i) in F.
    destruct F as [F | [F|(t & F)]];try omega.
    rewrite F. eauto using sub_lookup_closed, closed_fvars.
  - remember (sub_lookup g i) as N. destruct N.
    eauto using sub_lookup_closed, closed_fvars. eauto.
Qed.


Lemma fvars_bvars l b s t : fvars b t -> bvars l s b t.
Proof.
  intros F. generalize dependent l. induction F;eauto.
Qed.


Lemma fvars_bvars' l s t b : b = l + s -> fvars b t -> bvars l s l t.
Proof.
  intros E F. generalize dependent l. induction F;intros;eauto.
  - pose (dec_le l i) as L. destruct L.
    + apply bvars_var_between. omega.
    + apply bvars_var_below. omega.
  - constructor. apply IHF. omega.
  - constructor. apply IHF1. auto. apply IHF2. omega. 
  - constructor. apply IHF1. auto. apply IHF2. omega. apply IHF3. omega.
  - constructor. apply IHF. omega.
Qed.


Lemma full_sub_fvars b t g : closed_sub g -> fvars b t -> full_sub 0 b g -> closed_term (sub_app g t).
Proof.
  intros C B F. eapply fvars_bvars' in B. eapply full_sub_bvars;eauto. auto.
Qed.


Lemma sub_term_closed t u : fvars 1 t -> closed_term u -> closed_term (sub_term t u).
Proof.
  intros F C. eapply full_sub_fvars; eauto.
Qed.

