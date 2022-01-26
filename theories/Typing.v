(** This module defines the single-tick type system of the Rattus core
calculus 𝜆✓. *)

From Rattus Require Export Substitutions.

From Coq Require Import Lia Program.Equality NPeano.

(* Definition of well-formed types *)
Inductive wf_type : nat -> type -> Prop :=
| IT_Unit : forall Th,
    wf_type Th Unit
| IT_Nat  : forall Th,
    wf_type Th Nat
| IT_TypeVar : forall Th i,
    i < Th ->
    wf_type Th (TypeVar i)
| IT_Times : forall Th T1 T2,
    wf_type Th T1 ->
    wf_type Th T2 ->
    wf_type Th (Times T1 T2)
| IT_Plus : forall Th T1 T2,
    wf_type Th T1 ->
    wf_type Th T2 ->
    wf_type Th (Plus T1 T2)
| IT_Arrow : forall Th T1 T2,
    wf_type Th T1 ->
    wf_type Th T2 ->
    wf_type Th (Arrow T1 T2)
| IT_Delay : forall Th T,
    wf_type Th T ->
    wf_type Th (Delay T)
| IT_Box : forall Th T,
    wf_type Th T ->
    wf_type Th (Box T)
| IT_Fix : forall Th T,
    wf_type (S Th) T ->
    wf_type Th (Fix T).

(* A closed type is well-formed in the empty context *)
Definition closed_type (T : type) : Prop := wf_type 0 T.



Lemma closed_tsubst i A B : closed_type A -> tsubst i A B = A.
Proof.
  intros C. unfold closed_type in *. remember 0 as j.
  assert (j <= i) by (subst; apply NPeano.Nat.le_0_l).
  clear Heqj. generalize dependent i.

  induction C;intros;simpl;eauto;
    try solve[rewrite IHC1, IHC2;eauto|rewrite IHC;eauto].
  - assert (i0 <> i) as I by lia. rewrite <- NPeano.Nat.eqb_neq in I.
    rewrite I. reflexivity.
  - rewrite IHC. reflexivity. lia.
Qed.



(* Definition of stable types *)
Inductive stable : type -> Prop :=
| S_Unit : stable Unit
| S_Nat : stable Nat
| S_Times : forall T1 T2,
    stable T1 ->
    stable T2 ->
    stable (Times T1 T2)
| S_Plus : forall T1 T2,
    stable T1 ->
    stable T2 ->
    stable (Plus T1 T2)
| S_Box : forall T,
    stable (Box T).

#[global] Hint Constructors stable : core.

Fixpoint stableb (t : type) : bool :=
  match t with
  | Unit => true
  | Nat => true
  | Times t1 t2 => stableb t1 && stableb t2
  | Plus t1 t2 => stableb t1 && stableb t2
  | Box _ => true
  | _ => false
  end.


Lemma stableb_correct t : stableb t = true <-> stable t.
Proof.
  induction t; simpl;split;intros;eauto;try solve[inversion H].
  - apply andb_prop in H. destruct H. constructor ;[apply IHt1|apply IHt2];eauto.
  - inversion H. subst.  rewrite <- IHt1 in *. rewrite <- IHt2 in *. eauto using andb_true_intro.
  - apply andb_prop in H. destruct H. constructor ;[apply IHt1|apply IHt2];eauto.
  - inversion H. subst.  rewrite <- IHt1 in *. rewrite <- IHt2 in *. eauto using andb_true_intro.
Qed.

Inductive ctype := now | later.

Inductive ctx : ctype -> Set := 
| ctx_empty : ctx now
| ctx_var {ty} : ctx ty -> type -> ctx ty
| ctx_skip {ty} : ctx ty -> ctx ty
| ctx_tick : ctx now -> ctx later.



Fixpoint skip_later (G : ctx later) : ctx now :=
  match G with
  | ctx_tick G' => G'
  | @ctx_var later G' _ => ctx_skip (skip_later G')
  | @ctx_var now G' v => fun _ x => x
  | @ctx_skip now G' => fun _ x => x
  | @ctx_skip later G' => ctx_skip (skip_later G')
  end.

Fixpoint stabilize {i} (G : ctx i) : ctx now :=
  match G with
  | ctx_empty => ctx_empty
  | ctx_tick G' => stabilize G'
  | ctx_var G' t => if stableb t then ctx_var (stabilize G') t else ctx_skip (stabilize G')
  | ctx_skip G' => ctx_skip (stabilize G')
  end.


Fixpoint stabilize_later (G : ctx later) : ctx now :=
  match G with
  | ctx_tick G' => stabilize G'
  | @ctx_var later G' T => ctx_var (stabilize_later G') T
  | @ctx_var now G' v => fun _ x => x
  | @ctx_skip now G' => fun _ x => x
  | @ctx_skip later G' => ctx_skip (stabilize_later G')
  end.



Inductive ctx_lookup : forall {ty} , ctx ty -> nat -> type -> Prop :=
| ctx_zero ty (G : ctx ty)  T : ctx_lookup (ctx_var G T) 0 T
| ctx_succ ty (G : ctx ty) T T' n : ctx_lookup G n T -> ctx_lookup (ctx_var G T') (S n) T
| ctx_succ_skip ty (G : ctx ty) T  n : ctx_lookup G n T -> ctx_lookup (ctx_skip G ) (S n) T
| ctx_stable G T n : ctx_lookup G n T -> stable T -> ctx_lookup (ctx_tick G) n T.


Reserved Notation "G '⊢' e '∶' T" (at level 40). 
Inductive hastype : forall {ty}, ctx ty -> term -> type -> Prop :=
(* Simple λ-calculus with sums and products *)
| T_unit : forall ty (G : ctx ty),
    G ⊢ unit ∶ Unit
| T_nat : forall ty (G : ctx ty) n,
    G ⊢ natlit n ∶ Nat
| T_add : forall ty (G : ctx ty) t1 t2,
    G ⊢ t1 ∶ Nat -> G ⊢ t2 ∶ Nat -> G ⊢ add t1 t2 ∶ Nat
| T_var : forall ty (G : ctx ty) x T,
    ctx_lookup G x T ->
    G ⊢ var x ∶ T
| T_abs : forall (G : ctx now) t T1 T2,
    ctx_var G T1 ⊢ t ∶ T2 ->
    G ⊢ abs t ∶ (Arrow T1 T2)
| T_abs_tick : forall (G : ctx later) t T1 T2,
    ctx_var (stabilize_later G) T1 ⊢ t ∶ T2 ->
    G ⊢ abs t ∶ (Arrow T1 T2)
| T_app : forall ty (G : ctx ty) t1 t2 T1 T2,
    G ⊢ t1 ∶ (Arrow T1 T2) ->
    G ⊢ t2 ∶ T1 ->
    G ⊢ app t1 t2 ∶ T2
| T_letin : forall ty (G : ctx ty) t1 t2 T1 T2,
    G ⊢ t1 ∶ T1 ->
    ctx_var G T1 ⊢ t2 ∶ T2 ->
    G ⊢ letin t1 t2 ∶ T2
| T_pair : forall ty (G : ctx ty) t1 t2 T1 T2,
    G ⊢ t1 ∶ T1 ->
    G ⊢ t2 ∶ T2 ->
    G ⊢ pair t1 t2 ∶ (Times T1 T2)
| T_pr1 : forall ty (G : ctx ty) t T1 T2,
    G ⊢ t ∶ (Times T1 T2) ->
    G ⊢ pr1 t ∶ T1
| T_pr2 : forall ty (G : ctx ty) t T1 T2,
    G ⊢ t ∶ (Times T1 T2) ->
    G ⊢ pr2 t ∶ T2
| T_in1 : forall ty (G : ctx ty) t T1 T2,
    G ⊢ t ∶ T1 ->
    G ⊢ in1 t ∶ (Plus T1 T2)
| T_in2 : forall ty (G : ctx ty) t T1 T2,
    G ⊢ t ∶ T2 ->
    G ⊢ in2 t ∶ (Plus T1 T2)
| T_case : forall ty (G : ctx ty) t t1 t2 T T1 T2,
    G ⊢ t ∶ (Plus T1 T2) ->
    ctx_var G T1 ⊢ t1 ∶ T ->
    ctx_var G T2 ⊢ t2 ∶ T ->
    G ⊢ case t t1 t2 ∶ T
(* Reactive expressions *)
| T_delay : forall (G : ctx now) T t,
    ctx_tick G ⊢ t ∶ T ->
    G  ⊢ delay t ∶ Delay T
| T_delay_tick : forall (G : ctx later) T t,
    ctx_tick (stabilize_later G) ⊢ t ∶ T ->
    G  ⊢ delay t ∶ Delay T
| T_adv : forall G t T ,
    skip_later G ⊢ t ∶ Delay T ->
    G ⊢ adv t ∶ T
| T_box : forall i (G : ctx i) t T,
    stabilize G ⊢ t ∶ T ->
    G ⊢ box t ∶ (Box T)
| T_unbox : forall i (G : ctx i) t T,
    G ⊢ t ∶ Box T ->
    G ⊢ unbox t ∶ T
(* Temporal recursive expressions *)
| T_fix : forall i (G : ctx i) t T,
    (ctx_var (stabilize G) (Box (Delay T))) ⊢ t ∶ T ->
    G ⊢ fixp t ∶ T
| T_into : forall ty (G : ctx ty) t T,
    G ⊢ t ∶ tsubst 0 T (Delay (Fix T)) ->
    G ⊢ into t ∶ Fix T
| T_out : forall ty (G : ctx ty) t A B,
    B = tsubst 0 A (Delay (Fix A)) ->
    G ⊢ t ∶ Fix A ->
    G ⊢ out t ∶ B
 where "G '⊢' e '∶' T" := (hastype G e T) : type_scope.


#[global] Hint Constructors ctx_lookup hastype wf_type : core.

#[global] Hint Unfold closed_type : core.
