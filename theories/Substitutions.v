(** This module defines substitution of closed terms into open terms,
and substitution of a single closed type into an open type.  *)

From Coq Require Export List.

From Rattus Require Export RawSyntax.



(* Substitution in types *)
Fixpoint tsubst (j : index) (A : type) (B : type) : type :=
  match A with
  | TypeVar k  => if j =? k
                  then B
                  else TypeVar k
  | Times A1 A2    => Times (tsubst j A1 B) (tsubst j A2 B)
  | Plus A1 A2    => Plus (tsubst j A1 B) (tsubst j A2 B)
  | Arrow A1 A2    => Arrow (tsubst j A1 B) (tsubst j A2 B)
  | Delay A'       => Delay (tsubst j A' B)
  | Box A'       => Box (tsubst j A' B)
  | Fix A'       => Fix (tsubst (S j) A' B)
  | _          => A
  end.


(* = Terms = *)

Definition sub := list (option term).

Definition sub_lookup (g : sub) i := 
  match nth_error g i with
    | Some (Some t) => Some t
    | _ => None
  end.

Fixpoint sub_app (g : sub) (t : term) : term :=
  match t with
  | var j    => match sub_lookup g j with
                | Some t => t
                | None => var j
                end
  | abs t'   => abs (sub_app (None::g) t')
  | letin t1 t2 => letin (sub_app g t1) (sub_app (None::g) t2)
  | app t1 t2 => app (sub_app g t1) (sub_app g t2)
  | pair t1 t2 => pair (sub_app g t1) (sub_app g t2)
  | pr1 t'=> pr1 (sub_app g t')
  | pr2 t'=> pr2 (sub_app g t')
  | in1 t'=> in1 (sub_app g t')
  | in2 t'=> in2 (sub_app g t')
  | case t1 t2 t3 => case (sub_app g t1) (sub_app (None :: g) t2) (sub_app (None :: g) t3)
  | delay  t' => delay (sub_app g t')
  | adv  t' => adv (sub_app g t')
  | box  t'  => box (sub_app g t')
  | unbox  t' => unbox (sub_app g t')
  | into t'=> into (sub_app g t')
  | out t'=> out (sub_app g t')

  | fixp t'=> fixp (sub_app (None::g) t')
  | unit => unit
  | natlit n => natlit n
  | add t1 t2 => add (sub_app g t1) (sub_app g t2)
  | ref l => ref l
  end.

Import ListNotations.

(* substitute u into t *)
Definition sub_term (t u : term) : term := sub_app [ Some u ] t.


Inductive sub_empty : sub -> Prop :=
| sub_empty_nil : sub_empty nil
| sub_empty_cons g : sub_empty g -> sub_empty (None :: g).

Hint Constructors sub_empty : core.


Lemma sub_empty_app t g : sub_empty g -> sub_app g t = t.
Proof.
  generalize dependent g. induction t;intros;simpl;f_equal;eauto.

  generalize dependent g. generalize dependent (var i).
  induction i;intros; inversion H; simpl; eauto.
Qed.
