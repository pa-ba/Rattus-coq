(** This module defines the syntax of terms, values, and types in
Rattus. *)


From Coq Require Export Nat.


Definition loc : Set := nat.
Definition index := nat.

(* Types *)
Inductive type : Set :=
(* Standard λ-calculus with sums and products *)
| Unit    : type
| Nat     : type
| TypeVar : index -> type
| Times   : type -> type -> type
| Plus    : type -> type -> type
| Arrow   : type -> type -> type
(* Reactive types *)
| Delay   : type -> type
| Box     : type -> type 
(* Temporal recursive types *)
| Fix     : type -> type.

Bind Scope type_scope with type.
Open Scope type_scope.

(* Notation for pretty types *)


(*  Terms  *)
Inductive term :  Type :=
(* λ-calculus with sums and products *)
| var     : index -> term
| unit    : term
| natlit  : nat -> term
| add     : term -> term -> term
| abs     : term -> term
| letin   : term -> term -> term
| app     : term -> term -> term 
| pair    : term -> term -> term
| pr1     : term -> term
| pr2      : term -> term
| in1     : term -> term
| in2     : term -> term
| case    : term -> term -> term -> term
(* Reactive terms *)                                                                
| delay   : term -> term
| adv     : term -> term
| ref     : loc  -> term
| box     : term -> term
| unbox   : term -> term
(* Temporal recursive terms *)                           
| out     : term -> term
| into    : term -> term
| fixp    : term -> term.

Inductive isvalue : term -> Prop :=
| value_unit : isvalue unit
| value_nat n : isvalue (natlit n)
| value_ref l : isvalue (ref l)
| value_abs t : isvalue (abs t)
| value_box t : isvalue (box t)
| value_into v : isvalue v -> isvalue (into v)
| value_pair v1 v2 : isvalue v1 -> isvalue v2 -> isvalue (pair v1 v2)
| value_in1 v: isvalue v -> isvalue (in1 v)
| value_in2 v: isvalue v -> isvalue (in2 v).
                       
Hint Constructors isvalue : core.
