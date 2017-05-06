Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                             ast                              *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

(*
 * abstract syntax the code is written in
 *)

(* types are the types of values we can touch directly *)
Inductive type :=
| t_unit: type
| t_nat: type
| t_bool: type
| t_pair: type -> type -> type
| t_list: type -> type
| t_lock: type -> type
.

(* variables are identified with numbers *)
Inductive var: type -> Type :=
| mkvar: forall t, nat -> var t
.

(* locks are a special class of variables *)
Inductive lock: type -> Type :=
| mklock : forall t, nat -> bool -> lock t
.

Inductive value: type -> Type :=
| v_unit: value t_unit
| v_nat (n: nat): value t_nat
| v_bool (b: bool): value t_bool
| v_pair (ta: type) (a: value ta) (tb: type) (b: value tb):
     value (t_pair ta tb)
| v_list (t: type) (l: list (value t)): value (t_list t)
| v_lock (t: type) (l: lock t): value (t_lock t)
.

Inductive invariant : Type :=
(* Just an example *)
| nat_inv : invariant
.

(*
 * expressions produce values
 *)
Inductive expr: type -> Type :=
| e_value: forall (t : type), value t -> expr t
| e_read: forall (t: type), var t -> expr t
| e_cond: forall t, expr t_bool -> expr t -> expr t -> expr t
.

(*
 * statements don't
 *)
Inductive stmt: Type :=
| s_block: list stmt -> stmt
| s_start: forall (pt : type), proc pt t_unit -> expr pt -> stmt
| s_assign: forall t, var t -> expr t -> stmt
| s_load: forall t, var t -> lock t -> stmt
| s_store: forall t, lock t -> expr t -> stmt
| s_scope: stmt -> stmt
| s_if: expr t_bool -> stmt -> stmt -> stmt
| s_while: expr t_bool -> stmt -> stmt
| s_call: forall (pt : type) rt, var rt -> proc pt rt -> expr pt -> stmt
| s_local: forall t, var t -> expr t -> stmt
| s_return: forall t, expr t -> stmt
| s_getlock: forall t, lock t -> stmt
| s_putlock: forall t, lock t -> stmt
with

(*
 * procs both take and produce values
 *)
(*Inductive*) proc: type -> type -> Type :=
| mkproc: forall pt rt, var pt -> stmt -> proc pt rt
.


(*
 * Extended/sugary AST forms
 *)

Definition v_true: value t_bool := v_bool true.
Definition v_false: value t_bool := v_bool false.

(* doesn't quite work any more
Definition e_coqcall {ta tr : type} (f : ta -> tr) (x : ta): expr tr :=
   e_value tr (f x)
.
*)

Definition s_skip: stmt := s_block nil.

