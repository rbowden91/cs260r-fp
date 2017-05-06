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

Inductive invariant : Type :=
(* Just an example *)
| nat_inv : invariant
.

(* locks are a special class of variables *)
Inductive lock: Type -> Type :=
| mklock : forall t, invariant -> lock t
.

(* variables are identified with numbers *)
Inductive var: Type -> Type :=
| mkvar: forall t, nat -> var t
.

(*
 * expressions produce values
 *)
Inductive expr: Type -> Type :=
| e_value: forall (t : Type), t -> expr t
| e_read: forall (t: Type), var t -> expr t
| e_cond: forall t, expr bool -> expr t -> expr t -> expr t
.

(*
 * statements don't
 *)
Inductive stmt: Type :=
| s_block: list stmt -> stmt
| s_start: forall (pt : Type), proc pt unit -> expr pt -> stmt
| s_assign: forall t, var t -> expr t -> stmt
| s_load: forall t, var t -> lock t -> stmt
| s_store: forall t, lock t -> expr t -> stmt
| s_scope: stmt -> stmt
| s_if: expr bool -> stmt -> stmt -> stmt
| s_while: expr bool -> stmt -> stmt
| s_call: forall (pt : Type) rt, var rt -> proc pt rt -> expr pt -> stmt
| s_local: forall t, var t -> expr t -> stmt
| s_return: forall t, expr t -> stmt
| s_getlock: forall t, lock t -> stmt
| s_putlock: forall t, lock t -> stmt
with

(*
 * procs both take and produce values
 *)
(*Inductive*) proc: Type -> Type -> Type :=
| mkproc: forall pt rt, var pt -> stmt -> proc pt rt
.


(*
 * Extended/sugary AST forms
 *)

Definition e_coqcall {ta tr : Set} (f : ta -> tr) (x : ta): expr tr :=
   e_value tr (f x)
.

Definition s_skip: stmt := s_block nil.

