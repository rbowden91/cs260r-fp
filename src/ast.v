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

(* XXX remove this *)
Definition s_prop := nat.

Definition addr := nat.

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
| value: forall (t : Type), t -> expr t
| read: forall (t: Type), var t -> expr t
| cond: forall t, expr bool -> expr t -> expr t -> expr t
.

(*
 * statements don't
 *)
Inductive stmt: Type :=
| block: list stmt -> stmt
| start: forall (pt : Type), Proc pt unit -> expr pt -> stmt
| assign: forall t, var t -> expr t -> stmt
| load: forall t, var t -> lock t -> stmt
| store: forall t, lock t -> expr t -> stmt
| scope: stmt -> stmt
| if_: expr bool -> stmt -> stmt -> stmt
| while: expr bool -> stmt -> stmt
| call: forall (pt : Type) rt, var rt -> Proc pt rt -> expr pt -> stmt
| local: forall t, var t -> expr t -> stmt
| return_: forall t, expr t -> stmt
| getlock: forall t, lock t -> stmt
| putlock: forall t, lock t -> stmt
with

(*
 * procs both take and produce values
 *)
(*Inductive*) Proc: Type -> Type -> Type :=
| proc: forall pt rt, var pt -> stmt -> Proc pt rt
.


(*
 * Extended/sugary AST forms
 *)

Definition coqcall {ta tr : Set} (f : ta -> tr) (x : ta): expr tr :=
   value tr (f x)
.

Definition skip: stmt := block nil.

