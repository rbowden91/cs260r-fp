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
Inductive Expr: Type -> Type :=
| value: forall (t : Type), t -> Expr t
| read: forall (t: Type), var t -> Expr t
| cond: forall t, Expr bool -> Expr t -> Expr t -> Expr t
.

(*
 * statements don't
 *)
Inductive Stmt: Type :=
| block: list Stmt -> Stmt
| start: forall (pt : Type), Proc pt unit -> Expr pt -> Stmt
| assign: forall t, var t -> Expr t -> Stmt
| load: forall t, var t -> lock t -> Stmt
| store: forall t, lock t -> Expr t -> Stmt
| scope: Stmt -> Stmt
| if_: Expr bool -> Stmt -> Stmt -> Stmt
| while: Expr bool -> Stmt -> Stmt
| call: forall (pt : Type) rt, var rt -> Proc pt rt -> Expr pt -> Stmt
| local: forall t, var t -> Expr t -> Stmt
| return_: forall t, Expr t -> Stmt
| getlock: forall t, lock t -> Stmt
| putlock: forall t, lock t -> Stmt
with

(*
 * procs both take and produce values
 *)
(*Inductive*) Proc: Type -> Type -> Type :=
| proc: forall pt rt, var pt -> Stmt -> Proc pt rt
.


(*
 * Extended/sugary AST forms
 *)

Definition coqcall {ta tr : Set} (f : ta -> tr) (x : ta): Expr tr :=
   value tr (f x)
.

Definition skip: Stmt := block nil.

