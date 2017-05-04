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

Inductive Invariant : Set -> Type :=
(* Just an example *)
| nat_inv : (s_prop * s_prop) -> Invariant nat
.

(* locks are a special class of variables *)
Inductive Lock: Set -> Type :=
| lock : forall t, Invariant t -> Lock t
.

(* variables are named with strings *)
Inductive Var: Set -> Type :=
| var: forall t, string -> Var t
.

(*
 * expressions produce values
 *)
Inductive Expr: Set -> Type :=
| value: forall (t : Set), t -> Expr t
| read: forall t, Var t -> Expr t
| cond: forall t, Expr bool -> Expr t -> Expr t -> Expr t
.

(*
 * statements don't
 *)
Inductive Stmt: Type :=
| block: list Stmt -> Stmt
| start: forall (pt : Set), Proc pt unit -> Expr pt -> Stmt
| assign: forall t, Var t -> Expr t -> Stmt
| load: forall t, Var t -> Lock t -> Stmt
| store: forall t, Lock t -> Expr t -> Stmt
| if_: Expr bool -> Stmt -> Stmt -> Stmt
| while: Expr bool -> Stmt -> Stmt
| call: forall (pt : Set) rt, Var rt -> Proc pt rt -> Expr pt -> Stmt
| local: forall t, Var t -> Expr t -> Stmt
| return_: forall t, Expr t -> Stmt
| getlock: forall t, Lock t -> Stmt
| putlock: forall t, Lock t -> Stmt
with

(*
 * procs both take and produce values
 *)
(*Inductive*) Proc: Type -> Type -> Type :=
| proc: forall pt rt, Var pt -> Stmt -> Proc pt rt
.


(*
 * Extended/sugary AST forms
 *)

Definition coqcall {ta tr : Set} (f : ta -> tr) (x : ta): Expr tr :=
   value tr (f x)
.

Definition skip: Stmt := block nil.

