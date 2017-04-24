Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

Require Import ast.

(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                            logic                             *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

(*

a bunch of stuff that was wrong used to live right here

*)

Inductive ExprHoare: forall t, Prop -> Expr t -> (t -> Prop) :=
| ExprTriple: forall t p s q, ExprHoare t p s q.

Inductive StmtHoare: Prop -> Stmt -> Prop -> Prop :=
| StmtTriple: forall p s q, StmtHoare p s q.

Inductive ProcHoare: forall pt rt,
      (pt -> Prop) -> Proc pt rt -> (pt -> rt -> Prop) -> Prop :=
| ProcTriple: forall pt rt p s q, ProcHoare pt rt p s q.


