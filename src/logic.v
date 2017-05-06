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

Inductive ExprHoare: forall t, Prop -> expr t -> (value t -> Prop) :=
| ExprTriple: forall t p s q, ExprHoare t p s q.

Inductive StmtHoare: Prop -> stmt -> Prop -> Prop :=
| StmtTriple: forall p s q, StmtHoare p s q.

Inductive ProcHoare: forall (pt rt: type),
      (value pt -> Prop) -> proc pt rt -> (value pt -> value rt -> Prop) ->
	Prop :=
| ProcTriple: forall pt rt p s q, ProcHoare pt rt p s q.


