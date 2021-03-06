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

Inductive ExprHoare: forall (t: type), Prop -> expr -> (value -> Prop) :=
| ExprTriple: forall t p s q, ExprHoare t p s q.

Inductive StmtHoare: Prop -> stmt -> Prop -> Prop :=
| StmtTriple: forall p s q, StmtHoare p s q.

Inductive ProcHoare: forall (pt rt: type),
      (value -> Prop) -> proc -> (value -> value -> Prop) ->
	Prop :=
| ProcTriple: forall pt rt p s q, ProcHoare pt rt p s q.


