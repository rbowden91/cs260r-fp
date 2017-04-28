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

Inductive Invariant : Type -> Type :=
(* Just an example *)
| nat_inv : (s_prop * s_prop) -> Invariant nat
.

(* locks are a special class of variables *)
Inductive Lock: Type -> Type :=
| lock : forall t, Invariant t -> Lock t
.

(* variables are named with strings *)
Inductive Var: Type -> Type :=
| var: forall t, string -> t -> Var t
.

(*
 * expressions produce values
 *)
Inductive Expr: Type -> Type :=
| value: forall t, t -> Expr t
| read: forall t, Var t -> Expr t
| cond: forall t, Expr bool -> Expr t -> Expr t -> Expr t
.

(*
 * statements don't
 *)
Inductive Stmt: Type :=
| block: list Stmt -> Stmt
| start: forall pt, Proc pt unit -> Expr pt -> Stmt
| assign: forall t, Var t -> Expr t -> Stmt
| load: forall t, Var t -> Lock t -> Stmt
| store: forall t, Lock t -> Expr t -> Stmt
| if_: Expr bool -> Stmt -> Stmt -> Stmt
| while: Expr bool -> Stmt -> Stmt
| call: forall pt rt, Var rt -> Proc pt rt -> Expr pt -> Stmt
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

Definition coqcall {ta tr} (f : ta -> tr) (x : ta): Expr tr :=
   value tr (f x)
.

Definition skip: Stmt := block nil.

(*
 * well-formedness constraints
 *
 * this is (for now) chiefly about insisting that every variable is declared
 * exactly once. types are mostly enforced by the embedding. we ignore scopes
 * when checking for duplicate declarations, at least for now.
 *)

(* check that variable declarations are unique *)
Inductive StmtDeclaresVar: forall t, Stmt -> Var t -> bool -> Prop :=
| block_declares_var_nil: forall t v,
     StmtDeclaresVar t (block []) v false
| block_declares_var_cons_here: forall t s ss v,
     StmtDeclaresVar t s v true -> StmtDeclaresVar t (block ss) v false ->
     StmtDeclaresVar t (block (s :: ss)) v true
| block_declares_var_cons_nothere: forall t s ss v b,
     StmtDeclaresVar t s v false -> StmtDeclaresVar t (block ss) v b ->
     StmtDeclaresVar t (block (s :: ss)) v b
| start_declares_var: forall t s v b pt p e,
     StmtDeclaresVar t s v b ->
     StmtDeclaresVar t (start pt p e) v false
| assign_declares_var: forall t' t e e' v',
     StmtDeclaresVar t' (assign t e e') v' false
| load_declares_var: forall t' t v e v',
     StmtDeclaresVar t' (load t v e) v' false
| store_declares_var: forall t' t v e v',
     StmtDeclaresVar t' (store t v e) v' false
| if_declares_var: forall t e s1 s2 v b1 b2,
     StmtDeclaresVar t s1 v b1 -> StmtDeclaresVar t s2 v b2 ->
     StmtDeclaresVar t (if_ e s1 s2) v (b1 || b2)
| while_declares_var: forall t e s v b,
     StmtDeclaresVar t s v b ->
     StmtDeclaresVar t (while e s) v b
| call_declares_var: forall t' pt rt v p e v' b,
     ProcDeclaresVar t' pt rt p v' b ->
     StmtDeclaresVar t' (call pt rt v p e) v' b
| local_declares_var: forall t v e,
     StmtDeclaresVar t (local t v e) v true
| return_declares_var: forall t' t e v',
     StmtDeclaresVar t' (return_ t e) v' false
with
(*Inductive*) ProcDeclaresVar: forall t pt rt, Proc pt rt -> Var t -> bool -> Prop :=
| proc_declares_var_arg: forall pt rt s v,
     StmtDeclaresVar pt s v false ->
     ProcDeclaresVar pt pt rt (proc pt rt v s) v true
| proc_declares_var_nonarg_sametype: forall pt rt s v' v b,
     StmtDeclaresVar pt s v b ->
     v <> v' ->
     ProcDeclaresVar pt pt rt (proc pt rt v' s) v b
| proc_declares_var_nonarg_othertype: forall t pt rt s v' v b,
     StmtDeclaresVar t s v b ->
     t <> pt ->
     ProcDeclaresVar t pt rt (proc pt rt v' s) v b
.

(* check that variable uses are after declarations *)
(*
Inductive StmtLooseVars: forall t, Stmt -> list (Var t) -> Prop :=
| block_loose_vars_nil: forall t,
     StmtLooseVars t (block []) []
| (* TBD *)
*)


(* check that procedure returns are ok *)

Inductive StmtEndsInReturn: Stmt -> Type -> Prop :=
| block_ends_in_return: forall ss t e,
     StmtEndsInReturn (block (ss ++ [return_ t e])) t
| if_ends_in_return: forall s1 s2 t e,
     StmtEndsInReturn s1 t -> StmtEndsInReturn s2 t ->
     StmtEndsInReturn (if_ e s1 s2) t
| return_ends_in_return: forall t e,
     StmtEndsInReturn (return_ t e) t
with
(*Inductive*) ProcReturnOk: forall pt rt, Proc pt rt -> Prop :=
| proc_return_ok: forall pt rt v s,
     StmtEndsInReturn s rt ->
     ProcReturnOk pt rt (proc pt rt v s)
.

Definition StmtOk s : Prop :=
   (forall t v (b : bool), StmtDeclaresVar t s v b) /\
   (* (forall t, StmtLooseVars t s []) *) True.

Inductive ProcOk: forall pt rt, Proc pt rt -> Prop :=
| proc_ok: forall pt rt v s,
     StmtOk s ->
     ProcReturnOk pt rt (proc pt rt v s) ->
     ProcOk pt rt (proc pt rt v s)
.


