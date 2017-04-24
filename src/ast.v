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

(* locks are a special class of variables *)
Inductive Lock: Type :=
| lock: string -> Lock
.

(* variables are named with strings *)
Inductive Var: Type -> option Lock -> Type :=
| var: forall t, string -> t -> Var t None
| lockedvar t (name : string) (l : Lock): Var t (Some l)
.

(*
 * expressions produce values
 *)
Inductive Expr: Type -> Type :=
| value: forall t, t -> Expr t
| read: forall t l, Var t l -> Expr t
| cond: forall t, Expr bool -> Expr t -> Expr t -> Expr t
with

(*
 * statements don't
 *)
(*Inductive*) Stmt: Type :=
| block: list Stmt -> Stmt
| start: Stmt -> Stmt
| assign: forall t l, Var t l -> Expr t -> Stmt
| if_: Expr bool -> Stmt -> Stmt -> Stmt
| while: Expr bool -> Stmt -> Stmt
| call: forall pt rt l, Var rt l -> Proc pt rt -> Expr pt -> Stmt
| local: forall t, Var t None -> Stmt
| return_: forall t, Expr t -> Stmt
| getlock: Lock -> Stmt
| putlock: Lock -> Stmt
with

(*
 * procs both take and produce values
 *)
(*Inductive*) Proc: Type -> Type -> Type :=
| proc: forall pt rt, Var pt None -> Stmt -> Proc pt rt
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
Inductive StmtDeclaresVar: forall t l, Stmt -> Var t l -> bool -> Prop :=
| block_declares_var_nil: forall t l v,
     StmtDeclaresVar t l (block []) v false
| block_declares_var_cons_here: forall t l s ss v,
     StmtDeclaresVar t l s v true -> StmtDeclaresVar t l (block ss) v false ->
     StmtDeclaresVar t l (block (s :: ss)) v true
| block_declares_var_cons_nothere: forall t l s ss v b,
     StmtDeclaresVar t l s v false -> StmtDeclaresVar t l (block ss) v b ->
     StmtDeclaresVar t l (block (s :: ss)) v b
| start_declares_var: forall t l s v b,
     StmtDeclaresVar t l s v b ->
     StmtDeclaresVar t l (start s) v b
| assign_declares_var: forall t' l' t l v e v',
     StmtDeclaresVar t' l' (assign t l v e) v' false
| if_declares_var: forall t l e s1 s2 v b1 b2,
     StmtDeclaresVar t l s1 v b1 -> StmtDeclaresVar t l s2 v b2 ->
     StmtDeclaresVar t l (if_ e s1 s2) v (b1 || b2)
| while_declares_var: forall t l e s v b,
     StmtDeclaresVar t l s v b ->
     StmtDeclaresVar t l (while e s) v b
| call_declares_var: forall t' l' pt rt v p e v' b,
     ProcDeclaresVar t' l' pt rt p v' b ->
     StmtDeclaresVar t' l' (call pt rt None v p e) v' b
| local_declares_var: forall t v,
     StmtDeclaresVar t None (local t v) v true
| return_declares_var: forall t' l' t e v',
     StmtDeclaresVar t' l' (return_ t e) v' false
with
(*Inductive*) ProcDeclaresVar: forall t l pt rt, Proc pt rt -> Var t l -> bool -> Prop :=
| proc_declares_var_arg: forall pt rt s v,
     StmtDeclaresVar pt None s v false ->
     ProcDeclaresVar pt None pt rt (proc pt rt v s) v true
| proc_declares_var_nonarg_sametype: forall pt rt s v' v b,
     StmtDeclaresVar pt None s v b ->
     v <> v' ->
     ProcDeclaresVar pt None pt rt (proc pt rt v' s) v b
| proc_declares_var_nonarg_othertype: forall t l pt rt s v' v b,
     StmtDeclaresVar t l s v b ->
     t <> pt \/ l = None ->
     ProcDeclaresVar t l pt rt (proc pt rt v' s) v b
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
   (forall t l v (b : bool), StmtDeclaresVar t l s v b) /\
   (* (forall t, StmtLooseVars t s []) *) True.

Inductive ProcOk: forall pt rt, Proc pt rt -> Prop :=
| proc_ok: forall pt rt v s,
     StmtOk s ->
     ProcReturnOk pt rt (proc pt rt v s) ->
     ProcOk pt rt (proc pt rt v s)
.


