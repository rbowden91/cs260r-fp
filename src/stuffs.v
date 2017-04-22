Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.

(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                             base                             *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

(*
 * base definitions
 *)


(* Use nat as a standin for the data *)
Definition bytes : Type := (nat * nat).



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

Inductive Var: Type -> Type :=
| var: forall t, t -> Var t
.

(*
 * expressions produce values
 *)
Inductive Expr: Type -> Type :=
| value: forall t, t -> Expr t
| read: forall t, Var t -> Expr t
| cond: forall t, Expr bool -> Expr t -> Expr t -> Expr t
with

(*
 * statements don't
 *)
(*Inductive*) Stmt: Type :=
| block: list Stmt -> Stmt
| assign: forall t, Var t -> Expr t -> Stmt
| if_: Expr bool -> Stmt -> Stmt -> Stmt
| while: Expr bool -> Stmt -> Stmt
| call: forall pt rt, Var rt -> Proc rt pt -> Expr pt -> Stmt
with

(*
 * procs both take and produce values
 *)
(*Inductive*) Proc: Type -> Type -> Type :=
| proc: forall pt rt, Proc pt rt
.


(*
 * Extended/sugary AST forms
 *)

Definition coqcall {ta tr} (f : ta -> tr) (x : ta): Expr tr :=
   value tr (f x)
.

Definition skip: Stmt := block nil.


(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                            logic                             *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

Class Logic (T : Type) := {
   state: Type;
   eval: Stmt -> state -> state;
   evalproc: forall pt rt, Proc pt rt -> pt -> state -> (state * rt);
}.

Context {LT : Type}.
Instance logic_instance : Logic LT := {
}.
Admitted.

Inductive StmtHoare : Stmt -> Prop :=
| StmtTriple p (s : Stmt) q: forall x1 x2,
     (p -> (eval s x1) = x2 -> q) -> StmtHoare s.

Inductive ProcHoare: forall pt rt, Proc pt rt -> Prop :=
| ProcTriple pt rt (p : pt -> Prop) (s : Proc pt rt)  q: forall x1 x2 a r,
     (p a -> (evalproc pt rt s a x1) = (x2, r) -> q a r) -> ProcHoare pt rt s
.

Check ProcTriple.

(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                             vfs                              *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

(*
 * ghost state traces for vfs-level specifications
 *)

Section filetraces.

Inductive fileop: Type :=
| FileWrite: bytes -> nat -> fileop
| FileTruncate: nat -> fileop
.

Inductive file_trace: nat -> list fileop -> Prop :=
| FileTrace: forall j ops, j <= length ops -> file_trace j ops
.

End filetraces.

Section dirtraces.

Inductive dirop: Set :=
| DirCreate: string -> dirop
| DirUnlink: string -> dirop
.

Inductive dir_trace: nat -> list dirop -> Prop :=
| DirTrace: forall j ops, j <= length ops -> dir_trace j ops
.

End dirtraces.

(*
 * vfs objects
 *)

Section vfsobjects.

Class vnodeclass (vnode : Type) := {
  dirtrace_of_vnode: vnode -> (exists j ops, dir_trace j ops);

  VOP_LOOKUP: Proc (vnode * string) vnode;

  foo: Proc unit unit;
  foo_spec: ProcHoare unit unit foo;
(*
     ProcTriple unit unit (fun _ => True) foo (fun _ _ => True);
*)
(* doesn't work
  lookup_spec: forall t,
     ProcTriple
        (vnode * string) vnode
        (fun a => let (vn, name) := a in dirtrace_of_vnode vn = t)
        (VOP_LOOKUP)
        (fun a r => let (vn, name) := a in dirtrace_of_vnode vn = t);
*)

  VOP_CREATE: Proc (vnode * string) vnode;
  VOP_UNLINK: Proc (vnode * string) unit;
  VOP_READ: Proc (vnode * nat * nat) (bytes * nat)%type;
  VOP_WRITE: Proc (vnode * bytes * nat) unit;
  VOP_TRUNCATE: Proc (vnode * nat) unit;
  VOP_FSYNC: Proc vnode unit;
}.

Class fsclass (vfs : Type) := {
  vnode: Type;
  vnode_is_vnodeclass: vnodeclass vnode;

  VFS_GETROOT: Proc vfs vnode;
  VFS_SYNC: Proc vfs unit;
  newfs: Proc unit unit;
}.

End vfsobjects.
