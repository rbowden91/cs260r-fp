Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

Require Import stringfacts.

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


(* For now, each unit of a file is a nat. *)
Definition bytes : Type := list nat.



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
| proc: forall pt rt, Stmt -> Proc pt rt
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

(* wrong
Inductive StmtHoare : Stmt -> Prop :=
| StmtTriple p (s : Stmt) q: forall x1 x2,
     (p -> (eval s x1) = x2 -> q) -> StmtHoare s.

Inductive ProcHoare: forall pt rt, Proc pt rt -> Prop :=
| ProcTriple pt rt (p : pt -> Prop) (s : Proc pt rt)  q: forall x1 x2 a r,
     (p a -> (evalproc pt rt s a x1) = (x2, r) -> q a r) -> ProcHoare pt rt s
.
*)

Inductive ExprHoare: forall t, Prop -> Expr t -> (t -> Prop) :=
| ExprTriple: forall t p s q, ExprHoare t p s q.

Inductive StmtHoare: Prop -> Stmt -> Prop -> Prop :=
| StmtTriple: forall p s q, StmtHoare p s q.

Inductive ProcHoare: forall pt rt,
      (pt -> Prop) -> Proc pt rt -> (pt -> rt -> Prop) -> Prop :=
| ProcTriple: forall pt rt p s q, ProcHoare pt rt p s q.

Check ProcTriple.

Check (
ProcTriple unit unit (fun _ => True) (proc unit unit skip) (fun _ _ => True)
).

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

(* why must this be a Type when dirop can be a Set? *)
Inductive fileop: Type :=
| FileWrite: bytes -> nat -> fileop
| FileTruncate: nat -> fileop
.

Inductive file_trace: Type :=
| FileTrace: forall j (ops : list fileop), j <= length ops -> file_trace
.

(*
 * This stuff is in specification space so I don't care how inefficient it is.
 *)

Function fileops_currentlength ops sofar :=
   match ops with
   | [] => sofar
   | op :: more => match op with
        | FileWrite bytes offset =>
             fileops_currentlength more (max sofar (offset + length bytes))
        | FileTruncate len =>
             fileops_currentlength more len
        end
   end.

(* why does coq have <=? but not >=? ...? *)

Function fileops_readbyte ops offset sofar :=
   match ops with
   | nil => sofar
   | op :: more => match op with
        | FileWrite bytes offset' =>
             fileops_readbyte more offset (
                if ((offset' <=? offset) && (offset <? offset' + length bytes))%bool then
                   nth (offset - offset') bytes sofar
                else
                    sofar
             )
        | FileTruncate _ =>
             fileops_readbyte more offset sofar
        end
   end.

Function fileops_readbytes ops len offset :=
   match len with
   | 0 => []
   | S len' => fileops_readbyte ops offset 0 :: fileops_readbytes ops len' (S offset)
   end.

Function fileops_read ops len offset :=
   let maxoffset := fileops_currentlength ops 0 in
   if maxoffset <=? offset then []
   else let maxlen := maxoffset - offset in
      fileops_readbytes ops (min len maxlen) offset
.

Function filetrace_read t len offset :=
   match t with
   | FileTrace j ops p => fileops_read ops len offset
   end.

Definition filetrace_append (t : file_trace) (op : fileop): file_trace.
Proof.
   destruct t.
   refine (FileTrace j (ops ++ [op]) _).
   rewrite app_length.
   simpl.
   omega.
Defined.

Definition filetrace_sync (t : file_trace): file_trace.
Proof.
   destruct t.
   refine (FileTrace (length ops) ops _).
   omega.
Defined.

End filetraces.

Section dirtraces.

Inductive dirop: Set :=
| DirCreate: string -> nat -> dirop
| DirUnlink: string -> dirop
.

Inductive dir_trace: Set :=
| DirTrace: forall j (ops : list dirop), j <= length ops -> dir_trace
.

Function dirops_get ops name :=
   match ops with
   | nil => None
   | op :: more => match (dirops_get more name) with
        | Some (Some result) => Some (Some result) (* found *)
        | Some None => Some None (* removed *)
        | None => match op with (* not seen downstream *)
             | DirCreate tname ino => if string_eq tname name then Some (Some ino) else None
             | DirUnlink tname => if string_eq tname name then Some None else None
             end
        end
    end.

Function dirtrace_get (t : dir_trace) name :=
   match t with
   | DirTrace j ops p => match dirops_get ops name with
        | Some (Some result) => Some result
        | Some None => None
        | None => None
        end
   end.

Definition dirtrace_append (t : dir_trace) (op : dirop): dir_trace.
Proof.
   destruct t.
   refine (DirTrace j (ops ++ [op]) _).
   rewrite app_length.
   simpl.
   omega.
Defined.

End dirtraces.

(*
 * vfs objects
 *)

Section vfsobjects.

Class vnodeclass (vnode : Type) := {
  inum_of_vnode: vnode -> nat;
  dirtrace_of_vnode: vnode -> dir_trace;
  filetrace_of_vnode: vnode -> file_trace;

(*
  foo: Proc unit unit;
  foo_spec: ProcHoare unit unit (fun _ => True) foo (fun _ _ => True);
*)

  VOP_LOOKUP: Proc (vnode * string) (option vnode);
  lookup_spec: forall t,
     ProcHoare
        (vnode * string) (option vnode)
        (fun arg => let (dir, name) := arg in
            dirtrace_of_vnode dir = t)
        (VOP_LOOKUP)
        (fun arg retvn => let (dir, name) := arg in
            dirtrace_of_vnode dir = t /\ (
               match retvn with
               | Some rvn => dirtrace_get t name = Some (inum_of_vnode rvn)
               | None => dirtrace_get t name = None
               end
            ));


  VOP_CREATE: Proc (vnode * string) (option vnode);
  create_spec: forall t ino,
     ProcHoare
        (vnode * string) (option vnode)
        (fun arg => let (dir, name) := arg in
            dirtrace_of_vnode dir = t)
        (VOP_CREATE)
        (fun arg retvn => let (dir, name) := arg in
            match retvn with
               | Some rvn => (
                    dirtrace_of_vnode dir = dirtrace_append t (DirCreate name ino) /\
                    inum_of_vnode rvn = ino
                 )
               | None =>
                    dirtrace_of_vnode dir = t
               end
         );

  VOP_UNLINK: Proc (vnode * string) (option unit);
  unlink_spec: forall t,
     ProcHoare
        (vnode * string) (option unit)
        (fun arg => let (dir, name) := arg in
            dirtrace_of_vnode dir = t)
        VOP_UNLINK
        (fun arg ret => let (dir, name) := arg in
           match ret with
           | Some _ => dirtrace_of_vnode dir = dirtrace_append t (DirUnlink name)
           | None => dirtrace_of_vnode dir = t
           end
        );

  VOP_READ: Proc (vnode * nat * nat) bytes;
  read_spec: forall t,
     ProcHoare
        (vnode * nat * nat) bytes
        (fun arg => let (arg', offset) := arg in let (file, len) := arg' in
           filetrace_of_vnode file = t)
        VOP_READ
        (fun arg ret => let (arg', offset) := arg in let (file, len) := arg' in
           filetrace_of_vnode file = t /\ ret = filetrace_read t len offset);

  VOP_WRITE: Proc (vnode * bytes * nat) unit;
  write_spec: forall t,
     ProcHoare
        (vnode * bytes * nat) unit
        (fun arg => let (arg', offset) := arg in let (file, data) := arg' in
           filetrace_of_vnode file = t)
        VOP_WRITE
        (fun arg ret => let (arg', offset) := arg in let (file, data) := arg' in
           filetrace_of_vnode file = filetrace_append t (FileWrite data offset));

  VOP_TRUNCATE: Proc (vnode * nat) unit;
  truncate_spec: forall t,
     ProcHoare
        (vnode * nat) unit
        (fun arg => let (file, size) := arg in
           filetrace_of_vnode file = t)
        VOP_TRUNCATE
        (fun arg ret => let (file, size) := arg in
           filetrace_of_vnode file = filetrace_append t (FileTruncate size));

  VOP_FSYNC: Proc vnode unit;
  fsync_spec: forall t,
     ProcHoare
        vnode unit
        (fun file =>
           filetrace_of_vnode file = t)
        VOP_FSYNC
        (fun file ret =>
           filetrace_of_vnode file = filetrace_sync t);
}.

Class fsclass (vfs : Type) := {
  vnode: Type;
  vnode_is_vnodeclass: vnodeclass vnode;

  VFS_GETROOT: Proc vfs vnode;
  VFS_SYNC: Proc vfs unit;
  newfs: Proc unit unit;
}.

End vfsobjects.
