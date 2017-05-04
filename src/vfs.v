Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

Require Import OrderedType OrderedTypeEx.
Require FMapList.
Require FMapFacts.
Module NatMap := FMapList.Make Nat_as_OT.
Module NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.

Require Import stringfacts.
Require Import base.
Require Import ast.
Require Import logic.

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

Definition filetrace_empty: file_trace.
Proof.
   refine (FileTrace 0 [] _).
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

Definition dirtrace_sync (t : dir_trace): dir_trace.
Proof.
   destruct t.
   refine (DirTrace (length ops) ops _).
   omega.
Defined.

Definition dirtrace_empty: dir_trace.
Proof.
   refine (DirTrace 0 [] _).
   omega.
Defined.

End dirtraces.


(*
 * vfs objects
 *)

Section vfsobjects.

Definition Pair (t1 t2: Set): Set := (t1 * t2)%type.

Class vnodeclass (vnode : Set) := {
  inum_of_vnode: vnode -> nat;
  isdir: vnode -> bool;
  isfile: vnode -> bool;
  dirtrace_of_vnode: vnode -> dir_trace;
  filetrace_of_vnode: vnode -> file_trace;

(*
  foo: Proc unit unit;
  foo_spec: ProcHoare unit unit (fun _ => True) foo (fun _ _ => True);
*)

  VOP_LOOKUP: Proc (Pair vnode string) (option vnode);
  lookup_spec: forall t,
     ProcHoare
        (vnode * string) (option vnode)
        (fun arg => let (dir, name) := arg in
            isdir dir = true /\
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
            isdir dir = true /\
            dirtrace_of_vnode dir = t)
        (VOP_CREATE)
        (fun arg retvn => let (dir, name) := arg in
            match retvn with
               | Some rvn => (
                    dirtrace_of_vnode dir = dirtrace_append t (DirCreate name ino) /\
                    inum_of_vnode rvn = ino /\
                    filetrace_of_vnode rvn = filetrace_empty
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
            isdir dir = true /\
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
           isfile file = true /\
           filetrace_of_vnode file = t)
        VOP_READ
        (fun arg ret => let (arg', offset) := arg in let (file, len) := arg' in
           filetrace_of_vnode file = t /\ ret = filetrace_read t len offset);

  VOP_WRITE: Proc (vnode * bytes * nat) unit;
  write_spec: forall t,
     ProcHoare
        (vnode * bytes * nat) unit
        (fun arg => let (arg', offset) := arg in let (file, data) := arg' in
           isfile file = true /\
           filetrace_of_vnode file = t)
        VOP_WRITE
        (fun arg ret => let (arg', offset) := arg in let (file, data) := arg' in
           filetrace_of_vnode file = filetrace_append t (FileWrite data offset));

  VOP_TRUNCATE: Proc (vnode * nat) unit;
  truncate_spec: forall t,
     ProcHoare
        (vnode * nat) unit
        (fun arg => let (file, size) := arg in
           isfile file = true /\
           filetrace_of_vnode file = t)
        VOP_TRUNCATE
        (fun arg ret => let (file, size) := arg in
           filetrace_of_vnode file = filetrace_append t (FileTruncate size));

  VOP_FSYNC: Proc vnode unit;
  fsync_spec: forall t,
     ProcHoare
        vnode unit
        (fun file =>
           isfile file = true /\
           filetrace_of_vnode file = t)
        VOP_FSYNC
        (fun file ret =>
           filetrace_of_vnode file = filetrace_sync t);
}.

Section tracetable.

Inductive trace_table: Type :=
| TraceTable: NatMap.t dir_trace -> NatMap.t file_trace -> trace_table
.

Definition tracetable_dirprop {vnt : Set} {q: vnodeclass vnt}
                              (vn: vnt) (dtbl: NatMap.t dir_trace) (p : dir_trace -> Prop) :=
   forall t,
   isdir vn = true -> NatMap.find (inum_of_vnode vn) dtbl = Some t -> p t.

Definition tracetable_fileprop {vnt : Set} {q: vnodeclass vnt}
                               (vn : vnt) (ftbl: NatMap.t file_trace) (p: file_trace -> Prop) :=
   forall t,
   isfile vn = true -> NatMap.find (inum_of_vnode vn) ftbl = Some t -> p t.

Definition tracetable_has {vnt : Set} {q : vnodeclass vnt}
                          (vn: vnt) ttbl: Prop :=
   match ttbl with
   | TraceTable dtbl ftbl =>
        (tracetable_dirprop vn dtbl (fun t => dirtrace_of_vnode vn = t)) \/
        (tracetable_fileprop vn ftbl (fun t => filetrace_of_vnode vn = t))
   end.

Definition tracetable_apply {vnt: Set} {q: vnodeclass vnt}
                            (vn: vnt) df ff ttbl: Prop :=
   match ttbl with
   | TraceTable dtbl ftbl =>
        (tracetable_dirprop vn dtbl (fun t => dirtrace_of_vnode vn = df t)) \/
        (tracetable_fileprop vn ftbl (fun t => filetrace_of_vnode vn = ff t))
   end.

End tracetable.


Class fsclass (vfs : Set) := {
  vnode: Set;
  vnode_is_vnodeclass: vnodeclass vnode;

  root_inum: nat;
  getvnode: vfs -> nat -> vnode;

  VFS_GETROOT: Proc vfs vnode;
  getroot_spec:
     ProcHoare
        vfs vnode
        (fun fs => True)
        VFS_GETROOT
        (fun fs rootvn => inum_of_vnode rootvn = root_inum /\
           isdir rootvn = true);

  VFS_SYNC: Proc vfs unit;
  sync_spec: forall ttbl,
     ProcHoare
        vfs unit
        (fun fs => forall inum vn,
            getvnode fs inum = vn -> tracetable_has vn ttbl)
        VFS_SYNC
        (fun fs _ => forall inum vn,
           getvnode fs inum = vn ->
              tracetable_apply vn dirtrace_sync filetrace_sync ttbl);

  newfs: Proc unit vfs;
  newfs_spec:
     ProcHoare
        unit vfs
        (fun _ => True)
        newfs
        (fun _ fs => forall inum vn,
           getvnode fs inum = vn -> inum = root_inum /\
           dirtrace_of_vnode vn = dirtrace_empty);
}.

End vfsobjects.
