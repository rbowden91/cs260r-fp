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
Require Import vfs.

(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                           caponfs                            *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

Hypothesis undefined: forall T, T.

(*
 * the most ... bastardized fs model
 *)

Inductive caponvnode: Set :=
| capondir: nat -> dir_trace -> caponvnode
| caponfile: nat -> file_trace -> caponvnode
.

Inductive caponfs :=
| capon: NatMap.t caponvnode -> caponfs
.

Function caponfs_inum vn :=
   match vn with
   | capondir inum _ => inum
   | caponfile inum _ => inum
   end.

Function caponfs_isdir vn :=
   match vn with
   | capondir _ _ => true
   | caponfile _ _ => false
   end.

Function caponfs_isfile vn :=
   match vn with
   | capondir _ _ => false
   | caponfile _ _ => true
   end.

Function caponfs_dirtrace vn :=
   match vn with
   | capondir _ dt => dt
   | caponfile _ _ => dirtrace_empty (* ugh *)
   end.

Function caponfs_filetrace vn :=
   match vn with
   | capondir _ _ => filetrace_empty (* ugh *)
   | caponfile _ ft => ft
   end.

Function caponfs_getvnode fs inum: caponvnode :=
   match fs with
   | capon itbl => match NatMap.find inum itbl with
        | Some vn => vn
        | None => undefined caponvnode (* XXX *)
        end
   end.

Hypothesis caponfs_lookup: Proc (caponvnode * string) (option caponvnode).
Hypothesis caponfs_create: Proc (caponvnode * string) (option caponvnode).
Hypothesis caponfs_unlink: Proc (caponvnode * string) (option unit).
Hypothesis caponfs_read: Proc (caponvnode * nat * nat) bytes.
Hypothesis caponfs_write: Proc (caponvnode * bytes * nat) unit.
Hypothesis caponfs_truncate: Proc (caponvnode * nat) unit.
Hypothesis caponfs_fsync: Proc caponvnode unit.
Hypothesis caponfs_getroot: Proc caponfs caponvnode.
Hypothesis caponfs_sync: Proc caponfs unit.
Hypothesis caponfs_newfs: Proc unit caponfs.

Instance caponvnode_is_vnode: vnodeclass caponvnode := {
   inum_of_vnode := caponfs_inum;
   isdir := caponfs_isdir;
   isfile := caponfs_isfile;
   dirtrace_of_vnode := caponfs_dirtrace;
   filetrace_of_vnode := caponfs_filetrace;

   VOP_LOOKUP := caponfs_lookup;
   VOP_CREATE := caponfs_create;
   VOP_UNLINK := caponfs_unlink;
   VOP_READ := caponfs_read;
   VOP_WRITE := caponfs_write;
   VOP_TRUNCATE := caponfs_truncate;
   VOP_FSYNC := caponfs_fsync;
}.
Proof.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Instance caponfs_is_fs: fsclass caponfs := {
   vnode := caponvnode;
   vnode_is_vnodeclass := caponvnode_is_vnode;

   root_inum := 1;
   getvnode := caponfs_getvnode;

   VFS_GETROOT := caponfs_getroot;
   VFS_SYNC := caponfs_sync;

   newfs := caponfs_newfs;
}.
Proof.
  - admit.
  - admit.
  - admit.
Admitted.
