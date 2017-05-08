Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.

(*
 * Simple filesystem model for 260 project.
 *
 * This has:
 *    lookup
 *    create
 *    unlink
 *    read
 *    write
 *    truncate
 *    fsync
 *    getroot
 *    sync
 *
 * It is (for now) written using its own abstract syntax on the
 * grounds that (a) this lets me get started writing it, (b) changing
 * that around later is relatively straightforward, and (c) injecting
 * AST into a monad is a lot easier than the other way around.
 *)

(*************************************************************)
(* AST *)

Inductive Expr: Type -> Type :=
| value: forall t, t -> Expr t
| cond: forall t, Expr bool -> Expr t -> Expr t -> Expr t
.

Inductive Stmt: Type :=
| block: list Stmt -> Stmt
| assign: forall t, Var t -> Expr t -> Stmt
| if: Expr bool -> Stmt -> Stmt -> Stmt
| while: Expr bool -> Stmt -> Stmt
| call: forall t, Var t -> Proc t -> Stmt
.

(*
 * Extended/sugary AST forms
 *)

Definition coqcall (f : ta -> tr) (x : ta): Expr tr :=
   value (f x)
.

Definition skip: Stmt := block [].

(*************************************************************)
(* directory support *)

Definition roosterfs_searchdir dir name fs: option buffer :=
   {{ vnode_is_locked dir }}
   block [
	local slot;
	local lastslot;
	local ret;
	local lbn;
	local buf;
	local sm;
	local found;

	slot ::== value 0;
	lastslot ::== fieldof dir size;
	ret ::== value None;
	while (slot < lastslot) (block [
		lbn ::== slot / dirslots_per_block;
		buf ::== roosterfs_metaread dir lbn fs;
		sm ::== buf.metadata;
		found := value (
			match StringMap.find name sm with
			| Some _ => true
			| None => false
			end);
		if found (block [
			ret := Some buf;
			break;
		]) (*else*) skip;
		buf_release buf;
	]);
	return ret;
   ]
   {{ ret = None \/ (exists vn, ret = Some vn /\ hasreference vn) }}
   {{ True }} (* crash condition *)
.

(*************************************************************)
(* vnops *)

Definition roosterfs_lookup dir name fs: option roosterfs_vnode :=
   block [
	vnode_lock dir fs;
	optdirbuf := roosterfs_searchdir dir name fs;
	found := coqcall issome optdirbuf;
	if found (block [
		dirbuf := coqcall wassome optdirbuf;
		sm := dirbuf.metadata;
		ino := value (match StringMap.find name sm with
			| Some ino -> ino
			| None -> 0 (* impossible *)
			end);
		ret := roosterfs_loadvnode ino fs;
		buf_release buf;
	]) (*else*) (block [
		ret := None;
	]);
	vnode_unlock dir fs;
	return ret;
   ]
.

Definition roosterfs_create dir name fs: option roosterfs_vnode :=
   block [
	vnode_lock dir fs;
	optdirbuf := roosterfs_searchdir dir name fs;
	found := coqcall issome optbuf;
	if found (block [
		ret := None;
	]) (*else*) (block [
		dirbuf := coqcall wassome optdirbuf;
		sm := dirbuf.metadata;
		optinobuf := roosterfs_ialloc fs;
		worked := coqcall issome optinobuf;
		if worked (block [
			(inobuf, ino) := wassome optinobuf;
			dino := inobuf.metadata;
			dino.type = ROOSTERFS_FILE;
			dino.size = 0;
			dino.linkcount = 1;
			dino.blockmap = IntMap.empty;
			dino.corrupt = false;
			inobuf.metadata := dino;
			roosterfs_journal_zerodino ino;
			roosterfs_journal_type ino ROOSTERFS_INVALID
							ROOSTERFS_FILE;
			roosterfs_journal_linkcount ino 0 1;
			buffer_mark_dirty inobuf;

			ret := roosterfs_loadvnode_frombuf ino inobuf fs;
			worked := coqcall issome ret;
			if worked (block [
				sm := StringMap.add name ino sm;
				dirbuf.metadata := sm;
				roosterfs_journal_diradd dirino name ino;
				buffer_mark_dirty dirbuf;
			]) (*else*) (block [
				roosterfs_ifree ino fs;
			]);
			buffer_release buf;
			buffer_release inobuf;
		]) (*else*) (block [
			buf_release optbuf;
			ret := None;
		])
	]);
	vnode_unlock dir fs;
	return ret;
   ]
.

(* XXX; but let's make the above compile first
Definition roosterfs_unlink dir name fs: option roosterfs :=
   block [
	vnode_lock dir fs;
	vnode_unlock dir fs;
	return ret;
   ]
.

Definition roosterfs_read vn len offset fs: option bytes :=
   block [
	vnode_lock vn fs;
	vnode_unlock vn fs;
	return ret;
   ]
.

Definition roosterfs_write vn bytes offset fs: option roosterfs :=
   block [
	vnode_lock vn fs;
	vnode_unlock vn fs;
	return ret;
   ]
.

Definition roosterfs_truncate vn len fs: option roosterfs :=
   block [
	vnode_lock vn fs;
	vnode_unlock vn fs;
	return ret;
   ]
.

Definition roosterfs_fsync vn fs: option roosterfs :=
   block [
	vnode_lock dir fs;
	vnode_unlock dir fs;
	return ret;
   ]
.

Definition roosterfs_getroot fs: roosterfs_vnode :=
   block [
	vnode_lock dir fs;
	vnode_unlock dir fs;
	return ret;
   ]
.

Definition roosterfs_sync fs: roosterfs :=
   block [
	vnode_lock dir fs;
	vnode_unlock dir fs;
	return ret;
   ]
.
*)
