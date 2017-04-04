Require Import Bool Arith List Omega.
Require Import OrderedType OrderedTypeEx.
Require FMapList.
Require FMapFacts.
Import ListNotations.

(*************************************************************)
(* get us some maps *)

Module NatMap := FMapList.Make Nat_as_OT.
Module NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.

(*************************************************************)
(* Data block model *)

(*
 * A data block is either a user block (which we identify
 * by a file number, file block number, and generation number) or
 * a FS metadata block, which is a value of some type T
 * defined by the FS.
 *
 * XXX: how do we want to do this parameterization? I suspect what
 * I've put here for the moment is going to suck.
 *)

Section DataBlocks.

Inductive DataBlock : Type :=
| UserData: forall (userfilenum fileblocknum generation : nat), DataBlock
| FSData: forall T : Type, forall metadata : T, DataBlock
.

(*
 * A block table is a map from block addresses (nats) to data.
 *)
Definition BlockTable : Type := NatMap.t DataBlock.

End DataBlocks.

(*************************************************************)
(* Cache model *)

Section Cache.

(*
 * We have two caches: a disk cache (on the disk) and an OS-level
 * buffer cache. These are both write-back but have different
 * behavior, reflecting the real-world behavior of these abstractions.
 *
 * Both caches are modeled using maps containing pending writes. (We
 * don't bother to model the read behavior of caches as we aren't
 * interested in trying to model performance.)
 *
 * The disk cache is a list of maps; a new entry is pushed on the list
 * when a write ordering barrier is issued. Therefore, more than one
 * value for any given block may be kept on file, but only with a
 * write barrier in between. I'm assuming that sending a disk new data
 * for a block still pending will overwrite the old version in the cache
 * if there's no write barrier prohibiting such combining.
 *
 * (XXX: do we need to make sure not to write the same block on both
 * sides of a write barrier to keep the disk from screwing up?)
 *
 * The OS cache is one map, but there's a lot more machinery to access
 * it.
 *
 * The complete cache has both cache layers and a platter, which
 * represents what's actually on the physical media.
 *)

Definition RawCache : Type := BlockTable.

Definition DiskPlatter : Type := BlockTable.
Definition DiskCache : Type := list RawCache.
Definition OSCache : Type := RawCache.

Inductive Cache : Type :=
| cache : forall (oc : OSCache) (dc : DiskCache) (dp : DiskPlatter), Cache
.



(*
 * Operations on DiskPlatter.
 *
 * DiskPlatter_empty is a totally empty platter.
 *)

Definition DiskPlatter_empty := NatMap.empty DataBlock.

Function DiskPlatter_read (plat : DiskPlatter) (bn : nat) :=
   NatMap.find bn plat.

Function DiskPlatter_write (plat : DiskPlatter) (bn : nat) (data : DataBlock):=
   NatMap.add bn data plat.

(*
 * Operations on RawCache.
 *
 * RawCache_empty is the empty cache.
 *
 * RawCache_read reads the value for the indicated block, if any.
 *
 * RawCache_write inserts a new block value into the cache,
 * overwriting any value that already exists.
 *
 * RawCache_sync transfers all the blocks to the platter (passed in)
 * and returns a new platter. It does not return a new RawCache; use
 * RawCache_empty.
 *)
Print NatMap.fold.

Definition RawCache_empty := NatMap.empty DataBlock.

Function RawCache_read (rc : RawCache) (bn : nat) :=
   NatMap.find bn rc.

Function RawCache_write (rc : RawCache) (bn : nat) (data : DataBlock) :=
   NatMap.add bn data rc.

Function RawCache_sync (rc : RawCache) (plat : DiskPlatter) :=
    NatMap.fold (fun bn data plat =>
                   DiskPlatter_write plat bn data) rc plat
.


(*
 * Operations on DiskCache.
 *
 * DiskCache_empty is the empty cache.
 *
 * DiskCache_read reads the latest value for the indicated block.
 *
 * DiskCache_write inserts a new block value into the cache.
 *
 * DiskCache_writebarrier issues a write barrier.
 *
 * DiskCache_sync transfers all blocks to the platter, obeying the
 * write barriers. It returns a new DiskPlatter. It does not return
 * a new DiskCache; use DiskCache_empty.
 *)

Definition DiskCache_empty := [] : list RawCache.

Function DiskCache_read (dc : DiskCache) (bn : nat) :=
   match dc with
   | [] => None
   | rc :: more =>
        match RawCache_read rc bn with
        | None => DiskCache_read more bn
        | Some data => Some data
        end
   end.

Function DiskCache_write (dc : DiskCache) (bn : nat) (data : DataBlock) :=
   match dc with
   | [] => [RawCache_write RawCache_empty bn data]
   | rc :: more => (RawCache_write rc bn data) :: more
   end.

Function DiskCache_writebarrier (dc : DiskCache) :=
   RawCache_empty :: dc.

Function DiskCache_sync (dc : DiskCache) (plat : DiskPlatter) :=
   match dc with
   | [] => plat
   | rc :: more =>
        RawCache_sync rc (DiskCache_sync more plat)
   end.

(*
 * Operations on OSCache.
 *
 * OSCache_empty is the empty cache.
 * OSCache_read reads the value for the indicated block, if any.
 * OSCache_write inserts a new block value into the cache.
 *
 * (more TBD)
 *)

Definition OSCache_empty := RawCache_empty.
Definition OSCache_read := RawCache_read.
Definition OSCache_write := RawCache_write.

(*
 * Operations on the whole cache.
 *
 * Cache_boot generates an empty cache attached to the given platter.
 * Cache_read reads the value for the indicated block.
 * Cache_write inserts a new block value and does not flush it.
 *
 * (more tbd)
 *)

Function Cache_boot (plat : DiskPlatter) :=
   cache OSCache_empty DiskCache_empty plat.

Function Cache_read (c : Cache) (bn : nat) :=
   match c with
   | cache oc dc plat => 
        match OSCache_read oc bn with
        | Some data => Some data
        | None =>
             match DiskCache_read dc bn with
             | Some data => Some data
             | None =>
                  DiskPlatter_read plat bn
             end
        end
   end.

Function Cache_write (c : Cache) (bn : nat) (data : DataBlock) :=
   match c with
   | cache oc dc plat =>
        let oc' := OSCache_write oc bn data in
        cache oc' dc plat
   end.

End Cache.

Section CacheFacts.

(*
 * Lemmas about caches.
 *)

(*
 * Reading returns the latest write.
 *)

Lemma RawCache_read_nonstale:
   forall rc bn data,
      RawCache_read (RawCache_write rc bn data) bn = Some data.
Proof.
   intros.
   unfold RawCache_write.
   unfold RawCache_read.
   rewrite NatMapFacts.add_eq_o; auto.
Qed.

Lemma DiskPlatter_read_nonstale:
   forall plat bn data,
      DiskPlatter_read (DiskPlatter_write plat bn data) bn = Some data.
Proof.
   intros.
   unfold DiskPlatter_write.
   unfold DiskPlatter_read.
   rewrite NatMapFacts.add_eq_o; auto.
Qed.

Lemma DiskCache_read_nonstale:
   forall dc bn data,
      DiskCache_read (DiskCache_write dc bn data) bn = Some data.
Proof.
   intros.
   destruct dc; simpl;
     rewrite RawCache_read_nonstale;
     auto.
Qed.

Lemma OSCache_read_nonstale:
   forall oc bn data,
      OSCache_read (OSCache_write oc bn data) bn = Some data.
Proof.
   intros.
   unfold OSCache_write.
   unfold OSCache_read.
   apply RawCache_read_nonstale.
Qed.

Lemma Cache_read_nonstale:
   forall c bn data,
      Cache_read (Cache_write c bn data) bn = Some data.
Proof.
   intros.
   destruct c.
   simpl.
   rewrite OSCache_read_nonstale.
   auto.
Qed.

(*
 * Writing something else doesn't affect reads.
 *)

Lemma RawCache_read_noninterfere:
   forall rc bn1 bn2 data,
      bn1 <> bn2 ->
      RawCache_read (RawCache_write rc bn1 data) bn2 = RawCache_read rc bn2.
Proof.
   intros.
   unfold RawCache_write.
   unfold RawCache_read.
   rewrite NatMapFacts.add_neq_o; auto.
Qed.

Lemma DiskPlatter_read_noninterfere:
   forall plat bn1 bn2 data,
      bn1 <> bn2 ->
      DiskPlatter_read (DiskPlatter_write plat bn1 data) bn2 = DiskPlatter_read plat bn2.
Proof.
   intros.
   unfold DiskPlatter_write.
   unfold DiskPlatter_read.
   rewrite NatMapFacts.add_neq_o; auto.
Qed.

Lemma DiskCache_read_noninterfere:
   forall dc bn1 bn2 data,
      bn1 <> bn2 ->
      DiskCache_read (DiskCache_write dc bn1 data) bn2 = DiskCache_read dc bn2.
Proof.
   intros.
   destruct dc; simpl;
      rewrite RawCache_read_noninterfere;
      auto.
Qed.

Lemma OSCache_read_noninterfere:
   forall oc bn1 bn2 data,
      bn1 <> bn2 ->
      OSCache_read (OSCache_write oc bn1 data) bn2 = OSCache_read oc bn2.
Proof.
   intros.
   unfold OSCache_write.
   unfold OSCache_read.
   apply RawCache_read_noninterfere.
   auto.
Qed.

Lemma Cache_read_noninterfere:
   forall c bn1 bn2 data,
      bn1 <> bn2 ->
      Cache_read (Cache_write c bn1 data) bn2 = Cache_read c bn2.
Proof.
   intros.
   destruct c.
   simpl.
   rewrite OSCache_read_noninterfere; auto.
Qed.

(*
 * A write barrier doesn't affect what you read.
 *)
Lemma DiskCache_read_writebarrier:
   forall dc bn,
      DiskCache_read (DiskCache_writebarrier dc) bn = DiskCache_read dc bn.
Proof.
   intros.
   simpl.
   auto.
Qed.

End CacheFacts.
