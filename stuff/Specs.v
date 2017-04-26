Require Import List.
Import ListNotations.
Require Import ConcurrentSeparationLogic.
Require Import SepCancel.

Definition vnode_lock := 0.
Definition vnode_invariant := (emp,
                               emp).

Definition log_lock := 1.
Definition log_invariant := (emp, emp).

Definition buffer_lock := 2.
Definition buffer_invariant := (emp, emp).

Definition invariants := [
  vnode_invariant;
  log_invariant;
  buffer_invariant
].




Definition write (heap_addr : nat) (block_num : nat) (v : diskval) : cmd nat :=
  _ <- Lock vnode_lock ;
  vnode <- Read heap_addr ;
  match vnode with 
  | HVnode (i,b,l) =>
      _ <- Write heap_addr (HVnode (i,b,true)) ;
      _ <- Unlock vnode_lock ;
      (* XXX Do stuff with vnode *)
      _ <- Lock vnode_lock ;
      _ <- Write heap_addr (HVnode (i,b,false)) ;
      _ <- Unlock vnode_lock ;
      Return 0
  | HNat _ => 
      _ <- Unlock vnode_lock ;
      Fail
  end.

Definition write_spec :=
  forall addr bnum v, invariants ||- {{emp}} {{exists v, addr |-> HVnode v}} 
                                        write addr bnum v
                                     {{emp}} {{_ ~> emp}}.

Lemma write_ok : write_spec.
Proof.
  unfold write_spec; intros; unfold write.
  step.
  instantiate (2:=fst vnode_invariant).
  instantiate (1:=(fun _ => (snd vnode_invariant * (exists v0 : vnode, addr |-> HVnode v0)))%sep).
  apply HtWeaken with (P:=(emp * exists v0 : vnode, addr |-> HVnode v0)%sep).
  apply HtFrame with (R:=(exists v0 : vnode, addr |-> HVnode v0)%sep).
  step.
  cancel.
