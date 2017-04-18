Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.

(* bytes *)

(* Use nat as a standin for the data *)
Definition bytes : Type := (nat * nat).


(*************************************************************)
(* file traces *)

Section filetraces.

Inductive fileop: Type :=
| FileWrite: bytes -> nat -> fileop
| FileTruncate: nat -> fileop
.

Inductive file_trace: nat -> list fileop -> Type :=
| FileTrace: forall j ops, j <= length ops -> file_trace j ops
.

End filetraces.

(*************************************************************)
(* dir traces *)

Section dirtraces.

Inductive dirop: Set :=
| DirCreate: string -> dirop
| DirUnlink: string -> dirop
.

Inductive dir_trace: nat -> list dirop -> Type :=
| DirTrace: forall j ops, j <= length ops -> dir_trace j ops
.

End dirtraces.

(*************************************************************)
(* vnodes/fses *)

Section vnodes.

(* monad M... XXX *)
Class vnodeclass (M : Type -> Type) (vnode : Type) := {
  VOP_LOOKUP: vnode -> string -> M vnode;
  VOP_CREATE: vnode -> string -> M vnode;
  VOP_UNLINK: vnode -> string -> M unit;
  VOP_READ: vnode -> nat -> nat -> M (bytes * nat)%type;
  VOP_WRITE: vnode -> bytes -> nat -> M unit;
  VOP_TRUNCATE: vnode -> nat -> M unit;
  VOP_FSYNC: vnode -> M unit;
}.

(* monad M... XXX *)
Class fsclass (M : Type -> Type) (fs : Type) := {
  vnode: Type;
  VFS_GETROOT: fs -> M vnode;
  VFS_SYNC: fs -> M unit;
}.

End vnodes.

(*************************************************************)
(* ops *)

Section ops.

Inductive op: Type :=
| lookup: string -> op
| create: string -> op
| unlink: string -> op
| read: nat -> nat -> op
| write: bytes -> nat -> op
| truncate: nat -> op
| fsync: op
| getroot: op
| sync: op
.

Lemma string_eq_dec:
   forall s1 s2 : string,
   {s1 = s2} + {s1 <> s2}.
Proof.
Admitted.

Lemma op_eq_dec:
   forall op1 op2 : op,
   {op1 = op2} + {op1 <> op2}.
Proof.
   intros.
   destruct op1; destruct op2; auto; try (right; discriminate).
   1-3: destruct (string_eq_dec s s0);
        subst; auto;
        right;
        congruence.
   - destruct (Nat.eq_dec n n1); destruct (Nat.eq_dec n0 n2); subst.
     1: left; auto.
     1-3: right; congruence.
   - destruct b. destruct b0.
     destruct (Nat.eq_dec n1 n3);
     destruct (Nat.eq_dec n2 n4);
     destruct (Nat.eq_dec n n0); subst.
     1: left; auto.
     1-7: right; congruence.
   - destruct (Nat.eq_dec n n0); subst.
     1: left; auto.
     1: right; congruence.
Qed.

Inductive execution: Type :=
| exec_op: op -> execution
| exec_seq: execution -> execution -> execution
| exec_par: execution -> execution -> execution
.

Inductive serial: execution -> Prop :=
| serial_op: forall op, serial (exec_op op)
| serial_seq: forall x1 x2, serial (exec_seq x1 x2)
.

Inductive op_in: op -> execution -> Prop :=
| op_in_op: forall op, op_in op (exec_op op)
| op_in_seqa: forall op x1 x2, op_in op x1 -> op_in op (exec_seq x1 x2)
| op_in_seqb: forall op x1 x2, op_in op x2 -> op_in op (exec_seq x1 x2)
| op_in_para: forall op x1 x2, op_in op x1 -> op_in op (exec_par x1 x2)
| op_in_parb: forall op x1 x2, op_in op x2 -> op_in op (exec_par x1 x2)
.

Lemma OpInOp:
   forall op1 op2,
   op_in op1 (exec_op op2) -> op1 = op2.
Proof.
   intros.
   inversion H; auto.
Qed.

Lemma NotOpInOp:
   forall op1 op2,
   ~(op_in op1 (exec_op op2)) -> op1 <> op2.
Proof.
   intros.
   contradict H.
   subst.
   apply op_in_op.
Qed.

Lemma OpInSeq:
   forall op x1 x2,
   op_in op (exec_seq x1 x2) -> op_in op x1 \/ op_in op x2.
Proof.
   intros.
   inversion H; subst.
   - left; auto.
   - right; auto.
Qed.

Lemma OpInPar:
   forall op x1 x2,
   op_in op (exec_par x1 x2) -> op_in op x1 \/ op_in op x2.
Proof.
   intros.
   inversion H; subst.
   - left; auto.
   - right; auto.
Qed.

Lemma NotOpInSeq:
   forall op x1 x2,
   ~(op_in op (exec_seq x1 x2)) -> ~(op_in op x1) /\ ~(op_in op x2).
Proof.
   intros.
   split; contradict H.
   - apply op_in_seqa; auto.
   - apply op_in_seqb; auto.
Qed.

Lemma NotOpInPar:
   forall op x1 x2,
   ~(op_in op (exec_par x1 x2)) -> ~(op_in op x1) /\ ~(op_in op x2).
Proof.
   intros.
   split; contradict H.
   - apply op_in_para; auto.
   - apply op_in_parb; auto.
Qed.

Lemma not_op_in_op:
   forall op1 op2,
   op1 <> op2 -> ~(op_in op1 (exec_op op2)).
Proof.
   intros.
   contradict H.
   apply OpInOp in H.
   auto.
Qed.

Lemma not_op_in_seq:
   forall op x1 x2,
   ~(op_in op x1) -> ~(op_in op x2) -> ~(op_in op (exec_seq x1 x2)).
Proof.
   intros.
   contradict H.
   apply OpInSeq in H.
   destruct H.
   - auto.
   - contradiction. 
Qed.

Lemma not_op_in_par:
   forall op x1 x2,
   ~(op_in op x1) -> ~(op_in op x2) -> ~(op_in op (exec_par x1 x2)).
Proof.
   intros.
   contradict H.
   apply OpInPar in H.
   destruct H.
   - auto.
   - contradiction.
Qed.

Lemma in_dec:
   forall op x,
   {op_in op x} + {~(op_in op x)}.
Proof.
   intros.
   induction x.
   - destruct (op_eq_dec op0 o); subst.
     * left. apply op_in_op.
     * right. apply not_op_in_op. auto.
   - destruct IHx1; destruct IHx2.
     * left. apply op_in_seqa. auto.
     * left. apply op_in_seqa. auto.
     * left. apply op_in_seqb. auto.
     * right. apply not_op_in_seq; auto.
   - destruct IHx1; destruct IHx2.
     * left. apply op_in_para. auto.
     * left. apply op_in_para. auto.
     * left. apply op_in_parb. auto.
     * right. apply not_op_in_par; auto.
Qed.

Inductive op_occurs: op -> execution -> nat -> Prop :=
| op_occurs_self: forall op,
     op_occurs op (exec_op op) 1
| op_occurs_other: forall op1 op2, op1 <> op2 ->
     op_occurs op1 (exec_op op2) 0
| op_occurs_seq: forall op x1 x2 n1 n2,
       op_occurs op x1 n1 -> op_occurs op x2 n2 ->
     op_occurs op (exec_seq x1 x2) (n1 + n2)
| op_occurs_par: forall op x1 x2 n1 n2,
       op_occurs op x1 n1 -> op_occurs op x2 n2 ->
     op_occurs op (exec_par x1 x2) (n1 + n2)
.

Lemma op_occurs_det:
   forall op x n1 n2,
      op_occurs op x n1 -> op_occurs op x n2 ->
      n1 = n2.
Proof.
   intros.
   revert H0. revert n2.
   induction H; intros.
   - destruct (Nat.eq_dec n2 1); subst; auto.
     inversion H0; [ omega | contradiction ].
   - destruct (Nat.eq_dec n2 0); subst; auto.
     inversion H0; subst; contradiction; auto.
   - inversion H1; subst.
     apply IHop_occurs1 in H5.
     apply IHop_occurs2 in H7.
     subst; auto.
   - inversion H1; subst.
     apply IHop_occurs1 in H5.
     apply IHop_occurs2 in H7.
     subst; auto.
Qed.

Lemma op_occurs_seq_nosum_existential:
   forall op x1 x2 n1 n2,
   op_occurs op x1 n1 -> op_occurs op x2 n2 ->
   exists n,
   n = n1 + n2 /\ op_occurs op (exec_seq x1 x2) n.
Proof.
   intros.
   exists (n1 + n2).
   split; auto.
   apply op_occurs_seq; auto.
Qed.

Lemma op_occurs_seq_nosum:
   forall op x1 x2 n1 n2 n,
   op_occurs op x1 n1 -> op_occurs op x2 n2 -> n = n1 + n2 ->
   op_occurs op (exec_seq x1 x2) n.
Proof.
   intros.
   rewrite H1.
   apply op_occurs_seq; auto.
Qed.

Lemma op_occurs_par_nosum:
   forall op x1 x2 n1 n2 n,
   op_occurs op x1 n1 -> op_occurs op x2 n2 -> n = n1 + n2 ->
   op_occurs op (exec_par x1 x2) n.
Proof.
   intros.
   rewrite H1.
   apply op_occurs_par; auto.
Qed.

Lemma OpOccursSeq:
   forall op x1 x2 n,
   op_occurs op (exec_seq x1 x2) n ->
   exists n1 n2,
   n = n1 + n2 /\
   op_occurs op x1 n1 /\
   op_occurs op x2 n2.
Proof.
   intros.
   inversion H; subst.
   exists n1. exists n2.
   split; auto.
Qed.

Lemma OpOccursPar:
   forall op x1 x2 n,
   op_occurs op (exec_par x1 x2) n ->
   exists n1 n2,
   n = n1 + n2 /\
   op_occurs op x1 n1 /\
   op_occurs op x2 n2.
Proof.
   intros.
   inversion H; subst.
   exists n1. exists n2.
   split; auto.
Qed.

Lemma op_occurs_in:
   forall op x n,
   op_occurs op x n -> n > 0 -> op_in op x.
Proof.
   intros.
   induction H.
   - apply op_in_op.
   - omega.
   - destruct (Nat.eq_dec n1 0); subst.
     * rewrite Nat.add_0_l in H0.
       apply IHop_occurs2 in H0.
       apply op_in_seqb.
       auto.
     * assert (n1 > 0) by omega.
       apply IHop_occurs1 in H2.
       apply op_in_seqa.
       auto.
   - destruct (Nat.eq_dec n1 0); subst.
     * rewrite Nat.add_0_l in H0.
       apply IHop_occurs2 in H0.
       apply op_in_parb.
       auto.
     * assert (n1 > 0) by omega.
       apply IHop_occurs1 in H2.
       apply op_in_para.
       auto.
Qed.

Lemma op_notin_occurs:
   forall op x,
      ~(op_in op x) -> op_occurs op x 0.
Proof.
   intros.
   induction x.
   - apply NotOpInOp in H. 
     apply op_occurs_other.
     auto.
   - apply NotOpInSeq in H.
     destruct H as [Ha Hb].
     apply op_occurs_seq_nosum with (n1 := 0) (n2 := 0); auto.
   - apply NotOpInPar in H.
     destruct H as [Ha Hb].
     apply op_occurs_par_nosum with (n1 := 0) (n2 := 0); auto.
Qed.

Lemma op_in_occurs:
   forall op x,
      op_in op x -> exists n, n > 0 /\ op_occurs op x n.
Proof.
   intros.
   revert H.
   induction x; intros.
   - apply OpInOp in H.
     rewrite H.
     exists 1.
     split; auto.
     apply op_occurs_self.
   - apply OpInSeq in H.
     destruct H.
     * apply IHx1 in H.
       destruct H as [n1 [H1a H1b]].
       destruct (in_dec op0 x2) as [Hx2 | Hx2].
       + apply IHx2 in Hx2.
         destruct Hx2 as [n2 [H2a H2b]].
         exists (n1 + n2).
         split; try omega.
         apply op_occurs_seq; auto.
       + apply op_notin_occurs in Hx2.
         exists (n1 + 0).
         split; try omega.
         apply op_occurs_seq; auto.
     * apply IHx2 in H.
       destruct H as [n2 [H2a H2b]].
       destruct (in_dec op0 x1) as [Hx1 | Hx1].
       + apply IHx1 in Hx1.
         destruct Hx1 as [n1 [H1a H1b]].
         exists (n1 + n2).
         split; try omega.
         apply op_occurs_seq; auto.
       + apply op_notin_occurs in Hx1.
         exists (0 + n2).
         split; try omega.
         apply op_occurs_seq; auto.
   - apply OpInPar in H.
     destruct H.
     * apply IHx1 in H.
       destruct H as [n1 [H1a H1b]].
       destruct (in_dec op0 x2) as [Hx2 | Hx2].
       + apply IHx2 in Hx2.
         destruct Hx2 as [n2 [H2a H2b]].
         exists (n1 + n2).
         split; try omega.
         apply op_occurs_par; auto.
       + apply op_notin_occurs in Hx2.
         exists (n1 + 0).
         split; try omega.
         apply op_occurs_par; auto.
     * apply IHx2 in H.
       destruct H as [n2 [H2a H2b]].
       destruct (in_dec op0 x1) as [Hx1 | Hx1].
       + apply IHx1 in Hx1.
         destruct Hx1 as [n1 [H1a H1b]].
         exists (n1 + n2).
         split; try omega.
         apply op_occurs_par; auto.
       + apply op_notin_occurs in Hx1.
         exists (0 + n2).
         split; try omega.
         apply op_occurs_par; auto.
Qed.

Definition sameops (x1 x2 : execution): Prop :=
   forall op n,
   op_occurs op x1 n <-> op_occurs op x2 n.

Lemma sameops_refl:
   forall x,
   sameops x x.
Proof.
   unfold sameops.
   intros.
   split; auto. (* auto can't handle x <-> x... sigh *)
Qed.

Lemma sameops_sym:
   forall x1 x2,
   sameops x1 x2 -> sameops x2 x1.
Proof.
   unfold sameops.
   intros.
   split; intro.
   - rewrite H. auto.
   - rewrite <- H. auto.
Qed.

Lemma sameops_in:
   forall x1 x2,
   sameops x1 x2 ->
   forall op, op_in op x1 -> op_in op x2.
Proof.
   intros.
   unfold sameops in H.
   apply op_in_occurs in H0.
   destruct H0 as [n [H0 H1]].
   rewrite H in H1.
   apply op_occurs_in with (n := n); auto.
Qed.

Lemma sameops_occurs:
   forall x1 x2,
   sameops x1 x2 ->
   forall op n, op_occurs op x1 n -> op_occurs op x2 n.
Proof.
   intros.
   unfold sameops in H.
   rewrite <- H.
   auto.
Qed.

Lemma sameops_seq:
   forall x1 x2 y1 y2,
   sameops x1 x2 -> sameops y1 y2 ->
   sameops (exec_seq x1 y1) (exec_seq x2 y2).
Proof.
   unfold sameops in *.
   intros.
   split; intro;
     apply OpOccursSeq in H1;
     destruct H1 as [n1 [n2 [H1 [H2 H3]]]];
     rewrite H1.
   - rewrite H in H2;
     rewrite H0 in H3;
     apply op_occurs_seq; auto.
   - rewrite <- H in H2.
     rewrite <- H0 in H3.
     apply op_occurs_seq; auto.
Qed.

(* this is actually "before or same as" as that's easier to use *)
(* XXX is this even remotely right? what if an op appears twice? *)
Inductive op_before: op -> op -> execution -> Prop :=
| op_before_self: forall op x,
     op_in op x ->
     op_before op op x
| op_before_seq: forall op1 op2 x1 x2,
     op_in op1 x1 -> op_in op2 x2 ->
     op_before op1 op2 (exec_seq x1 x2)
| op_before_seqappend: forall op1 op2 x1 x2,
     op_before op1 op2 x1 ->
     op_before op1 op2 (exec_seq x1 x2)
| op_before_seqprepend: forall op1 op2 x1 x2,
     op_before op1 op2 x2 ->
     op_before op1 op2 (exec_seq x1 x2)
| op_before_parappend: forall op1 op2 x1 x2,
     op_before op1 op2 x1 ->
     op_before op1 op2 (exec_par x1 x2)
| op_before_parprepend: forall op1 op2 x1 x2,
     op_before op1 op2 x2 ->
     op_before op1 op2 (exec_par x1 x2)
.

Definition sameorder (x1 x2 : execution): Prop :=
   forall op1 op2,
   op_before op1 op2 x1 -> op_before op1 op2 x2.

Lemma sameorder_refl:
   forall x, sameorder x x.
Proof.
   unfold sameorder.
   auto.
Qed.

(* XXX
Definition equivalent (x1 x2 : execution): Prop :=
   forall gt0 gt1 gt2,
   eval gt0 x1 = gt1 ->
   eval gt0 x2 = gt2 ->
   forall f, gt_select f gt1 = gt_select f gt2.
*)

(* x1 serializes x2, not x2 serializes x1 *)
Definition serializes (x1 x2 : execution): Prop :=
   sameops x1 x2 /\ sameorder x2 x1 /\ serial x1.
(* /\ equivalent x1 x2 *) (* XXX *)

Lemma serializes_refl:
   forall x, serial x -> serializes x x.
Proof.
   intros.
   unfold serializes.
   split. 2: split.
   - apply sameops_refl.
   - apply sameorder_refl.
   - auto.
Qed.


(*
 * This should be in the typeclass, but first I have to figure out
 * how to hook "execution" up to it.
 *)

Hypothesis ops_noninterference:
   forall op1 op2,
      serializes (exec_seq op1 op2) (exec_par op1 op2) \/
      serializes (exec_seq op2 op1) (exec_par op1 op2).

Theorem serializability:
   forall x2,
   exists x1,
   serializes x1 x2.
Proof.
   intros.
   induction x2.
   - exists (exec_op o). apply serializes_refl; apply serial_op.
   - destruct IHx2_1 as [x_1 IH1].
     destruct IHx2_2 as [x_2 IH2].
     exists (exec_seq x_1 x_2).
     unfold serializes in *.
     destruct IH1 as [IH1a [IH1b IH1c]].
     destruct IH2 as [IH2a [IH2b IH2c]].
     split. 2: split.
     * unfold sameops.
       split; intros.
       1,2: apply OpOccursSeq in H;
         destruct H as [n1 [n2 [Hn [H1 H2]]]];
         unfold sameops in IH1a;
         unfold sameops in IH2a;
         apply IH1a in H1;
         apply IH2a in H2;
         rewrite Hn;
         apply op_occurs_seq; auto.
     * unfold sameorder in *.
       intros.
       inversion H; subst; try discriminate.
       + apply op_before_self.
         assert (sameops (exec_seq x2_1 x2_2) (exec_seq x_1 x_2)) by
            (apply sameops_sym; apply sameops_seq; auto).
         apply sameops_in with (op := op2) in H1; auto.
       + apply sameops_sym in IH1a.
         apply sameops_sym in IH2a.
         apply op_before_seq.
         apply sameops_in with (op := op1) in IH1a; auto.
         apply sameops_in with (op := op2) in IH2a; auto.
       + apply op_before_seqappend.
         apply IH1b; auto.
       + apply op_before_seqprepend.
         apply IH2b; auto.
     * apply serial_seq.
   - destruct IHx2_1 as [sx1 Ser1].
     destruct IHx2_2 as [sx2 Ser2].
     exists (exec_seq sx1 sx2).
     unfold serializes in *.
     destruct Ser1 as [Ser1a [Ser1b Ser1c]].
     destruct Ser2 as [Ser2a [Ser2b Ser2c]].
     split; split.
     * intro.
       apply OpOccursSeq in H.
       destruct H as [n1 [n2 [H1 [H2 H3]]]].
       rewrite H1.
       apply op_occurs_par.
       + apply sameops_occurs with (x1 := sx1); auto.
       + apply sameops_occurs with (x1 := sx2); auto.
     * intro.
       apply OpOccursPar in H.
       destruct H as [n1 [n2 [H1 [H2 H3]]]].
       rewrite H1.
       apply op_occurs_seq.
       + apply sameops_occurs with (x1 := x2_1); apply sameops_sym in Ser1a; auto.
       + apply sameops_occurs with (x1 := x2_2); apply sameops_sym in Ser2a; auto.
     * unfold sameorder in *.
       intros.
       inversion H; subst; try discriminate.
       + apply op_before_self.
         apply OpInPar in H0.
         destruct H0.
         -- apply sameops_sym in Ser1a.
            apply sameops_in with (op := op2) in Ser1a; auto.
            apply op_in_seqa; auto.
         -- apply sameops_sym in Ser2a.
            apply sameops_in with (op := op2) in Ser2a; auto.
            apply op_in_seqb; auto.
       + apply op_before_seqappend.
         apply Ser1b; auto.
       + apply op_before_seqprepend.
         apply Ser2b; auto.
     * apply serial_seq.
Qed.

End ops.
