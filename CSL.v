Require Import compcert.backend.Cminor.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Values.

Require Coq.Structures.OrderedType.
Require FMapList.
Require FMapFacts.
Require XMapFacts.
Require Import Coq.PArith.BinPos.
Require Import Coq.Classes.RelationClasses.
Require Import OrderedType OrderedTypeEx DecidableType.

Require Import SepCancel.

Set Implicit Arguments.


Inductive ptr : Set :=
  | StackPtr : ptrofs -> ptr
  | HeapPtr : ptrofs -> ptr
  | LocalPtr : ident -> ptr
(*  | GlobalPtr : ident -> mem_type *)
.

(*
  Tried combining things into one big memory, but decided to
  just use three separate maps...

Module PtrMiniOrderedType <: OrderedType.MiniOrderedType.
  Definition t := ptr.

  Definition eq ptr1 ptr2:=
    match ptr1, ptr2 with
    | StackPtr off1, StackPtr off2 => off1 = off2
    | HeapPtr off1, HeapPtr off2 => off1 = off2
    | LocalPtr id1, LocalPtr id2 => id1 = id2
    | _, _ => False
    end.

  Definition lt ptr1 ptr2:=
    match ptr1, ptr2 with
    | StackPtr off1, StackPtr off2 => Ptrofs.lt off1 off2 = true
    | HeapPtr off1, HeapPtr off2 => Ptrofs.lt off1 off2 = true
    | LocalPtr id1, LocalPtr id2 => (id1 < id2)%positive
    | StackPtr _, HeapPtr _ => True
    | HeapPtr _, LocalPtr _ => True
    | StackPtr _, LocalPtr _ => True
    | _, _ => False
    end.
*)

Module MemorySegment.
  Module OT <: MiniOrderedType.
    Definition t := ptrofs.
    Definition eq (ptr1 ptr2 : ptrofs) := ptr1 = ptr2.
    Definition lt (ptr1 ptr2 : ptrofs) := Ptrofs.lt ptr1 ptr2 = true.

    Lemma eq_refl : forall x : t, eq x x.
      unfold eq; auto.
    Qed.

    Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      unfold eq; auto.
    Qed.

    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      unfold eq; intros; subst; auto.
    Qed.

    (* Almost definitely not how I should be doing these... *)
    Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      unfold lt.
      unfold Ptrofs.lt.
      intros.
      destruct (Coqlib.zlt (Ptrofs.signed x) (Ptrofs.signed y));
      destruct (Coqlib.zlt (Ptrofs.signed y) (Ptrofs.signed z));
      destruct (Coqlib.zlt (Ptrofs.signed x) (Ptrofs.signed z));
      simpl; auto.
      assert (BinInt.Z.lt (Ptrofs.signed x) (Ptrofs.signed z)); auto.
      pose (BinInt.Z.lt_trans (Ptrofs.signed x) (Ptrofs.signed y) (Ptrofs.signed z)).
      auto.
    Qed.

    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      unfold lt.
      unfold eq.
      unfold Ptrofs.lt.
      intros.
      destruct (Coqlib.zlt (Ptrofs.signed x) (Ptrofs.signed y)).
      assert (Ptrofs.signed x <> Ptrofs.signed y).
      pose (Z_as_OT.lt_not_eq (Ptrofs.signed x) (Ptrofs.signed y)); auto.
      intro; subst; auto.
      discriminate.
    Qed.

    Definition compare : forall x y : t, Compare lt eq x y.
      Admitted.

  End OT.

  Module MOT := MOT_to_OT OT.
  Module H := FMapList.Make MOT.
  Include FMapFacts.WFacts_fun MOT H.
  Include XMapFacts.WXFacts_fun MOT H.

  Module Properties := FMapFacts.WProperties_fun MOT H.

  Include H.
  Export Properties.
End MemorySegment.

Module LocalEnv.
  Module H := FMapList.Make Positive_as_OT.
  Include FMapFacts.WFacts_fun Positive_as_OT H.
  Include XMapFacts.WXFacts_fun Positive_as_OT H.

  Module Properties := FMapFacts.WProperties_fun Positive_as_OT H.

  Include H.
  Export Properties.
End LocalEnv.

Definition heap := MemorySegment.t byte.
Definition empty_heap := MemorySegment.empty byte.

Definition stack := MemorySegment.t byte.
Definition empty_stack := MemorySegment.empty byte.

Definition env := LocalEnv.t val.
Definition empty_env := LocalEnv.empty val.

Definition memory := heap.
Definition empty_memory := empty_heap.

Module Import S <: SEP.
  Definition mprop := memory -> Prop.

  (* We add the locks to the mix. *)

  Definition mimp (p q : mprop) := forall h, p h -> q h.
  Definition meq (p q : mprop) := forall h, p h <-> q h.

  (* Lifting a pure proposition: it must hold, and the heap must be empty. *)
  Definition lift (P : Prop) : mprop :=
    fun h => P /\ h = empty_memory.

(*
  Definition partition (m m1 m2 : memory) : Prop :=
    match (m, m1, m2) with
    | ((h, s), (h1, s1), (h2, s2)) =>
      MemorySegment.Properties.Partition h h1 h2 /\
        MemorySegment.Properties.Partition h s1 s2
    end.

  Definition disjoint (m1 : memory) (m2 : memory) : Prop :=
    match (m1, m2) with
    | ((h1, s1), (h2, s2)) =>
      MemorySegment.Properties.Disjoint h1 h2 /\
        MemorySegment.Properties.Disjoint s1 s2
    end.
*)

  Definition partition := MemorySegment.Properties.Partition.
  Definition disjoint := MemorySegment.Properties.Disjoint.

  (* Separating conjunction, one of the two big ideas of separation logic.
   * When does [star p q] apply to [h]?  When [h] can be partitioned into two
   * subheaps [h1] and [h2], respectively compatible with [p] and [q].  See book
   * module [Map] for definitions of [split] and [disjoint]. *)
  Definition star (p q : mprop) : mprop :=
    fun h => exists h1 h2, partition h h1 h2 /\ disjoint h1 h2 /\ p h1 /\ q h2.

  (* Existential quantification *)
  Definition exis A (p : A -> mprop) : mprop :=
    fun h => exists x, p x h.

  (* Convenient notations *)
  Notation "[| P |]" := (lift P) : sep_scope.
  Infix "*" := star : sep_scope.
  Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
  Delimit Scope sep_scope with sep.
  Notation "p === q" := (meq p%sep q%sep) (no associativity, at level 70).
  Notation "p ===> q" := (mimp p%sep q%sep) (no associativity, at level 70).

  Local Open Scope sep_scope.

  (* And now we prove some key algebraic properties, whose details aren't so
   * important.  The library automation uses these properties. *)

  Lemma iff_two : forall A (P Q : A -> Prop),
    (forall x, P x <-> Q x)
    -> (forall x, P x -> Q x) /\ (forall x, Q x -> P x).
  Proof.
    firstorder.
  Qed.

  Local Ltac t := (unfold mimp, meq, lift, star, exis; intuition; subst);
                 repeat (match goal with
                         | [ H : forall x, _ <-> _ |- _  ] =>
                           apply iff_two in H
                         | [ H : ex _ |- _ ] => destruct H
                         | [ H : partition _ _ empty_memory |- _ ] => apply MemorySegment.Partition_empty_r in H
                         end; intuition; subst); eauto 15.

  Theorem mimp_meq : forall p q, p === q
    <-> (p ===> q /\ q ===> p).
  Proof.
    t.
  Qed.

  Theorem mimp_refl : forall p, p ===> p.
  Proof.
    t.
  Qed.

  Theorem mimp_trans : forall p q r, p ===> q -> q ===> r -> p ===> r.
  Proof.
    t.
  Qed.

  Theorem lift_left : forall p (Q : Prop) r,
    (Q -> p ===> r)
    -> p * [| Q |] ===> r.
  Proof.
    t.
  Admitted.

  Theorem lift_right : forall p q (R : Prop),
    p ===> q
    -> R
    -> p ===> q * [| R |].
  Proof.
    t.
  Admitted.

(*  Hint Resolve split_empty_bwd'.*)

  Theorem extra_lift : forall (P : Prop) p,
    P
    -> p === [| P |] * p.
  Proof.
    t.
    (*apply split_empty_fwd' in H1; subst; auto.*)
  Admitted.

  Theorem star_comm : forall p q, p * q === q * p.
  Proof.
    t.
  Admitted.

  Theorem star_assoc : forall p q r, p * (q * r) === (p * q) * r.
  Proof.
    t.
  Admitted.

  Theorem star_cancel : forall p1 p2 q1 q2, p1 ===> p2
    -> q1 ===> q2
    -> p1 * q1 ===> p2 * q2.
  Proof.
    t.
  Qed.

  Theorem exis_gulp : forall A p (q : A -> _),
    p * exis q === exis (fun x => p * q x).
  Proof.
    t.
  Qed.

  Theorem exis_left : forall A (p : A -> _) q,
    (forall x, p x ===> q)
    -> exis p ===> q.
  Proof.
    t.
  Qed.

  Theorem exis_right : forall A p (q : A -> _) x,
    p ===> q x
    -> p ===> exis q.
  Proof.
    t.
  Qed.
End S.

Export S.
Module Import Se := SepCancel.Make(S).

Notation "$0" := empty_memory (at level 11).
Notation "$s0" := empty_stack (at level 12).
Notation "$h0" := empty_heap (at level 12).
Notation "$e0" := empty_env (at level 12).

Notation "m $+ ( a , v )" :=
  (MemorySegment.add a v m) (at level 13).
(*
Definition stack_mem1 (a : ptrofs) (v : byte) : memory :=
  ($h0, $s0 $+ (a, v)).
Definition stack_ptsto (a : ptrofs) (v : byte) : mprop :=
  fun m => m = stack_mem1 a v.
*)
Definition mem_mem1 (a : ptrofs) (v : byte) : memory :=
  $0 $+ (a, v).
Definition mem_ptsto (a : ptrofs) (v : byte) : mprop :=
  fun m => m = mem_mem1 a v.

(* Helpful notations, some the same as above *)
Notation "[| P |]" := (lift P) : sep_scope.
Notation emp := (lift True).
Notation MFalse := (lift False).
Infix "*" := star : sep_scope.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
Delimit Scope sep_scope with sep.
Notation "p === q" := (meq p%sep q%sep) (no associativity, at level 70).
Notation "p ===> q" := (mimp p%sep q%sep) (no associativity, at level 70).
Infix "|->" := mem_ptsto (at level 30) : sep_scope.

(* IMPORTANT: to make life easier, we forbid taking a step if a load happens anywhere
 * but in a simple Sassign (because we need to make sure we own that memory. *)
Function exp_no_load (e : expr) : Prop :=
  match e with
  | Evar _ => True
  | Econst _ => True
  | Eunop _ e' => exp_no_load e'
  | Ebinop _ e1 e2 => exp_no_load e1 /\ exp_no_load e2
  | Eload _ _ => False
  end.

(* Based on the original separation logic for Cminor. See
 * "Separation Logic for Small-step Cminor (extended version)" by Appel and Blazy.
 * https://hal.inria.fr/inria-00134699v5/document
 *)

(* Mutual recursion support could be added with something like
 * "Hoare Logic for Mutual Recursion and Local Variables" (von Oheimb) *)


(* Octuple / Nonuple *)
(* Stack memory, temp memory, and heap memory *)
(* Resource invariants: pre/post and crash *)
(* J ; (* G ; *) R ; B ; S ; E ||- {{P}} {{C}} s {{fun r => Q r}} *)
(* Not concurrently capturing "result" in the post-condition, except for call/returns... *)
(* For now, assumes function has been correctly "loaded" (stack space allocated, etc.) *)

(* A resource invariant is both a *strong* invariant (needs to be satisfied
 * at every step. Corresponds to the crash condition) and a *weak* invariant
 * (only applies to pre- and post-conditions). *)
Definition resource_invariant := (mprop * mprop)%type.

(* Abusing/Reusing MemorySegment.t, since it maps "pointers" to something *)
Definition resource_invariant_map := MemorySegment.t resource_invariant.

Definition return_condition := (list val -> mprop).
Definition block_conditions := list mprop.

Definition translate_pure (e : expr) (env : LocalEnv.am

(* C should always hold *)
Inductive hoare_judgement :
  resource_invariant_map -> return_condition -> block_conditions ->
  stack -> env ->
  mprop -> mprop -> stmt -> mprop -> Prop :=

| HtSkip : forall J R B S E P C,
    hoare_judgement J R B S E P C Sskip P
| HtLoop : forall J R B S E I C s,
    hoare_judgement J R B S E I C s I ->
    hoare_judgement J R B S E I C (Sloop s) MFalse
| HtExit : forall J R B S E C b n,
    nth_error B n = Some b ->
    hoare_judgement J R B S E b C (Sexit n) MFalse
| HtSeq : forall J R B S E P C Q s1 s2 P',
    hoare_judgement J R B S E P C s1 P' ->
    (P' ===> C) -> (* Is this right? *)
    hoare_judgement J R B S E P' C s2 Q ->
    hoare_judgement J R B S E P C (Sseq s1 s2) Q
| HtBlock : forall J R B S E P C Q s,
    hoare_judgement J R (Q::B) S E P C s MFalse ->
    hoare_judgement J R B S E P C (Sblock s) Q
| HtIfThenElseImpure : forall ,
    impure(e) ->
    hoare_judgement J R B S E P C (Sassign  ;; Sifthenelse e s1 s2) Q ->
    hoare_judgement J R B S E P C (Sifthenelse e s1 s2) Q -> (* Lift? *)

| HtIfThenElse : forall J R B S E P C Q e s1 s2,
    pure(e) -> (* Why pure? *)
    hoare_judgement J R B S E (P * lift(e)) C s1 Q -> (* Lift? *)
    hoare_judgement J R B S E (P * not(lift(e))) C s2 Q -> (* Lift? *)
    hoare_judgement J R B S E P C (Sifthenelse e s1 s2) Q -> (* Lift? *)


| HtReturn : forall J R B S E P C el vl,
    eval_expr el = Some vl ->
    R(vl) ->
    hoare_judgement J R B S E P C (Sreturn el) MFalse.


| HtAssign : forall J R B P C,
  ->
  hoare_judgement J R B S E P C (Sassign a e) 
| HtStore :
| HtCall :

| HtBlock :

(* TODO. Doesn't affect soundness; just completeness.
| HtTailCall :
| HtBuiltIn :
| HtSwitch :
| HtLabel :
| HtGoto :
*)


(* When forking into two threads, divide the (local) heap among them. *)
| HtPar : forall P1 c1 Q1 P2 c2 Q2,
    hoare_triple linvs P1 c1 Q1
    -> hoare_triple linvs P2 c2 Q2
    -> hoare_triple linvs (P1 * P2)%sep (Par c1 c2) (fun _ => Q1 tt * Q2 tt)%sep

| HtAlloc : forall numWords,
    hoare_triple linvs emp%sep (Alloc numWords) (fun r => r |--> zeroes numWords * [| r <> 0 |])%sep
| HtFree : forall a numWords,
    hoare_triple linvs (a |->? numWords)%sep (Free a numWords) (fun _ => emp)%sep

(* Next, how to handle locking: the thread takes ownership of a memory chunk
 * satisfying the lock's invariant. *)
| HtLock : forall a I1 I2,
    lookup linvs a = Some I
    -> hoare_triple linvs emp%sep (Lock a) (fun _ => I)
| HtCreateLock : forall a I1 I2,
    lookup linvs a = Some I
    -> hoare_triple linvs emp%sep (Lock a) (fun _ => I)
| HtDestroyLock : forall a I1 I2,
    lookup linvs a = Some I
    -> hoare_triple linvs emp%sep (Lock a) (fun _ => I)

(* When unlocking, the thread relinquishes ownership of a memory chunk
 * satisfying the lock's invariant. *)
| HtUnlock : forall a I,
    nth_error linvs a = Some I
    -> hoare_triple linvs I (Unlock a) (fun _ => emp)%sep

(* The usual consequence rule. *)
| HtConsequence : forall {result} (c : cmd result) P Q (P' : hprop) (Q' : _ -> hprop),
    hoare_triple linvs P c Q
    -> P' ===> P
    -> (forall r, Q r ===> Q' r)
    -> hoare_triple linvs P' c Q'

| HtFrame : forall {result} (c : cmd result) P Q R,
    hoare_triple linvs P c Q
    -> hoare_triple linvs (P * R)%sep c (fun r => Q r * R)%sep.

(* First, we have the basic separation-logic rules from before.  The only change
 * is in the threading-through of parameter [linvs]. *)
| HtReturn : forall P {result : Set} (v : result),
    hoare_triple linvs P (Return v) (fun r => P * [| r = v |])%sep
| HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
    hoare_triple linvs P c1 Q
    -> (forall r, hoare_triple linvs (Q r) (c2 r) R)
    -> hoare_triple linvs P (Bind c1 c2) R
| HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) I,
    (forall acc, hoare_triple linvs (I (Again acc)) (body acc) I)
    -> hoare_triple linvs (I (Again init)) (Loop init body) (fun r => I (Done r))
| HtFail : forall {result},
    hoare_triple linvs [| False |]%sep (Fail (result := result)) (fun _ => [| False |])%sep
| HtRead : forall a R,
    hoare_triple linvs (exists v, a |-> v * R v)%sep (Read a) (fun r => a |-> r * R r)%sep
| HtWrite : forall a v',
    hoare_triple linvs (exists v, a |-> v)%sep (Write a v') (fun _ => a |-> v')%sep

