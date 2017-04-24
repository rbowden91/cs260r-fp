Require Import Setoid Classes.Morphisms SepCancel Omega.
Require Import OrderedType OrderedTypeEx.
Require FMapList.
Require FMapFacts.
Import ListNotations.
Set Implicit Arguments.
Set Asymmetric Patterns.

Module NatMap := FMapList.Make Nat_as_OT.
Module NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.
Module NatMapProperties := FMapFacts.WProperties_fun Nat_as_OT NatMap.

(*Inductive vnode :=
| *)
Definition inode_num := nat.
Definition is_dir := bool.
Definition is_locked := bool.
Definition vnode := (inode_num * is_dir * is_locked)%type.

Inductive heapval :=
| HNat (n : nat)
| HVnode (v : vnode)
.

Inductive diskval :=
| DNat (n : nat)
.

Definition heap := NatMap.t heapval.
Definition disk := NatMap.t (diskval * list (list diskval)).
Notation locks := (list nat).

Hint Extern 1 (_ <= _) => omega.
Hint Extern 1 (@eq nat _ _) => omega.

Ltac invert' H := inversion H; clear H; subst.

Ltac invertN n :=
  match goal with
    | [ |- forall x : ?E, _ ] =>
      match type of E with
        | Prop =>
          let H := fresh in intro H;
            match n with
              | 1 => invert' H
              | S ?n' => invertN n'
            end
        | _ => intro; invertN n
      end
  end.

Ltac invert e := invertN e || invert' e.

Ltac simplify := repeat match goal with
                        | [ H : True |- _ ] => clear H
                        end;
                 repeat progress (simpl in *; intros; try autorewrite with core in *).

Ltac simp := repeat (simplify; subst; intuition idtac;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         end); try omega.


(** * A shared-memory concurrent language with loops *)

(* Let's work with a variant of the shared-memory concurrent language from last
 * time.  We add back in result types, loops, and dynamic memory allocation. *)

Inductive loop_outcome acc :=
| Done (a : acc)
| Again (a : acc).

Definition valueOf {A} (o : loop_outcome A) :=
  match o with
  | Done v => v
  | Again v => v
  end.

Inductive cmd : Type -> Type :=
| Return {result} (r : result) : cmd result
| Fail {result} : cmd result
| Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc

| Read (a : nat) : cmd heapval
| Write (a : nat) (v : heapval) : cmd unit

| DiskRead (a : nat) : cmd diskval
| DiskWrite (a : nat) (v : diskval) : cmd unit
| DiskSync : cmd unit
| DiskBarrier : cmd unit

| Lock (a : nat) : cmd unit
| Unlock (a : nat) : cmd unit
| Alloc (numWords : nat) : cmd nat
| Free (base numWords : nat) : cmd unit

| Par (c1 c2 : cmd unit) : cmd unit.


Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).
Infix "||" := Par.

Fixpoint initialize_heap (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => NatMap.add (base + numWords') (HNat 0) (initialize_heap h base numWords')
  end.

Fixpoint deallocate_heap (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => NatMap.remove base (deallocate_heap h (base+1) numWords')
  end.

Fixpoint initialize_disk (d : disk) (length : nat) : disk :=
  match length with
  | O => d
  | S length' => NatMap.add length' (DNat 0, []) (initialize_disk d length') 
  end.

Inductive step : forall A, disk * heap * cmd A -> disk * heap * cmd A -> Prop :=
| StepBindRecur : forall result result' (c1 c1' : cmd result') (c2 : result' -> cmd result) d h d' h',
  step (d, h, c1) (d', h', c1')
  -> step (d, h, Bind c1 c2) (d', h', Bind c1' c2)
| StepBindProceed : forall (result result' : Set) (v : result') (c2 : result' -> cmd result) d h,
  step (d, h, Bind (Return v) c2) (d, h, c2 v)
(* XXX ROB why doesn't this update state? *)
| StepLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)) h d,
  step (d, h, Loop init body) (d, h, o <- body init; match o with
                                                     | Done a => Return a
                                                     | Again a => Loop a body
                                                     end)

| StepRead : forall h a v d,
  NatMap.find a h = Some v
  -> step (d, h, Read a) (d, h, Return v)
| StepWrite : forall h a v v' d,
  NatMap.find a h = Some v
  -> step (d, h, Write a v') (d, NatMap.add a v' h, Return tt)
(* XXX something about None read? *)
| StepDiskRead : forall h a v vs d,
  NatMap.find a d = Some (v, vs)
  -> step (d, h, DiskRead a) (d, h, Return v)

| StepDiskWrite : forall h a v v0 vs vss d,
  NatMap.find a d = Some (v0, vs::vss) ->
  step (d, h, DiskWrite a v) (NatMap.add a (v, (v::vs)::vss) d, h, Return tt)
| StepDiskBarrier : forall h d,
  step (d, h, DiskBarrier) 
    (NatMap.map (fun v => match v with (v0, vss) => (v0, []::vss) end) d, h, Return tt)
| StepDiskSync : forall h d,
  step (d, h, DiskSync) (NatMap.map (fun v => match v with (v0, _) => (v0, []) end) d, h, Return tt)
| StepAlloc : forall (h:heap) (numWords:nat) (a:nat) (d:disk) (k:nat),
  NatMap.fold (fun k _ m => max k m)
              h 0 + 1 = k ->
  step (d, h, Alloc numWords) (d, initialize_heap h a numWords, Return a)

| StepFree : forall h a numWords d,
  step (d, h, Free a numWords) (d, deallocate_heap h a numWords, Return tt)

(* XXX this isn't quite right... *)
| StepLock : forall h a d,
  step (d, h, Lock a) (d, h, Return tt)
| StepUnlock : forall h a d,
  step (d, h, Unlock a) (d, h, Return tt)

| StepPar1 : forall d h c1 c2 d' h' c1',
  step (d, h, c1) (d', h', c1')
  -> step (d, h, Par c1 c2) (d', h', Par c1' c2)
| StepPar2 : forall d h c1 c2 d' h' c2',
  step (d, h, c2) (d', h', c2')
  -> step (d, h, Par c1 c2) (d', h', Par c1 c2').

(* Next, we define our notion of assertion and instantiate the generic
 * separation-logic cancelation automation, in exactly the same way as
 * before. *)
Module Import S <: SEP.
  Definition s_prop := heap * disk -> Prop.

  Definition s_imp (p q : s_prop) := forall h, p h -> q h.
  Definition s_eq (p q : s_prop) := forall h, p h <-> q h.

  (* Lifting a pure proposition: it must hold, and the heap must be empty. *)
  Definition lift (P : Prop) : s_prop :=
    fun h => P /\ h = (NatMap.empty heapval, NatMap.empty (diskval * list (list diskval))).

  (* Separating conjunction, one of the two big ideas of separation logic.
   * When does [star p q] apply to [h]?  When [h] can be partitioned into two
   * subheaps [h1] and [h2], respectively compatible with [p] and [q].  See book
   * module [Map] for definitions of [split] and [disjoint]. *)
  Definition star (p q : s_prop) : s_prop :=
    fun s => exists h d h1 h2 d1 d2, 
      s = (h,d) ->
      NatMapProperties.Partition h h1 h2 /\ NatMapProperties.Disjoint h1 h2 /\
      NatMapProperties.Partition d d1 d2 /\ NatMapProperties.Disjoint d1 d2 /\
      p (h1,d1) /\ q (h2,d2).

  (* Existential quantification *)
  Definition exis A (p : A -> s_prop) : s_prop :=
    fun h => exists x, p x h.

  (* Convenient notations *)
  Notation "[| P |]" := (lift P) : sep_scope.
  Infix "*" := star : sep_scope.
  Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
  Delimit Scope sep_scope with sep.
  Notation "p === q" := (s_eq p%sep q%sep) (no associativity, at level 70).
  Notation "p ===> q" := (s_imp p%sep q%sep) (no associativity, at level 70).

  Local Open Scope sep_scope.

  (* And now we prove some key algebraic properties, whose details aren't so
   * important.  The library automation uses these properties. *)

  Lemma iff_two : forall A (P Q : A -> Prop),
    (forall x, P x <-> Q x)
    -> (forall x, P x -> Q x) /\ (forall x, Q x -> P x).
  Proof.
    firstorder.
  Qed.
(*
  Local Ltac t := (unfold s_imp, s_eq, lift, star, exis; propositional; subst);
                 repeat (match goal with
                         | [ H : forall x, _ <-> _ |- _  ] =>
                           apply iff_two in H
                         | [ H : ex _ |- _ ] => destruct H
                         | [ H : split _ _ (NatMap.empty |- _ ] => apply split_empty_fwd in H
                         end; propositional; subst); eauto 15.
*)
  Theorem s_imp_s_eq : forall p q, p === q
    <-> (p ===> q /\ q ===> p).
  Proof.
  Admitted.

  Theorem s_imp_refl : forall p, p ===> p.
  Proof.
  Admitted.

  Theorem s_imp_trans : forall p q r, p ===> q -> q ===> r -> p ===> r.
  Proof.
  Admitted.

  Theorem lift_left : forall p (Q : Prop) r,
    (Q -> p ===> r)
    -> p * [| Q |] ===> r.
  Proof.
  Admitted.

  Theorem lift_right : forall p q (R : Prop),
    p ===> q
    -> R
    -> p ===> q * [| R |].
  Proof.
  Admitted.
(*
  Hint Resolve split_empty_bwd'.
*)
  Theorem extra_lift : forall (P : Prop) p,
    P
    -> p === [| P |] * p.
  Proof.
  Admitted.
(*
    apply split_empty_fwd' in H1; subst; auto.
  Qed.    
*)
  Theorem star_comm : forall p q, p * q === q * p.
  Proof.
  Admitted.

  Theorem star_assoc : forall p q r, p * (q * r) === (p * q) * r.
  Proof.
  Admitted.

  Theorem star_cancel : forall p1 p2 q1 q2, p1 ===> p2
    -> q1 ===> q2
    -> p1 * q1 ===> p2 * q2.
  Proof.
  Admitted.

  Theorem exis_gulp : forall A p (q : A -> _),
    p * exis q === exis (fun x => p * q x).
  Proof.
  Admitted.

  Theorem exis_left : forall A (p : A -> _) q,
    (forall x, p x ===> q)
    -> exis p ===> q.
  Proof.
  Admitted.

  Theorem exis_right : forall A p (q : A -> _) x,
    p ===> q x
    -> p ===> exis q.
  Proof.
  Admitted.
End S.

Export S.

Module Import Se := SepCancel.Make(S).
Export Se.

Definition foral A (p : A -> s_prop) : s_prop :=
    fun h => forall x, p x h.

(* Capturing single-mapping heaps *)
Definition empty_heap : heap := NatMap.empty heapval.
Definition empty_disk : disk := NatMap.empty (diskval * list (list diskval)).
Definition heap1 a v : heap := NatMap.add a v empty_heap.
Definition heap_ptsto a v : s_prop :=
  fun h => h = (heap1 a v, empty_disk).

Notation "[| P |]" := (lift P) : sep_scope.
Notation emp := (lift True).
Infix "*" := star : sep_scope.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
(*Notation "'forall_' x .. y , p" := (foral (fun x => .. (foral (fun y => p)) ..)) (no associativity, at level 70) : sep_scope.*)
Delimit Scope sep_scope with sep.
Notation "p === q" := (s_eq p%sep q%sep) (no associativity, at level 70).
Notation "p ===> q" := (s_imp p%sep q%sep) (no associativity, at level 70).
Infix "|->" := heap_ptsto (at level 30) : sep_scope.

Fixpoint multi_heap_ptsto (a : nat) (vs : list heapval) : s_prop :=
  match vs with
  | nil => emp
  | v :: vs' => a |-> v * multi_heap_ptsto (a + 1) vs'
  end%sep.

Infix "|-->" := multi_heap_ptsto (at level 30) : sep_scope.

Fixpoint heap_zeroes (n : nat) : list heapval :=
  match n with
  | O => nil
  | S n' => heap_zeroes n' ++ HNat 0 :: nil
  end.

Fixpoint allocated (a n : nat) : s_prop :=
  match n with
  | O => emp
  | S n' => (exists v, a |-> v) * allocated (a+1) n'
  end%sep.

Infix "|->?" := allocated (at level 30) : sep_scope.




Inductive hoare (linvs : list (s_prop * s_prop)) : forall {result}, s_prop -> s_prop -> cmd result -> s_prop -> (result -> s_prop) -> Prop :=

| HtReturn : forall C P {result : Set} (v : result),
    hoare linvs C P (Return v) C (fun r => P * [| r = v |])%sep

| HtBind : forall PC QC RC P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
    hoare linvs PC P c1 QC Q
    -> (forall r, hoare linvs QC (Q r) (c2 r) RC R)
    -> hoare linvs PC P (Bind c1 c2) RC R

| HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) I IC,
    (forall acc, hoare linvs IC (I (Again acc)) (body acc) IC I)
    -> hoare linvs IC (I (Again init)) (Loop init body) IC (fun r => I (Done r))

(* XXX ROB Crash condition here?? *)
| HtFail : forall {result},
    hoare linvs ([|False|])%sep ([|False|])%sep (Fail (result := result)) ([|False|])%sep (fun _ => [| False |])%sep

| HtRead : forall a R C,
    hoare linvs C (exists v, a |-> v * R v)%sep (Read a) C (fun r => a |-> r * R r)%sep

| HtWrite : forall a v' C,
    hoare linvs C (exists v, a |-> v)%sep (Write a v') C (fun _ => a |-> v')%sep

(* XXX
| HtDiskRead : forall a R C,
    hoare linvs C ((exists v, a |-> v * R v), emp)%sep (Read a) (fun r => (a |-> r * R r, emp))%sep

| HtDiskWrite : forall a v' C,
    hoare linvs C ((exists v, a |-> v), emp)%sep (Write a v') (fun _ => (a |-> v', emp))%sep.
Barrier/Sync
*)
| HtAlloc : forall numWords C,
    hoare linvs C emp%sep (Alloc numWords) C (fun r => r |--> heap_zeroes numWords * [| r <> 0 |])%sep
| HtFree : forall a numWords C,
    hoare linvs C (a |->? numWords)%sep (Free a numWords) C (fun _ => emp)%sep

(* Next, how to handle locking: the thread takes ownership of a memory chunk
 * satisfying the lock's invariant. *)
| HtLock : forall a I IC,
    nth_error linvs a = Some (IC, I)
    -> hoare linvs emp%sep emp%sep (Lock a) IC (fun _ => I)

(* When unlocking, the thread relinquishes ownership of a memory chunk
 * satisfying the lock's invariant. *)
| HtUnlock : forall a I IC,
    nth_error linvs a = Some (IC, I)
    -> hoare linvs IC I (Unlock a) emp%sep (fun _ => emp)%sep

(* XXX think through the crash conditions. *)
(* When forking into two threads, divide the (local) heap among them. *)
| HtPar : forall PC P1 c1 Q1 P2 c2 Q2,
    hoare linvs PC P1 c1 PC Q1
    -> hoare linvs PC P2 c2 PC Q2
    -> hoare linvs PC (P1 * P2)%sep (Par c1 c2) PC (fun _ => Q1 tt * Q2 tt)%sep

(* XXX something to add to the crash condition? Definitely can't take away... *)

(* Now we repeat these two structural rules from before. *)
| HtConsequence : forall {result} (c : cmd result) PC QC P Q (P' : s_prop) (Q' : _ -> s_prop),
    hoare linvs PC P c QC Q
    -> P' ===> P
    -> (forall r, Q r ===> Q' r)
    -> hoare linvs PC P' c QC Q'

| HtFrame : forall {result} (c : cmd result) P Q R PC QC,
    hoare linvs PC P c QC Q
    -> hoare linvs PC (P * R)%sep c QC (fun r => Q r * R)%sep.


Notation "linvs ||- {{ PC }} {{ P }} c {{ QC }} {{ r ~> Q }}" :=
  (hoare linvs PC%sep P%sep c QC%sep (fun r => Q%sep)) (at level 90, c at next level).

Lemma HtStrengthen : forall linvs {result} (c : cmd result) PC P QC Q (Q' : _ -> s_prop),
    hoare linvs PC P c QC Q
    -> (forall r, Q r ===> Q' r)
    -> hoare linvs PC P c QC Q'.
Proof.
  intros.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.

Lemma HtWeaken : forall linvs {result} (c : cmd result) PC P QC Q (P' : s_prop),
    hoare linvs PC P c QC Q
    -> P' ===> P
    -> hoare linvs PC P' c QC Q.
Proof.
  intros.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.


Opaque s_eq s_imp lift star exis heap_ptsto.

Theorem use_lemma : forall linvs result P' (c : cmd result) (Q : result -> s_prop) P R PC QC,
  hoare linvs PC P' c QC Q
  -> P ===> P' * R
  -> hoare linvs PC P c QC (fun r => Q r * R)%sep.
Proof.
  simp.
  eapply HtWeaken.
  eapply HtFrame.
  eassumption.
  eauto.
Qed.

Theorem HtRead' : forall linvs a v C,
  hoare linvs C (a |-> v)%sep (Read a) C (fun r => a |-> v * [| r = v |])%sep.
Proof.
  simp.
  apply HtWeaken with (exists r, a |-> r * [| r = v |])%sep.
  eapply HtStrengthen.
  apply HtRead.
  simp.
  cancel; auto.
  subst; cancel.
  cancel; auto.
Qed.

Theorem HtRead'' : forall linvs p P R C,
  P ===> (exists v, p |-> v * R v)
  -> hoare linvs C P (Read p) C (fun r => p |-> r * R r)%sep.
Proof.
  simp.
  eapply HtWeaken.
  apply HtRead.
  assumption.
Qed.

Lemma HtReturn' : forall linvs P {result : Set} (v : result) Q C,
    P ===> Q v
    -> hoare linvs C P (Return v) C Q.
Proof.
  simp.
  eapply HtStrengthen.
  constructor.
  simp.
  cancel.
Qed.

Ltac basic := apply HtReturn' || eapply HtWrite || eapply HtAlloc || eapply HtFree
              || (eapply HtLock; simpl; solve [ eauto ])
              || (eapply HtUnlock; simpl; solve [ eauto ]).
Ltac step0 := basic || eapply HtBind || (eapply use_lemma; [ basic | cancel; auto ])
              || (eapply use_lemma; [ eapply HtRead' | solve [ cancel; auto ] ])
              || (eapply HtRead''; solve [ cancel ])
              || (eapply HtStrengthen; [ eapply use_lemma; [ basic | cancel; auto ] | ])
              || (eapply HtConsequence; [ apply HtFail | .. ]).
Ltac step := step0; simp.
Ltac ht := simp; repeat step.
Ltac conseq := simpl; eapply HtConsequence.
Ltac use_IH H := conseq; [ apply H | .. ]; ht.
Ltac loop_inv0 Inv := (eapply HtWeaken; [ apply HtLoop with (I := Inv) | .. ])
                      || (eapply HtConsequence; [ apply HtLoop with (I := Inv) | .. ]).
Ltac loop_inv Inv := loop_inv0 Inv; ht.
Ltac fork0 P1 P2 := apply HtWeaken with (P := (P1 * P2)%sep); [ apply HtPar | ].
Ltac fork P1 P2 := fork0 P1 P2 || (eapply HtStrengthen; [ fork0 P1 P2 | ]).
Ltac use H := (eapply use_lemma; [ eapply H | cancel; auto ])
              || (eapply HtStrengthen; [ eapply use_lemma; [ eapply H | cancel; auto ] | ]).

Ltac s_eq := intros; apply s_imp_s_eq; split.

Instance hoare_morphism : forall linvs A,
  Proper (s_eq ==> s_eq ==> eq ==> s_eq ==> (eq ==> s_eq) ==> iff) (@hoare linvs A).
Proof.
  Transparent s_imp.
  repeat (hnf; intros).
  unfold pointwise_relation in *; intuition subst.
(*
  eapply HtConsequence; eauto.
  rewrite H; reflexivity.
  intros.
  hnf in H1.
  specialize (H1 r _ eq_refl).
  rewrite H1; reflexivity.

  eapply HtConsequence; eauto.
  rewrite H; reflexivity.
  intros.
  hnf in H1.
  specialize (H1 r _ eq_refl).
  rewrite H1; reflexivity.
  Opaque s_imp.
Qed.
*)
Admitted.

Theorem try_ptsto_first : forall a v, try_me_first (heap_ptsto a v).
Proof.
  simplify.
  apply try_me_first_easy.
Qed.

Hint Resolve try_ptsto_first.


(** ** The nonzero shared counter *)

(* This program has two threads shared a numeric counter, which starts out as
 * nonzero and remains that way, since each thread only increments the counter,
 * with the lock held to avoid race conditions.  (Actually, the lock isn't
 * needed to maintain the property in this case, but it's a pleasant starting
 * example, and reasoning about racey code is more involved.) *)

Example incrementer :=
  for i := tt loop
    _ <- Lock 0;
    n <- Read 0;
    n' <- match n with HNat n' => Return n' | _ => Fail end;
    _ <- Write 0 (HNat (n' + 1));
    _ <- Unlock 0;
    if Nat.eq_dec n' 0 then
      Fail
    else
      Return (Again tt)
  done.

(* Recall that each lock has an associated invariant.  This program only uses
 * lock 0, and here's its invariant: memory cell 0 holds a positive number. *)
Definition incrementer_inv := 
  (emp, exists n, 0 |-> HNat n * [| n > 0 |])%sep.
(*
Theorem incrementers_ok :
    [incrementer_inv] ||- {{emp}} {{emp}} (incrementer || incrementer) {{emp}} {{_ ~> emp}}.
Proof.
  unfold incrementer, incrementer_inv.
  (* When we must prove a parallel composition, we manually explain how to split
   * the precondition into two, one for each new thread.  In this case, there is
   * no local state to share, so both sides are empty. *)
  fork (emp%sep) (emp%sep).

  (* This loop invariant is also trivial, since neither thread has persistent
   * local state. *)
(*
eapply HtWeaken; [ apply HtLoop with (I:=fun _ : loop_outcome unit => emp%sep)| .. ]. 
simp. step. step. step. (eapply HtRead''). hide_evars. normalize.
    eapply HtWeaken with .
    apply s_imp_refl. admit.
    match goal with
      | [ |- _ ===> ?Q ] =>
        match Q with

        | _ => apply s_imp_refl
        end
      | _ => progress autorewrite with core
    end; auto.


 repeat cancel1. cancel. solve [ cancel ]. simp. step. repeat step.*)
  loop_inv (fun _ : loop_outcome unit => emp%sep).
  cases (r0 ==n 0); ht.
  cancel.
  linear_arithmetic.
  cancel.
  cancel.
  cancel.

  loop_inv (fun _ : loop_outcome unit => emp%sep).
  cases (r0 ==n 0); ht.
  cancel.
  linear_arithmetic.
  cancel.
  cancel.
  cancel.

  cancel.
  cancel.
Qed.

(* Hm, we used exactly the same proof code for each thread, which makes sense,
 * since they share the same code.  Let's take advantage of this symmetry to
 * prove that any 2^n-way composition of this code remains correct. *)

Fixpoint incrementers (n : nat) :=
  match n with
  | O => incrementer
  | S n' => incrementers n' || incrementers n'
  end.

Theorem any_incrementers_ok : forall n,
    [incrementer_inv] ||- {{emp}} incrementers n {{_ ~> emp}}.
Proof.
  induct n; simp.

  unfold incrementer, incrementer_inv.
  loop_inv (fun _ : loop_outcome unit => emp%sep).
  cases (r0 ==n 0); ht.
  cancel.
  linear_arithmetic.
  cancel.
  cancel.
  cancel.

  fork (emp%sep) (emp%sep); eauto.
  cancel.
  cancel.
Qed.


(** ** Producer-consumer with a linked list *)

(* First, here's a literal repetition of the definition of linked lists from
 * SeparationLogic.v. *)

Fixpoint linkedList (p : nat) (ls : list nat) :=
  match ls with
    | nil => [| p = 0 |]
    | x :: ls' => [| p <> 0 |]
                  * exists p', p |--> [x; p'] * linkedList p' ls'
  end%sep.

Theorem linkedList_null : forall ls,
  linkedList 0 ls === [| ls = nil |].
Proof.
  s_eq; cases ls; cancel.
Qed.

Theorem linkedList_nonnull : forall p ls,
  p <> 0
  -> linkedList p ls === exists x ls' p', [| ls = x :: ls' |] * p |--> [x; p'] * linkedList p' ls'.
Proof.
  s_eq; cases ls; cancel; match goal with
                         | [ H : _ = _ :: _ |- _ ] => invert H
                         end; cancel.
Qed.

(* Now let's use linked lists as shared stacks for communication between
 * threads, with a lock protecting each stack.  To start out with, here's a
 * producer-consumer example with just one stack.  The producer is looping
 * pushing the consecutive even numbers to the stack, and the consumer is
 * looping popping numbers and failing if they're odd. *)

Example producer :=
  _ <- for i := 0 loop
    cell <- Alloc 2;
    _ <- Write cell i;
    _ <- Lock 0;
    head <- Read 0;
    _ <- Write (cell+1) head;
    _ <- Write 0 cell;
    _ <- Unlock 0;
    Return (Again (2 + i))
  done;
  Return tt.

Fixpoint isEven (n : nat) : bool :=
  match n with
  | O => true
  | S (S n) => isEven n
  | _ => false
  end.

Example consumer :=
  for i := tt loop
    _ <- Lock 0;
    head <- Read 0;
    if head ==n 0 then
      _ <- Unlock 0;
      Return (Again tt)
    else
      tail <- Read (head+1);
      _ <- Write 0 tail;
      _ <- Unlock 0;
      data <- Read head;
      _ <- Free head 2;
      if isEven data then
        Return (Again tt)
      else
        Fail
  done.

(* Invariant of the only lock: cell 0 points to a linked list, whose elements
 * are all even. *)
Definition producer_consumer_inv :=
  (exists ls p, 0 |-> p * linkedList p ls * [| forallb isEven ls = true |])%sep.

(* Let's prove that the program is correct (can never [Fail]). *)
Theorem producer_consumer_ok :
  [producer_consumer_inv] ||- {{emp}} producer || consumer {{_ ~> emp}}.
Proof.
  unfold producer_consumer_inv, producer, consumer.
  fork (emp%sep) (emp%sep); ht.

  loop_inv (fun o => [| isEven (valueOf o) = true |]%sep).
  match goal with
  | [ H : r = 0 -> False |- _ ] => erewrite (linkedList_nonnull _ H)
  end.
  cancel.
  simp.
  apply andb_true_iff; propositional.
  cancel.
  cancel.
  cancel.
  
  loop_inv (fun _ : loop_outcome unit => emp%sep).
  cases (r0 ==n 0).
  ht.
  cancel.
  setoid_rewrite (linkedList_nonnull _ n).
  ht.
  apply andb_true_iff in H.
  simp.
  cases (isEven r4); ht.
  cancel.
  cancel.
  simp.
  rewrite Heq in H0.
  simp.
  equality.
  cancel.
  cancel.
  cancel.

  cancel.
Qed.


(** ** A length-3 producer-consumer chain *)

(* Here's a variant on the last example.  Now we have three stages.
 * Stage 1: push consecutive even numbers to stack 1.
 * Stage 2: pop from stack 1 and push to stack 1, reusing the memory for the
 *          list node.
 * Stage 3: pop from stack 2 and fail if odd. *)

Example stage1 :=
  _ <- for i := 0 loop
    cell <- Alloc 2;
    _ <- Write cell i;
    _ <- Lock 0;
    head <- Read 0;
    _ <- Write (cell+1) head;
    _ <- Write 0 cell;
    _ <- Unlock 0;
    Return (Again (2 + i))
  done;
  Return tt.

Example stage2 :=
  for i := tt loop
    _ <- Lock 0;
    head <- Read 0;
    if head ==n 0 then
      _ <- Unlock 0;
      Return (Again tt)
    else
      tail <- Read (head+1);
      _ <- Write 0 tail;
      _ <- Unlock 0;

      _ <- Lock 1;
      head' <- Read 1;
      _ <- Write (head+1) head';
      _ <- Write 1 head;
      _ <- Unlock 1;

      Return (Again tt)
  done.

Example stage3 :=
  for i := tt loop
    _ <- Lock 1;
    head <- Read 1;
    if head ==n 0 then
      _ <- Unlock 1;
      Return (Again tt)
    else
      tail <- Read (head+1);
      _ <- Write 1 tail;
      _ <- Unlock 1;
      data <- Read head;
      _ <- Free head 2;
      if isEven data then
        Return (Again tt)
      else
        Fail
  done.

(* Same invariant as before, for each of the two stacks. *)
Definition stages_inv root :=
  (exists ls p, root |-> p * linkedList p ls * [| forallb isEven ls = true |])%sep.

Theorem stages_ok :
  [stages_inv 0; stages_inv 1] ||- {{emp}} stage1 || stage2 || stage3 {{_ ~> emp}}.
Proof.
  unfold stages_inv, stage1, stage2, stage3.
  fork (emp%sep) (emp%sep); ht.
  fork (emp%sep) (emp%sep); ht.

  loop_inv (fun o => [| isEven (valueOf o) = true |]%sep).
  match goal with
  | [ H : r = 0 -> False |- _ ] => erewrite (linkedList_nonnull _ H)
  end.
  cancel.
  simp.
  apply andb_true_iff; propositional.
  cancel.
  cancel.
  cancel.
  
  loop_inv (fun _ : loop_outcome unit => emp%sep).
  simp.
  cases (r0 ==n 0).
  ht.
  cancel.
  setoid_rewrite (linkedList_nonnull _ n).
  ht.
  apply andb_true_iff in H.
  simp.
  erewrite (linkedList_nonnull _ n).
  cancel.
  simp.
  apply andb_true_iff in H1.
  apply andb_true_iff.
  simp.
  cancel.
  cancel.
  cancel.

  loop_inv (fun _ : loop_outcome unit => emp%sep).
  simp.
  cases (r0 ==n 0).
  ht.
  cancel.
  setoid_rewrite (linkedList_nonnull _ n).
  ht.
  apply andb_true_iff in H.
  simp.
  simp.
  cases (isEven r4); ht.
  cancel.
  cancel.
  simp.
  rewrite Heq in H0.
  simp.
  equality.
  cancel.
  cancel.
  cancel.

  cancel.
Qed.


(** * Soundness proof *)

(* We can still prove that the logic is sound.  That is, any state compatible
 * with a proved Hoare triple has the invariant that it never fails.  See the
 * book PDF for a sketch of the important technical devices and lemmas in this
 * proof. *)

Hint Resolve s_imp_refl.

Lemma invert_Return : forall linvs {result : Set} (r : result) P Q,
  hoare_triple linvs P (Return r) Q
  -> P ===> Q r.
Proof.
  induct 1; propositional; eauto.

  cancel.

  eauto using s_imp_trans.

  rewrite IHhoare_triple; eauto.
Qed.

Hint Constructors hoare_triple.

Lemma invert_Bind : forall linvs {result' result} (c1 : cmd result') (c2 : result' -> cmd result) P Q,
  hoare_triple linvs P (Bind c1 c2) Q
  -> exists R, hoare_triple linvs P c1 R
               /\ forall r, hoare_triple linvs (R r) (c2 r) Q.
Proof.
  induct 1; propositional; eauto.

  invert IHhoare_triple; propositional.
  eexists; propositional.
  eapply HtWeaken.
  eassumption.
  auto.
  eapply HtStrengthen.
  apply H4.
  auto.

  simp.
  exists (fun r => x r * R)%sep.
  propositional.
  eapply HtFrame; eauto.
  eapply HtFrame; eauto.
Qed.

Transparent s_eq s_imp lift star exis ptsto.

Lemma invert_Loop : forall linvs {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) P Q,
    hoare_triple linvs P (Loop init body) Q
    -> exists I, (forall acc, hoare_triple linvs (I (Again acc)) (body acc) I)
                 /\ P ===> I (Again init)
                 /\ (forall r, I (Done r) ===> Q r).
Proof.
  induct 1; propositional; eauto.

  invert IHhoare_triple; propositional.
  exists x; propositional; eauto.
  unfold s_imp in *; eauto.

  eauto using s_imp_trans.

  simp.
  exists (fun o => x o * R)%sep; propositional; eauto.
  rewrite H0; eauto.
  rewrite H3; eauto.
Qed.

(* Now that we proved enough basic facts, let's hide the definitions of all
 * these predicates, so that we reason about them only through automation. *)
Opaque s_eq s_imp lift star exis ptsto.

Lemma unit_not_nat : unit = nat -> False.
Proof.
  simplify.
  assert (exists x : unit, forall y : unit, x = y).
  exists tt; simplify.
  cases y; reflexivity.
  rewrite H in H0.
  invert H0.
  specialize (H1 (S x)).
  linear_arithmetic.
Qed.

Lemma invert_Read : forall linvs a P Q,
  hoare_triple linvs P (Read a) Q
  -> exists R, (P ===> exists v, a |-> v * R v)%sep
               /\ forall r, a |-> r * R r ===> Q r.
Proof.
  induct 1; simp; eauto.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  eauto 7 using s_imp_trans.

  exists (fun n => x n * R)%sep; simp.
  rewrite H1.
  cancel.

  rewrite <- H2.
  cancel.
Qed.

Lemma invert_Write : forall linvs a v' P Q,
  hoare_triple linvs P (Write a v') Q
  -> exists R, (P ===> (exists v, a |-> v) * R)%sep
               /\ a |-> v' * R ===> Q tt.
Proof.
  induct 1; simp; eauto.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  exists emp; simp.
  cancel; auto.
  cancel; auto.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  eauto 7 using s_imp_trans.

  exists (x * R)%sep; simp.
  rewrite H1.
  cancel.

  cancel.
  rewrite <- H2.
  cancel.
Qed.

Lemma invert_Alloc : forall linvs numWords P Q,
  hoare_triple linvs P (Alloc numWords) Q
  -> forall r, P * r |--> zeroes numWords * [| r <> 0 |] ===> Q r.
Proof.
  induct 1; simp; eauto.

  apply unit_not_nat in x0; simp.

  cancel.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  rewrite H0; eauto.
  eauto 7 using s_imp_trans.

  rewrite <- IHhoare_triple.
  cancel.
Qed.

(* Temporarily transparent again! *)
Transparent s_eq s_imp lift star exis ptsto.

Lemma zeroes_initialize' : forall h a v,
    h $? a = None
    -> (fun h' : heap => h' = h $+ (a, v)) ===> (fun h' => h' = h) * a |-> v.
Proof.
  unfold s_imp, star, split, ptsto, disjoint; simp.
  exists h, (heap1 a v).
  propositional.
  maps_equal.
  unfold heap1.
  rewrite lookup_join2.
  simp.
  simp.
  apply lookup_None_dom in H.
  propositional.
  cases (h $? k).
  rewrite lookup_join1; auto.
  eauto using lookup_Some_dom.
  rewrite lookup_join2; auto.
  unfold heap1; simp.
  eauto using lookup_None_dom.
  unfold heap1 in *.
  cases (a ==n a0); simp.
Qed.

(* Opaque again! *)
Opaque s_eq s_imp lift star exis ptsto.

Lemma multi_ptsto_app : forall ls2 ls1 a,
     a |--> ls1 * (a + length ls1) |--> ls2 ===> a |--> (ls1 ++ ls2).
Proof.
  induct ls1; simp; cancel; auto.

  replace (a + 0) with a by linear_arithmetic.
  cancel.

  rewrite <- IHls1.
  cancel.
  replace (a0 + 1 + length ls1) with (a0 + S (length ls1)) by linear_arithmetic.
  cancel.
Qed.

Lemma length_zeroes : forall n,
    length (zeroes n) = n.
Proof.
  induct n; simplify; auto.
  rewrite app_length; simplify.
  linear_arithmetic.
Qed.

Lemma initialize_fresh : forall a' h a numWords,
    a' >= a + numWords
    -> initialize h a numWords $? a' = h $? a'.
Proof.
  induct numWords; simp; auto.
Qed.

Lemma zeroes_initialize : forall numWords a h,
    (forall i, i < numWords -> h $? (a + i) = None)
    -> (fun h' => h' = initialize h a numWords) ===> (fun h' => h' = h) * a |--> zeroes numWords.
Proof.
  induct numWords; simp.

  cancel; auto.
  rewrite <- multi_ptsto_app.
  rewrite zeroes_initialize'.
  erewrite IHnumWords.
  simp.
  rewrite length_zeroes.
  cancel; auto.
  auto.
  rewrite initialize_fresh; auto.
Qed.

Lemma invert_Free : forall linvs a numWords P Q,
  hoare_triple linvs P (Free a numWords) Q
  -> P ===> a |->? numWords * Q tt.
Proof.
  induct 1; simp; eauto.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  cancel; auto.

  rewrite H0.
  rewrite IHhoare_triple.
  cancel; auto.

  rewrite IHhoare_triple.
  cancel; auto.
Qed.

(* Temporarily transparent again! *)
Transparent s_eq s_imp lift star exis ptsto.

Lemma do_deallocate' : forall a Q h,
    ((exists v, a |-> v) * Q)%sep h
    -> Q (h $- a).
Proof.
  unfold ptsto, star, split, heap1; simp.
  invert H1.
  replace ($0 $+ (a, x1) $++ x0 $- a) with x0; auto.
  maps_equal.
  cases (k ==n a); simp.
  specialize (H a).
  simp.
  cases (x0 $? a); auto.
  exfalso; apply H; equality.
  rewrite lookup_join2; auto.
  apply lookup_None_dom.
  simp.
Qed.

Lemma do_deallocate : forall Q numWords a h,
    (a |->? numWords * Q)%sep h
    -> Q (deallocate h a numWords).
Proof.
  induct numWords; simp.

  unfold star, exis, lift in H; simp.
  apply split_empty_fwd' in H0; simp.

  apply IHnumWords.
  clear IHnumWords.
  
  apply do_deallocate'.
  Opaque s_eq s_imp lift star exis ptsto.
  match goal with
  | [ H : ?P h |- ?Q h ] => assert (P ===> Q) by cancel
  end.
  Transparent s_imp.
  apply H0; auto.
  Opaque s_imp.
Qed.

Opaque s_eq s_imp lift star exis ptsto.

Lemma invert_Lock : forall linvs a P Q,
  hoare_triple linvs P (Lock a) Q
  -> exists I, nth_error linvs a = Some I
               /\ P * I ===> Q tt.
Proof.
  induct 1; simp; eauto 10.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  eexists; simp.
  eauto.
  cancel.

  eexists; simp.
  eauto.
  rewrite H0; eauto using s_imp_trans.

  eexists; simp.
  eauto.
  rewrite <- H2.
  cancel.
Qed.

Lemma invert_Unlock : forall linvs a P Q,
  hoare_triple linvs P (Unlock a) Q
  -> exists I, nth_error linvs a = Some I
               /\ P ===> Q tt * I.
Proof.
  induct 1; simp; eauto 10.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  eexists; simp.
  eauto.
  cancel.

  eexists; simp.
  eauto.
  rewrite <- H1; eauto using s_imp_trans.

  eexists; simp.
  eauto.
  rewrite H2.
  cancel.
Qed.

Lemma invert_Par : forall linvs c1 c2 P Q,
  hoare_triple linvs P (Par c1 c2) Q
  -> exists P1 P2 Q1 Q2,
      hoare_triple linvs P1 c1 Q1
      /\ hoare_triple linvs P2 c2 Q2
      /\ P ===> P1 * P2
      /\ Q1 tt * Q2 tt ===> Q tt.
Proof.
  induct 1; simp; eauto 10.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  eauto 10 using s_imp_trans.

  exists (x * R)%sep, x0, (fun r => x1 r * R)%sep, x2; simp; eauto.
  rewrite H2; cancel.
  rewrite <- H4; cancel.
Qed.

(* Temporarily transparent again! *)
Transparent s_eq s_imp lift star exis ptsto.

(* Guarded predicates *)
Definition guarded (P : Prop) (p : s_prop) : s_prop :=
  fun h => IF P then p h else emp%sep h.

Infix "===>" := guarded : sep_scope.

Theorem guarded_true : forall (P : Prop) p, P
  -> (P ===> p) === p.
Proof.
  unfold s_eq, guarded, IF_then_else; simp.
Qed.

Theorem guarded_false : forall (P : Prop) p, ~P
  -> (P ===> p) === emp.
Proof.
  unfold s_eq, guarded, IF_then_else; simp.
Qed.

(* Iterated separating conjunction *)
Fixpoint bigstar A (P : nat -> A -> s_prop) (ls : list A) : s_prop :=
  match ls with
  | nil => emp
  | x :: ls' => P 0 x * bigstar (fun n => P (S n)) ls'
  end%sep.

Definition lockChunks (l : locks) (ls : list s_prop) :=
  bigstar (fun i I => (~i \in l) ===> I)%sep ls.

Lemma use_s_imp : forall P Q, P ===> Q
  -> forall h, P h -> Q h.
Proof.
  auto.
Qed.

Lemma ptsto_out : forall h a v p,
    h $? a = Some v
    -> (exists v', a |-> v' * p v')%sep h
    -> (a |-> v * p v)%sep h
       /\ forall v', (a |-> v' * p v)%sep (h $+ (a, v')).
Proof.
  invert 2.
  invert H1.
  simp.

  invert H2.
  unfold split in H0; subst.
  rewrite lookup_join1 in H.
  unfold heap1 in H.
  simplify.
  invert H.
  exists (heap1 a v), x1; simp.
  eauto.
  unfold ptsto.
  eauto.
  unfold heap1; simplify.
  sets.

  invert H2.
  unfold split in H0; subst.
  rewrite lookup_join1 in H.
  unfold heap1 in H.
  simplify.
  invert H.
  exists (heap1 a v'), x1; simp.
  unfold split.
  maps_equal.
  rewrite lookup_join1.
  unfold heap1; simplify; auto.
  unfold heap1; simplify; sets.
  repeat rewrite lookup_join2; auto.
  unfold heap1; simplify; sets.
  unfold heap1; simplify; sets.
  unfold disjoint in *; simp.
  apply (H1 a0); eauto.
  cases (a ==n a0); simp.
  unfold heap1 in *; simplify; equality.
  unfold heap1 in *; simplify; equality.
  unfold ptsto.
  eauto.
  unfold heap1; simplify; sets.
Qed.

Lemma specialize_s_prop : forall (p : s_prop) h,
    p h
    -> (fun h' => h' = h) ===> p.
Proof.
  unfold s_imp; equality.
Qed.

Opaque s_eq s_imp lift star exis ptsto.

Lemma bigstar_impl : forall A ls (p q : nat -> A -> s_prop),
    (forall i x, p i x ===> q i x)
    -> bigstar p ls ===> bigstar q ls.
Proof.
  induct ls; simplify; auto.
  rewrite H.
  rewrite IHls.
  cancel.
  simp.
  eauto.
Qed.

Lemma guarded_impl : forall P Q p,
    (P <-> Q)
    -> (P ===> p) ===> (Q ===> p).
Proof.
  simp.
  excluded_middle P.
  repeat rewrite guarded_true by propositional.
  auto.
  repeat rewrite guarded_false by propositional.
  auto.
Qed.

Lemma lockChunks_lock' : forall l I linvs (f : nat -> nat) a,
    ~f a \in l
    -> nth_error linvs a = Some I
    -> (forall x y, f x = f y -> x = y)
    -> bigstar (fun i I => (~f i \in l) ===> I)%sep linvs ===> I * bigstar (fun i I => (~(f i \in {f a} \cup l)) ===> I)%sep linvs.
Proof.
  induct linvs; simplify.

  cases a; simplify; try unfold error in *; equality.

  cases a0; simplify.
  invert H0.
  rewrite guarded_true by sets.
  rewrite guarded_false by sets.
  cancel.
  apply bigstar_impl.
  simp.
  apply guarded_impl.
  sets.
  apply H1 in H2.
  equality.

  apply (IHlinvs (fun n => f (S n))) in H0; auto.
  rewrite H0.
  cancel.
  apply guarded_impl.
  sets.
  apply H1 in H3.
  equality.
  simp.
  apply H1 in H2.
  equality.
Qed.

Lemma lockChunks_lock : forall a l I linvs,
    ~a \in l
    -> nth_error linvs a = Some I
    -> lockChunks l linvs ===> I * lockChunks ({a} \cup l) linvs.
Proof.
  simp.
  apply lockChunks_lock' with (f := fun n => n); auto.
Qed.

Lemma lockChunks_unlock' : forall l I linvs (f : nat -> nat) a,
    f a \in l
    -> nth_error linvs a = Some I
    -> (forall x y, f x = f y -> x = y)
    -> I * bigstar (fun i I => (~f i \in l) ===> I)%sep linvs ===> bigstar (fun i I => (~(f i \in l \setminus {f a})) ===> I)%sep linvs.
Proof.
  induct linvs; simplify.

  cases a; simplify; try unfold error in *; equality.

  cases a0; simplify.
  invert H0.
  rewrite guarded_false by sets.
  rewrite guarded_true by sets.
  cancel.
  apply bigstar_impl.
  simp.
  apply guarded_impl.
  sets.
  apply H0; propositional.
  apply H1 in H4.
  equality.

  apply (IHlinvs (fun n => f (S n))) in H0; auto.
  rewrite <- H0.
  cancel.
  apply guarded_impl.
  sets.
  apply H2; propositional.
  apply H1 in H5.
  equality.
  simp.
  apply H1 in H2.
  equality.
Qed.

Lemma lockChunks_unlock : forall a l I linvs,
    a \in l
    -> nth_error linvs a = Some I
    -> I * lockChunks l linvs ===> lockChunks (l \setminus {a}) linvs.
Proof.
  simp.
  apply lockChunks_unlock' with (f := fun n => n); auto.
Qed.

Lemma preservation : forall linvs {result} (c : cmd result) h l c' h' l',
    step (h, l, c) (h', l', c')
    -> forall P Q R, hoare_triple linvs P c Q
                     -> (P * R * lockChunks l linvs)%sep h
                     -> exists P', hoare_triple linvs P' c' Q
                                   /\ (P' * R * lockChunks l' linvs)%sep h'.
Proof.
  induct 1; simplify.

  apply invert_Bind in H0; simp.
  eapply IHstep in H0; eauto.
  simp.
  eauto.
  
  apply invert_Bind in H; simp.
  specialize (invert_Return H); eauto using HtWeaken.

  apply invert_Loop in H; simp.
  eexists; simp.
  econstructor.
  eauto.
  simp.
  cases r.
  apply HtReturn'.
  auto.
  eapply HtStrengthen.
  eauto.
  eauto.
  eapply use_s_imp; try eassumption.
  rewrite H1.
  eauto.

  apply invert_Read in H0; simp.
  assert ((exists v, a |-> v * (x v * R * lockChunks l' linvs))%sep h').
  eapply use_s_imp; try eassumption.
  rewrite H0.
  cancel.
  eapply ptsto_out in H2; eauto.
  eexists; simp.
  apply HtReturn'.
  eauto.
  eapply use_s_imp; try eassumption.
  cancel.

  apply invert_Write in H0; simp.
  assert ((exists v, a |-> v * (x * R * lockChunks l' linvs))%sep h).
  eapply use_s_imp; try eassumption.
  rewrite H0.
  cancel.
  eapply ptsto_out in H2; eauto.
  propositional.
  eexists; simp.
  apply HtReturn'.
  eauto.
  eapply use_s_imp; try apply H5.
  cancel.

  apply invert_Alloc with (r := a) in H1.
  eexists; propositional.
  apply HtReturn'.
  eassumption.
  apply use_s_imp with ((P * R * lockChunks l' linvs) * a |--> zeroes numWords)%sep.
  cancel.
  apply use_s_imp with ((fun h' => h' = h) * a |--> zeroes numWords)%sep.
  cancel.
  eauto using specialize_s_prop.
  eapply use_s_imp.
  apply zeroes_initialize; auto.
  simp.

  apply invert_Free in H.
  eexists; propositional.
  instantiate (1 := Q tt).
  apply HtReturn'.
  auto.
  apply do_deallocate; simplify.
  change (fun f => (Q tt * lockChunks l' linvs) f)%sep with (Q tt * lockChunks l' linvs)%sep.
  eapply use_s_imp; try eassumption.
  rewrite H.
  cancel.

  apply invert_Lock in H0.
  simp.
  eexists; propositional.
  apply HtReturn'; auto.
  eapply use_s_imp; try eassumption.
  rewrite <- H3.
  cancel.
  apply lockChunks_lock; auto.

  apply invert_Unlock in H0.
  simp.
  eexists; propositional.
  apply HtReturn'; auto.
  eapply use_s_imp; try eassumption.
  rewrite H3.
  cancel.
  rewrite <- lockChunks_unlock; eauto.
  cancel.

  apply invert_Par in H0.
  simp.
  eapply IHstep in H2.
  simp.
  eexists; propositional.
  eapply HtStrengthen.
  econstructor.
  eassumption.
  eassumption.
  simp.
  cases r; auto.
  eapply use_s_imp; try eassumption.
  cancel.
  eapply use_s_imp; try eassumption.
  cancel.
  
  apply invert_Par in H0.
  simp.
  eapply IHstep in H0.
  simp.
  eexists; propositional.
  eapply HtStrengthen.
  econstructor.
  eassumption.
  eassumption.
  simp.
  cases r; auto.
  eapply use_s_imp; try eassumption.
  cancel.
  eapply use_s_imp; try eassumption.
  rewrite H3.
  cancel.
Qed.

Definition allLockChunks (linvs : list s_prop) := bigstar (fun _ I => I) linvs.

Lemma allLockChunks_lockChunks' : forall linvs (f : nat -> nat),
   bigstar (fun _ I => I) linvs ===> bigstar (fun i I => (~f i \in {}) ===> I) linvs.
Proof.
  induct linvs; simp; auto.

  rewrite guarded_true by sets.
  rewrite IHlinvs.
  cancel.
Qed.

Lemma allLockChunks_lockChunks : forall linvs,
    allLockChunks linvs ===> lockChunks {} linvs.
Proof.
  simp.
  apply allLockChunks_lockChunks' with (f := fun n => n).
Qed.

Lemma hoare_triple_sound' : forall linvs P {result} (c : cmd result) Q,
    hoare_triple linvs P c Q
    -> forall h, (P * allLockChunks linvs)%sep h
    -> invariantFor (trsys_of h {} c)
                    (fun p =>
                       let '(h, l, c) := p in
                       exists P', hoare_triple linvs P' c Q
                                  /\ (P' * lockChunks l linvs)%sep h).
Proof.
  simplify.

  apply invariant_induction; simplify.

  propositional; subst; simplify.
  eexists; propositional.
  eauto.
  eapply use_s_imp; try eassumption.
  rewrite allLockChunks_lockChunks.
  auto.

  cases s.
  cases p.
  cases s'.
  cases p.
  simp.
  eapply preservation with (R := emp%sep) in H1; eauto.
  simp.
  eexists; propositional; eauto.
  eapply use_s_imp; try eassumption.
  cancel.
  eapply use_s_imp; try eassumption.
  cancel.
Qed.

Fixpoint notAboutToFail {result} (c : cmd result) :=
  match c with
  | Fail _ => false
  | Bind _ _ c1 _ => notAboutToFail c1
  | Par c1 c2 => notAboutToFail c1 && notAboutToFail c2
  | _ => true
  end.

Lemma hoare_triple_notAboutToFail : forall linvs P result (c : cmd result) Q,
    hoare_triple linvs P c Q
    -> notAboutToFail c = false
    -> P ===> [| False |].
Proof.
  induct 1; simp; try equality; eauto using s_imp_trans.

  apply andb_false_iff in H1; propositional.
  rewrite H1; cancel.
  rewrite H1; cancel.

  rewrite H1; cancel.
Qed.

Lemma False_star : forall p,
    [| False |] * p ===> [| False |].
Proof.
  cancel.
Qed.

Theorem hoare_triple_sound : forall linvs P {result} (c : cmd result) Q,
    hoare_triple linvs P c Q
    -> forall h, (P * allLockChunks linvs)%sep h
    -> invariantFor (trsys_of h {} c)
                    (fun p => let '(_, _, c) := p in
                              notAboutToFail c = true).
Proof.
  simplify.

  eapply invariant_weaken.
  eapply hoare_triple_sound'; eauto.
  simp.
  cases s.
  cases p.
  simp.
  cases (notAboutToFail c0); auto.
  eapply hoare_triple_notAboutToFail in Heq; eauto.
  assert ([| False |]%sep f).
  apply use_s_imp with (x * lockChunks s linvs)%sep.
  rewrite Heq.
  apply False_star.
  assumption.
  invert H2; propositional.
Qed.
*)
