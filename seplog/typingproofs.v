Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Require Import Program.
Import ListNotations.

Require Import OrderedType OrderedTypeEx.
Require FMapList.
Require FMapFacts.
Module NatMap := FMapList.Make Nat_as_OT.
Module NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.

Require Import ast.
Require Import varmap.
Require Import astfacts.
Require Import typing.
Require Import semantics.

(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                         typing proofs                        *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

(*
 * support logic
 *)

(*
 * property stating that a local variable environment is sound
 * relative to the typing environment
 *)
Definition localenv_sound (tyenv: VarMap type) (env: Locals): Prop :=
   forall t id,
      VarMapMapsTo (mkvar t id) t tyenv ->
      exists a, NatMap.MapsTo id a env /\ type_of_value a = t.

(*
 * adding a new variable to a localenv is sound given suitable conditions
 *)
Lemma localenv_sound_addition:
   forall tyenv loc t id a,
   type_of_value a = t ->
   localenv_sound tyenv loc ->
   ~(VarMapIn (mkvar t id) tyenv) ->
   localenv_sound
        (VarMap_add (mkvar t id) t tyenv)
        (NatMap.add id a loc).
Proof.
   unfold localenv_sound.
   intros.
   destruct (Nat.eq_dec id0 id).
   - subst.
     assert (type_of_value a = t0).
        (unfold VarMapMapsTo in *;
         unfold VarMap_add in *;
         unfold var_id in *;
         rewrite varmap.NatMapFacts.add_mapsto_iff in H2;
         destruct H2 as [H2 | H2]; destruct H2;
         try contradiction; auto).
     subst.
     exists a.
     split; auto.
     apply NatMap.add_1; auto.
   - unfold VarMapMapsTo in *.
     unfold VarMap_add in *.
     unfold var_id in *.
     rewrite varmap.NatMapFacts.add_neq_mapsto_iff in H2; auto.
     apply H0 in H2.
     destruct H2 as [a0 [H2a H2b]].
     exists a0.
     split; auto.
     apply NatMap.add_2; auto.
Qed.

(*
 * replacing a value in a localenv is sound given suitable conditions
 *)
Lemma localenv_sound_replacement:
   forall tyenv loc t id a,
   type_of_value a = t ->
   localenv_sound tyenv loc ->
   VarMapMapsTo (mkvar t id) t tyenv ->
   localenv_sound tyenv (NatMap.add id a loc).
Proof.
   unfold localenv_sound.
   intros.
   destruct (Nat.eq_dec id0 id).
   - subst.
     assert (type_of_value a = t0) by
        (unfold VarMapMapsTo in *;
        unfold var_id in *;
        unfold VarMap in tyenv;
        apply varmap.NatMapFacts.MapsTo_fun with (m := tyenv) (x := id);
        auto).
     subst.
     specialize H0 with (t := type_of_value a) (id := id).
     apply H0 in H1.
     destruct H1 as [a0 H1].
     exists a.
     split; auto.
     apply NatMap.add_1.
     auto.
   - specialize H0 with (t := t0) (id := id0).
     apply H0 in H2.
     destruct H2 as [a0 [H2a H2b]].
     exists a0.
     split; auto.
     apply NatMap.add_2; auto.
Qed.

(**************************************************************)
(* expressions *)

(*
 * preservation and progress for expressions:
 *    - expressions yield the right type
 *    - well-typed expressions always evaluate
 *)

Lemma ExprYieldsPreserves:
   forall t tyenv e l a,
   ExprTyped t tyenv e -> ExprYields t l e a ->
   type_of_value a = t.
Proof.
   intros; induction H0; inversion H; subst; auto.
Qed.

Lemma ExprYieldsProgress:
  forall t tyenv l e,
    ExprTyped t tyenv e ->
    localenv_sound tyenv l ->
    exists a, ExprYields t l e a.
Proof.
   intros. revert H H0. revert tyenv l t.
   (*remember e as e1. revert Heqe1. revert e1.*)
   induction e; intros.
   - subst. exists v. inversion H; subst. apply value_yields.
   - inversion H; subst.
     (* this got added at the last minute and I'm not sure how it's supposed to work *)
     admit.
   - subst. inversion H; subst.
     unfold localenv_sound in H0.
     apply H0 in H4.
     destruct H4 as [a [H4a H4b]].
     exists a.
     apply read_yields with (id := id); auto.
     all: apply NatMap.find_1.
     auto.
   - (*
      * This case seems to demand decidable equality on types. This failed badly
      * when we wanted to have arbitrary coq types in the AST. Now we have our
      * own notion of types and they're decidable.
      *
      * Update: dependent destruction fixes this too.
      *)
     inversion H.
(* no longer needed with the change away from explicitly typed exprs *)
(*
     (* make the existT rubbish go away *)
     apply Eqdep_dec.inj_pair2_eq_dec in H2; try apply type_dec.
     apply Eqdep_dec.inj_pair2_eq_dec in H3; try apply type_dec.
*)
     subst.
     remember H6 as H7; clear HeqH7.
     apply IHe1 with (l := l) in H6; auto.
     apply IHe2 with (l := l) in H8; auto.
     apply IHe3 with (l := l) in H9; auto.
     destruct H6 as [pred H6].
     destruct H8 as [vt H8].
     destruct H9 as [vf H9].
(* no longer needed either *)
(*
     (*
      * now we have a fatal problem where extracting the bool from inside the
      * value t_bool loses the connection between the bool and the value, so
      * destructing the bool leaves you stuck. aha: "dependent destruction"
      * fixes this. (note later: also see "dependent rewrite".
      *)
     dependent destruction pred.
     destruct b;
        [exists vt; apply cond_true_yields | exists vf; apply cond_false_yields];
        auto.
*)
     remember H6 as H6a. clear HeqH6a.
     apply ExprYieldsPreserves with (tyenv := tyenv) in H6; auto.
     destruct pred.
     1-2,4-5,8: unfold type_of_value in H6; discriminate.
     2,3: unfold type_of_value in H6; destruct a; discriminate.
     destruct b.
     * exists vt. apply cond_true_yields; auto.
     * exists vf. apply cond_false_yields; auto.
  - inversion H; subst.
    apply IHe1 with (l := l) in H5; auto.
    apply IHe2 with (l := l) in H7; auto.
    destruct H5 as [a1 H5].
    destruct H7 as [a2 H7].
    inversion H; subst.
    assert (type_of_value a1 = t_nat) by
       (apply ExprYieldsPreserves with (tyenv := tyenv) in H5; auto).
    assert (type_of_value a2 = t_nat) by
       (apply ExprYieldsPreserves with (tyenv := tyenv) in H7; auto).
    destruct a1; simpl in H1; try discriminate.
    destruct a2; simpl in H2; try discriminate.
    exists (v_nat (n n0 n1)).
    apply natbinop_yields; auto.
    all: destruct a; discriminate.
Admitted.

(**************************************************************)
(* statements *)

(*
 * preservation for statements
 *)

Lemma StmtStepsPreserves :
  forall tyenv h l s,
    StmtTyped tyenv s ->
    localenv_sound tyenv l ->
    forall h' l' s',
       StmtSteps h l s h' l' s' ->
          StmtTyped tyenv s' /\
          localenv_sound tyenv l'.
Proof.
  intros.
  revert H0 H. revert tyenv.
  induction H1; intros.
  - inversion H; subst.
    apply IHStmtSteps in H5; auto.
    destruct H5 as [H5a H5b].
    split; auto.
    apply s_seq_typed; auto.
  - inversion H; subst.
    split; auto.
  - split.
    { apply s_skip_typed. }
    inversion H1; subst.
    apply localenv_sound_replacement with (t := type); auto.
    apply ExprYieldsPreserves with (tyenv := tyenv) (l := loc) (e := e); auto.
  - split.
    { apply s_skip_typed. }
    inversion H2; subst.
    apply localenv_sound_replacement with (t := t); auto.
    admit. (* currently don't have types from heap values *)
  - split.
    { apply s_skip_typed. }
    inversion H2; subst; auto.
  - inversion H1; subst.
    split; auto.
  - inversion H1; subst.
    split; auto.
  - inversion H1; subst.
    split; auto.
    apply s_seq_typed; auto.
  - inversion H1; subst.
    split; auto.
    apply s_skip_typed.
(* holdup: we don't currently have typing for heap values *)
Admitted.

(*
 * progress for statements
 *
 * this has to be one lemma per statement type, because some are handled at
 * higher levels and the induction on s_seq blows up horribly if you try it
 * at this level.
 *)

(* s_skip doesn't step *)

(* this one doesn't even require type soundness or anything else... *)
Lemma StmtStepsProgress_seq_skip:
   forall h l s,
     StmtSteps h l (s_seq s_skip s) h l s.
Proof.
   apply step_next.
Qed.

(* anything else in s_seq needs to be handled at a higher level *)

(* s_start happens at a higher level *)

(* s_assign *)
Lemma StmtStepsProgress_assign:
   forall tyenv h l x e,
      StmtTyped tyenv (s_assign x e) ->
      localenv_sound tyenv l ->
      exists h' l',
         StmtSteps h l (s_assign x e) h' l' (s_skip).
Proof.
   intros.
   inversion H; subst.
   apply ExprYieldsProgress with (l := l) in H4; auto.
   destruct H4 as [a H4].
   exists h, (NatMap.add id a l).
   apply step_assign with (h := h) (loc := l) (id := id) (type := t) (e := e) (a := a).
   auto.
Qed.

(* s_load *)
Lemma StmtStepsProgress_load:
   forall tyenv h l x e,
      StmtTyped tyenv (s_load x e) ->
      localenv_sound tyenv l ->
      exists h' l',
         StmtSteps h l (s_load x e) h' l' (s_skip).
Proof.
   intros.
   inversion H; subst.

   (* this should be an ltac *)
   assert (exists addr: value, ExprYields (t_addr t) l e addr) as Haddr by
      (apply ExprYieldsProgress with (l := l) in H4; auto).
   destruct Haddr as [addr Haddr].
   assert (type_of_value addr = t_addr t) by 
      (apply ExprYieldsPreserves with (l := l) (a := addr) in H4; auto).
   destruct addr; simpl in H1; try discriminate.
   - destruct a as [t'a heapaddr whichheap].
     assert (t'a = t) by congruence; subst.
     (* don't have typing for heap values yet *)
     assert (exists a, heap_get_data whichheap heapaddr h = Some a) as Ha by admit.
     destruct Ha as [a Ha].
     exists h, (NatMap.add id a l).
     apply step_load with (heapaddr := heapaddr) (whichheap := whichheap); auto.
   - destruct a; discriminate.
(* holdup: we don't have heap types *)
Admitted.

(* s_store *)
Lemma StmtStepsProgress_store:
   forall tyenv h l x e,
      StmtTyped tyenv (s_store x e) ->
      localenv_sound tyenv l ->
      exists h' l',
         StmtSteps h l (s_store x e) h' l' (s_skip).
Proof.
   intros.
   inversion H; subst.
   unfold localenv_sound in H0.
   apply H0 in H4.
   destruct H4 as [addr [H4a H4b]].
   destruct addr; simpl in H4b; try discriminate.
   destruct a as [t'addr hid whichheap].

   (* this should be an ltac *)
   assert (exists a: value, ExprYields t l e a) as Ha by
      (apply ExprYieldsProgress with (l := l) in H5; auto).
   destruct Ha as [a Ha].
   assert (type_of_value a = t) by 
      (apply ExprYieldsPreserves with (l := l) (a := a) in H5; auto).

   - exists (heap_set_data whichheap hid a h), l.
     apply step_store; auto.
     apply read_yields with (id := lid); auto.
     apply NatMap.find_1.
     assert (t'addr = t) by congruence; subst.
     auto.
   - destruct a; discriminate.
Qed.

(* s_if *)
Lemma StmtStepsProgress_if:
   forall tyenv h l p st sf,
      StmtTyped tyenv (s_if p st sf) ->
      localenv_sound tyenv l ->
      exists h' l' s',
         StmtSteps h l (s_if p st sf) h' l' s'.
Proof.
   intros.
   inversion H; subst.

   (* this should be an ltac *)
   assert (exists pred: value, ExprYields t_bool l p pred) as Hpred by
      (apply ExprYieldsProgress with (l := l) in H5; auto).
   destruct Hpred as [pred Hpred].
   assert (type_of_value pred = t_bool) as Htpred by
      (apply ExprYieldsPreserves with (l := l) (a := pred) in H5; auto).
   destruct pred; simpl in Htpred; try discriminate.

   - (* the real case *)
     destruct b.
     * exists h, l, st. apply step_if_true. auto.
     * exists h, l, sf. apply step_if_false. auto.
   - (* these are bogus *)
     destruct a; discriminate.
   - destruct a; discriminate.
Qed.

(* s_while *)
Lemma StmtStepsProgress_while:
   forall tyenv h l e s,
      StmtTyped tyenv (s_while e s) ->
      localenv_sound tyenv l ->
      exists h' l' s',
         StmtSteps h l (s_while e s) h' l' s'.
Proof.
   intros.
   inversion H; subst.

   (* this should be an ltac *)
   assert (exists pred: value, ExprYields t_bool l e pred) as Hpred by
      (apply ExprYieldsProgress with (l := l) in H4; auto).
   destruct Hpred as [pred Hpred].
   assert (type_of_value pred = t_bool) as Htpred by
      (apply ExprYieldsPreserves with (l := l) (a := pred) in H4; auto).
   destruct pred; simpl in Htpred; try discriminate.

   - (* the real case *)
     destruct b.
     * exists h, l, (s_seq s (s_while e s)). apply step_while_true. auto.
     * exists h, l, s_skip. apply step_while_false. auto.
   - (* these are bogus *)
     destruct a; discriminate.
   - destruct a; discriminate.
Qed.

(* s_call happens at a higher level *)

(* s_return happens at a higher level *)

(* s_getlock *)
Lemma StmtStepsProgress_getlock:
   forall tyenv h l x,
      StmtTyped tyenv (s_getlock x) ->
      localenv_sound tyenv l ->
      exists h' l',
         StmtSteps h l (s_getlock x) h' l' (s_skip).
Proof.
   intros.
   inversion H; subst.
   unfold localenv_sound in H0.
   apply H0 in H3.
   destruct H3 as [a [H3a H3b]].
   destruct a; simpl in H3b; try discriminate.
   - destruct a; discriminate.
   - destruct a as [t'a heapaddr whichheap].
     exists (heap_set_lockstate heapaddr LockHeld h), l.
     apply step_getlock.
     * apply NatMap.find_1.
       assert (t'a = t) by congruence; subst.
       (*
        * This doesn't come out because constructing lock values with
        * other whichheap values is structurally possible, and the amount
        * of machinery required to rule out invalid values everywhere is
        * large and prohibitive. The right solution is to rearrange the
        * lock values to get rid of the whichheap component. (Also, the
        * separate layer of the "addr" type should go away; it complicates
        * all the proofs for no clear benefit. But I don't want to do that
        * at this stage because it might blow up the logic. (XXX)
        *)
       assert (whichheap = MemoryHeap) by admit; subst.
       auto.
     * (*
        * this case is to show that the lock is available, which we can't
        * show in general unless we go and prove that the code is deadlock-free.
        *)
       admit.
Admitted.

(* s_putlock *)
Lemma StmtStepsProgress_putlock:
   forall tyenv h l x,
      StmtTyped tyenv (s_putlock x) ->
      localenv_sound tyenv l ->
      exists h' l',
         StmtSteps h l (s_putlock x) h' l' (s_skip).
Proof.
   intros.
   inversion H; subst.
   unfold localenv_sound in H0.
   apply H0 in H3.
   destruct H3 as [a [H3a H3b]].
   destruct a; simpl in H3b; try discriminate.
   - destruct a; discriminate.
   - destruct a as [t'a heapaddr whichheap].
     exists (heap_set_lockstate heapaddr LockAvailable h), l.
     apply step_putlock.
     * apply NatMap.find_1.
       assert (t'a = t) by congruence; subst.
       (* see above *)
       assert (whichheap = MemoryHeap) by admit; subst.
       auto.
     * (* here we have to prove that we hold the lock. the logic does that but we don't *)
       admit.
Admitted.

(**************************************************************)
(* stacks *)

Inductive StackSound tyenv: Stack -> Prop :=
| stack_sound_base:
     forall loc s,
     StmtTyped tyenv s -> localenv_sound tyenv loc ->
     StackSound tyenv (stack_frame loc stack_empty s)
| stack_sound_inner:
     forall loc s stk',
     StackSound tyenv stk' ->
     StmtTyped tyenv s -> localenv_sound tyenv loc ->
     StackSound tyenv (stack_frame loc stk' s)
.

(*
 * preservation for stacks
 *)

Lemma StackStepsPreserves:
   forall tyenv h stk,
   StackSound tyenv stk ->
   forall h' stk',
      StackSteps h stk h' stk' ->
      StackSound tyenv stk'.
Proof.
   intros.
   induction H0.
   - (* statement level cases *)
     inversion H; subst; [apply stack_sound_base | apply stack_sound_inner];
        apply StmtStepsPreserves with (tyenv := tyenv) in H0; auto.
     (* rolling this into the previous doesn't work tidily *)
     all: destruct H0; auto.
   - (* tail call *)
     inversion H; subst; [apply stack_sound_base | apply stack_sound_inner]; auto.
     all: apply s_seq_typed; auto; apply s_skip_typed.
   - (* general call *)
     apply stack_sound_inner.
     * (* show that the updated caller frame is sound *)
       inversion H; subst; [apply stack_sound_base | apply stack_sound_inner]; auto.
       + inversion H6; subst.
         apply s_seq_typed; auto.
         apply s_assign_typed.
         -- (* note: v_undef should have type forall t, t; it's actually t_unit *)
            (* (that's not good enough here) *)
            apply e_value_typed; simpl.
            admit.
         -- inversion H5; subst; auto.
       + inversion H8; subst.
         apply s_seq_typed; auto.
         apply s_assign_typed.
         -- (* ditto *)
            apply e_value_typed; simpl.
            admit.
         -- inversion H5; subst; auto.
     * (* show that the callee's body is well typed *)
       (* XXX except that it's supposed to be wrt the caller's type environment. bogus *)
(*
       inversion H; subst.
       inversion H6; subst.
       inversion H5; subst.
       inversion H10; subst.
       auto.
*)
       admit.
     * (* show that the new local environment is sound *)
       (* this requires VardeclsStepsPreserves *)
       admit.
    - (* return followed by crap *)
      inversion H; subst; [apply stack_sound_base | apply stack_sound_inner]; auto.
      * inversion H2; subst; auto.
      * inversion H4; subst; auto.
    - (* general return *)
      inversion H; subst.
      inversion H6; subst;
         apply stack_sound_inner; auto.
      * (*
         * this wants us to prove that an empty stack is sound, which it isn't;
         * this is because we don't have anything that prohibits that, and more
         * specifically, we don't have a way to know that the initial frame
         * consists of a call followed by skip such that it ultimately steps to
         * StackDone.
         *)
        admit.
      * (* Show that the residual assignment of the return value is typed. *)
        destruct x.
        (* currently we don't enforce return types properly *)
        assert (ExprTyped rt tyenv ret) by admit.
        assert (t = rt) by admit; subst.
        apply s_assign_typed.
        + apply e_value_typed.
          apply ExprYieldsPreserves with (tyenv := tyenv) in H0; auto.
        + inversion H3; subst; auto.
      * (* carbon copy of previous case for different stack configuration *)
        destruct x.
        (* currently we don't enforce return types properly *)
        assert (ExprTyped rt tyenv ret) by admit.
        assert (t = rt) by admit; subst.
        apply s_assign_typed.
        + apply e_value_typed.
          apply ExprYieldsPreserves with (tyenv := tyenv) in H0; auto.
        + inversion H5; subst; auto.
Admitted.

Lemma StackStepsStartPreserves:
   forall tyenv stk,
   StackSound tyenv stk ->
   forall stk' stk2,
      StackStepsStart stk stk' stk2 ->
      exists tyenv2,
         StackSound tyenv stk' /\
         StackSound tyenv2 stk2.
Proof.
   (* not yet... *)
Admitted.

(*
 * progress for stacks
 *)

Lemma StackStepsProgress_seq_sublemma:
   forall tyenv h loc stk0 s1 s2,
   StmtTyped tyenv s1 ->
   localenv_sound tyenv loc ->
   (exists h' stk', StackSteps h (stack_frame loc stk0 s1) h' stk') ->
   exists h' stk',
      StackSteps h (stack_frame loc stk0 (s_seq s1 s2)) h' stk'.
Proof.
   intros.
   destruct H1 as [h' [stk' H1]].
   destruct stk'; inversion H1; subst.
   - (* stmt case *)
     exists h', (stack_frame l stk' (s_seq s s2)).
     apply stack_steps_stmt.
     apply step_in_seq.
     auto.
   - (* tail call *)
     (* XXX do this *)
     admit.
   - (* full call *)
     (* XXX do this *)
     admit.
   - (* return followed by crap (inside a seq) *)
     (* XXX this case doesn't work *) 
     admit.
   - (* return *)
     exists h', (stack_frame loc (stack_frame l stk' (s_assign x ejunk)) (s_return ret)).
     apply stack_steps_return_seq.
Admitted.

Lemma StackStepsProgress:
   forall tyenv h stk,
   StackSound tyenv stk ->
   ~(StackDone stk) ->
   (exists h' stk',
      StackSteps h stk h' stk') \/
   (exists stk' stk2,
      StackStepsStart stk stk' stk2).
Proof.
   intros.
   (* this has too damn many cases, need to figure out how to clean it up *)
   destruct H; [revert H H0 H1 | revert H H0 H1 H2].
   all: revert loc h tyenv.
   all: induction s; intros.
   (* bottom of stack cases *)
   - (* skip *)
     contradict H0. apply stack_done.
   - (* seq *)
     inversion H; subst.
     destruct s1.
     (* get the skip case, which is different *)
     Focus 1.
        left.
        exists h, (stack_frame loc stack_empty s2); apply stack_steps_stmt; apply step_next.
     (* get the start case, which is different *)
     Focus 2.
        apply IHs1 with (h := h) in H1; auto; [ | contradict H0; inversion H0 ].
        destruct H1.
        destruct H1 as [h' [stk' H1]]; inversion H1; inversion H10; subst; discriminate.
        destruct H1 as [stk' [stk2 H1]]. right; exists stk', stk2.
        (* XXX this case doesn't work (start inside a seq) *)
        admit.
     (* the rest of the cases are the same *)
     all: left.
     all: apply StackStepsProgress_seq_sublemma with (tyenv := tyenv); auto.
     all: apply IHs1 with (h := h) in H1; auto.
     2,4,6,8,10,12,14,16,18,20: contradict H0; inversion H0.
     all: destruct H1; auto; destruct H1 as [stk' [stk2 H1]]; inversion H1; subst.
   - (* start *)
     right; inversion H; subst.
     (* haven't done this yet *)
     admit.
   - (* assign *)
     left; inversion H; subst.
     apply StmtStepsProgress_assign with (h := h) (l := loc) in H; auto.
     destruct H as [h' [l' H]].
     exists h', (stack_frame l' stack_empty s_skip).
     apply stack_steps_stmt; auto.
   - (* load *)
     left; inversion H; subst.
     apply StmtStepsProgress_load with (h := h) (l := loc) in H; auto.
     destruct H as [h' [l' H]].
     exists h', (stack_frame l' stack_empty s_skip).
     apply stack_steps_stmt; auto.
   - (* store *)
     left; inversion H; subst.
     apply StmtStepsProgress_store with (h := h) (l := loc) in H; auto.
     destruct H as [h' [l' H]].
     exists h', (stack_frame l' stack_empty s_skip).
     apply stack_steps_stmt; auto.
   - (* if *)
     left; inversion H; subst.
     apply StmtStepsProgress_if with (h := h) (l := loc) in H; auto.
     destruct H as [h' [l' [s' H]]].
     exists h', (stack_frame l' stack_empty s').
     apply stack_steps_stmt; auto.
   - (* while *)
     left; inversion H; subst.
     apply StmtStepsProgress_while with (h := h) (l := loc) in H; auto.
     destruct H as [h' [l' [s' H]]].
     exists h', (stack_frame l' stack_empty s').
     apply stack_steps_stmt; auto.
   - (* call *)
     left; inversion H; subst.
     (* haven't done this yet *)
     admit.
   - (* return *)
     left; inversion H; subst.
     (* this case is illegal but we don't know how to rule it out yet (see above) *)
     admit.
   - (* getlock *)
     left; inversion H; subst.
     apply StmtStepsProgress_getlock with (h := h) (l := loc) in H; auto.
     destruct H as [h' [l' H]].
     exists h', (stack_frame l' stack_empty s_skip).
     apply stack_steps_stmt; auto.
   - (* putlock *)
     left; inversion H; subst.
     apply StmtStepsProgress_putlock with (h := h) (l := loc) in H; auto.
     destruct H as [h' [l' H]].
     exists h', (stack_frame l' stack_empty s_skip).
     apply stack_steps_stmt; auto.
   (* now come the mostly duplicate not-bottom-of-stack cases *)
   - (* skip at end of procedure missing its return *)
     (* illegal but not yet ruled out *)
     admit.
   - (* seq *)
     (* this is ultimately identical to the mess above *)
     admit.
   - (* start *)
     right; inversion H1; subst.
     (* haven't done this yet *)
     admit.
   - (* assign *)
     left; inversion H1; subst.
     apply StmtStepsProgress_assign with (h := h) (l := loc) in H1; auto.
     destruct H1 as [h' [l' H1]].
     exists h', (stack_frame l' stk' s_skip).
     apply stack_steps_stmt; auto.
   - (* load *)
     left; inversion H1; subst.
     apply StmtStepsProgress_load with (h := h) (l := loc) in H1; auto.
     destruct H1 as [h' [l' H1]].
     exists h', (stack_frame l' stk' s_skip).
     apply stack_steps_stmt; auto.
   - (* store *)
     left; inversion H1; subst.
     apply StmtStepsProgress_store with (h := h) (l := loc) in H1; auto.
     destruct H1 as [h' [l' H1]].
     exists h', (stack_frame l' stk' s_skip).
     apply stack_steps_stmt; auto.
   - (* if *)
     left; inversion H1; subst.
     apply StmtStepsProgress_if with (h := h) (l := loc) in H1; auto.
     destruct H1 as [h' [l' [s' H1]]].
     exists h', (stack_frame l' stk' s').
     apply stack_steps_stmt; auto.
   - (* while *)
     left; inversion H1; subst.
     apply StmtStepsProgress_while with (h := h) (l := loc) in H1; auto.
     destruct H1 as [h' [l' [s' H1]]].
     exists h', (stack_frame l' stk' s').
     apply stack_steps_stmt; auto.
   - (* call *)
     left; inversion H1; subst.
     (* haven't done this yet *)
     admit.
   - (* return *)
     left; inversion H1; subst.
     (* haven't done this yet *)
     admit.
   - (* getlock *)
     left; inversion H1; subst.
     apply StmtStepsProgress_getlock with (h := h) (l := loc) in H1; auto.
     destruct H1 as [h' [l' H1]].
     exists h', (stack_frame l' stk' s_skip).
     apply stack_steps_stmt; auto.
   - (* putlock *)
     left; inversion H1; subst.
     apply StmtStepsProgress_putlock with (h := h) (l := loc) in H1; auto.
     destruct H1 as [h' [l' H1]].
     exists h', (stack_frame l' stk' s_skip).
     apply stack_steps_stmt; auto.
Admitted.

(**************************************************************)
(* threads *)

Definition ThreadSound tyenv t :=
   match t with
   | thread stk => StackSound tyenv stk
   end.

(*
 * preservation for threads
 *)

Lemma ThreadStepsPreserves:
   forall tyenv h t,
      ThreadSound tyenv t ->
      forall h' t',
         ThreadSteps h t h' t' ->
         ThreadSound tyenv t'.
Proof.
   unfold ThreadSound.
   destruct t.
   destruct t'.
   intros.
   inversion H0; subst.
   apply StackStepsPreserves with (h := h) (stk := s) (h' := h'); auto.
Qed.

Lemma ThreadStepsStartPreserves:
   forall tyenv t,
      ThreadSound tyenv t ->
      forall t' tnew,
         ThreadStepsStart t t' tnew ->
         exists tyenvnew,
            ThreadSound tyenv t' /\
            ThreadSound tyenvnew tnew.
Proof.
   unfold ThreadSound.
   destruct t.
   destruct t'.
   intros.
   inversion H0; subst.
   apply StackStepsStartPreserves with (tyenv := tyenv) in H3; auto.
Qed.

(*
 * progress for threads
 *)

Definition threadstmt_is (t: Thread) s0 :=
   match t with
   | thread (stack_empty) => False
   | thread (stack_frame loc stk s) => s = s0
   end.

Lemma ThreadStepsProgress:
   forall tyenv h t,
      ThreadSound tyenv t ->
      ~(ThreadDone t) ->
      (exists h' t',
         ThreadSteps h t h' t') \/
      (exists t' t2,
         ThreadStepsStart t t' t2).
Proof.
   unfold ThreadSound.
   destruct t.
   intros.
   apply StackStepsProgress with (h := h) in H.
   destruct H.
   - left.
     destruct H as [h' [stk' H]].
     exists h', (thread stk').
     apply thread_steps; auto.
   - right.
     destruct H as [stk' [stk2 H]].
     exists (thread stk'), (thread stk2).
     apply thread_steps_start; auto.
   - contradict H0.
     apply thread_done; auto.
Qed.

(**************************************************************)
(* machine *)

Definition MachineSound (m: Machine) :=
   match m with
   | machine h ts => 
        (* XXX XXX XXX this is no good, each thread needs its own tyenv *)
        forall tyenv t, In t ts -> ThreadSound tyenv t
   end.

(*
 * preservation for machines
 *)

Lemma MachineStepsPreserves:
   forall m,
      MachineSound m ->
      forall m',
         MachineSteps m m' ->
         MachineSound m'.
Proof.
   intros.
   inversion H0; subst.
   - admit.
   - admit.
   - admit.
Admitted.

(*
 * progress for machines
 *)

Lemma MachineStepsProgress:
   forall m,
      MachineSound m ->
      exists m',
         MachineSteps m m'.
Proof.
Admitted.

(**************************************************************)
(* top level *)

Theorem general_type_soundness_of_ast_and_semantics:
   forall m,
      MachineSound m ->
      (exists m',
         MachineSteps m m') /\
      (forall m',
         MachineSteps m m' ->
         MachineSound m').
Proof.
   intros.
   split.
   - apply MachineStepsProgress.
     auto.
   - apply MachineStepsPreserves.
     auto.
Qed.
