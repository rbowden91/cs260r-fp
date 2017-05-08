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

(* env is sound relative to tyenv *)
Definition localenv_sound (tyenv: VarMap type) (env: Locals): Prop :=
   forall t id,
      VarMapMapsTo (mkvar t id) t tyenv ->
      exists a, NatMap.MapsTo id a env /\ type_of_value a = t.

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

Lemma StmtStepsPreserves :
  forall tyenv h l s,
    VarsScopedStmt tyenv s ->
    localenv_sound tyenv l ->
    forall h' l' s',
       StmtSteps h l s h' l' s' ->
          VarsScopedStmt tyenv s' /\
          localenv_sound tyenv l'.
Proof.
  intros.
  revert H0 H. revert tyenv.
  induction H1; intros.
  - inversion H; subst.
    apply IHStmtSteps in H5; auto.
    destruct H5 as [H5a H5b].
    split; auto.
    apply vars_scoped_seq; auto.
  - inversion H; subst.
    split; auto.
  - split.
    { apply vars_scoped_skip. }
    inversion H1; subst.
    apply localenv_sound_replacement with (t := type); auto.
    apply expr_yields_typed_value with (tyenv := tyenv) (l := loc) (e := e); auto.
  - split.
    { apply vars_scoped_skip. }
    inversion H2; subst.
    apply localenv_sound_replacement with (t := type); auto.
    admit. (* currently don't have types from heap values *)
  - split.
    { apply vars_scoped_skip. }
    inversion H2; subst; auto.
  - inversion H1; subst.
    split; auto.
  - inversion H1; subst.
    split; auto.
  - inversion H1; subst.
    split; auto.
    apply vars_scoped_seq; auto.
  - inversion H1; subst.
    split; auto.
    apply vars_scoped_skip.
Admitted.

Definition ThreadStateSound tyenv t :=
   match t with
   | thread (stack_empty) => False
   | thread (stack_frame loc stk s) =>
        VarsScopedStmt tyenv s /\
        localenv_sound tyenv loc (* /\
        stack_sound tyenv stk *)
   end.

Lemma ThreadStepsPreserves:
   forall tyenv h t,
      ThreadStateSound tyenv t ->
      forall h' t',
         ThreadSteps h t h' t' ->
         ThreadStateSound tyenv t'.
Proof.
   intros.
   destruct H0.
   induction H0.
   - unfold ThreadStateSound in *.
     destruct H as [H1 H2].
     apply StmtStepsPreserves with
         (tyenv := tyenv)
            (h := h) (l := loc) (s := s)
            (h' := h') (l' := loc') (s' := s') in H0; auto.
   - (* call *)
     unfold ThreadStateSound in *.
     destruct H as [H1 H2].
     admit.
   - (* call #2 *)
     unfold ThreadStateSound in *.
     destruct H as [Ha Hb].
     admit.
   - (* return *)
     admit.
   - (* return #2 *)
     admit.
Admitted.

Lemma ThreadStepsStartPreserves:
   forall tyenv t,
      ThreadStateSound tyenv t ->
      forall t' tnew,
         ThreadStepsStart t t' tnew ->
         exists tyenvnew,
            ThreadStateSound tyenv t' /\
            ThreadStateSound tyenvnew tnew.
Proof.
   intros.
   admit.
Admitted.

Definition MachineEnv := nat. (* XXX *)
Definition MachineStateSound (menv: MachineEnv) (m: Machine) (menv2: MachineEnv) :=
   True. (* XXX *)

Lemma MachineStepsPreserves:
   forall menv menv2 m,
      MachineStateSound menv m menv2 ->
      forall m',
         MachineSteps m m' ->
         exists menv',
            MachineStateSound menv' m' menv2.
Proof.
Admitted.


Lemma ExprStepsProgress:
  forall t tyenv l e,
    VarsScopedExpr t tyenv e ->
    localenv_sound tyenv l ->
    exists a, ExprYields t l e a.
Proof.
   intros. revert H H0. revert tyenv l t.
   (*remember e as e1. revert Heqe1. revert e1.*)
   induction e; intros.
   - subst. exists v. inversion H; subst. apply value_yields.
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
   apply expr_yields_typed_value with (tyenv := tyenv) in H6; auto.
   destruct pred.
   1-2,4-5,8: unfold type_of_value in H6; discriminate.
   2,3: unfold type_of_value in H6; destruct a; discriminate.
   destruct b.
   * exists vt. apply cond_true_yields; auto.
   * exists vf. apply cond_false_yields; auto.
Qed.

Lemma StmtStepsProgress:
  forall tyenv h l s,
    VarsScopedStmt tyenv s ->
    localenv_sound tyenv l ->
    s <> s_skip ->
    (forall p arg, s = s_start p arg -> False) ->
    (forall x p e, s = s_call x p e -> False) ->
    (forall e, s = s_return e -> False) ->
    exists h' l' s',
       StmtSteps h l s h' l' s'.
Proof.
  intros tyenv h l s; revert tyenv h l.
  induction s; intros.
  - contradiction.
  - admit.
  - specialize (H2 p e). contradiction.
  - inversion H; subst.
    apply ExprStepsProgress with (l := l) in H8; auto.
    destruct H8 as [a H8].
    exists h, (NatMap.add id a l), s_skip.
    apply step_assign with (h := h) (loc := l) (id := id) (type := t) (e := e) (a := a).
    auto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Definition threadstmt_is (t: Thread) s0 :=
   match t with
   | thread (stack_empty) => False
   | thread (stack_frame loc stk s) => s = s0
   end.

Lemma ThreadStepsProgress:
   forall tyenv h t,
      ThreadStateSound tyenv t ->
      (forall p arg, threadstmt_is t (s_start p arg) = False) ->
      exists h' t',
         ThreadSteps h t h' t'.
Proof.
Admitted.

Lemma ThreadStepsStartProgress:
   forall tyenv t,
      ThreadStateSound tyenv t ->
      (exists p arg, threadstmt_is t (s_start p arg)) ->
      exists t' tnew,
         ThreadStepsStart t t' tnew.
Proof.
Admitted.

Lemma MachineStepsProgress:
   forall menv menv2 m,
      MachineStateSound menv m menv2 ->
      exists m',
         MachineSteps m m'.
Proof.
Admitted.

Theorem general_soundness_of_ast_and_semantics:
   forall menv menv2 m,
      MachineStateSound menv m menv2 ->
      (exists m',
         MachineSteps m m') /\
      (forall m',
         MachineSteps m m' ->
         exists menv',
            MachineStateSound menv' m' menv2).
Proof.
   intros.
   split.
   - apply MachineStepsProgress with (menv := menv) (menv2 := menv2).
     auto.
   - apply MachineStepsPreserves with (menv := menv).
     auto.
Qed.
