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

(* ffs there is no standard instance for this *)
Require Import string_as_ot.
Module StringMap := FMapList.Make String_as_OT.
Module StringMapFacts := FMapFacts.WFacts_fun String_as_OT StringMap.

Require Import ast.
Require Import varmap.
Require Import astprops.
Require Import semantics.

(* env is sound relative to tyenv *)
Definition localenv_sound_new (tyenv: VarMap type) (env: Locals): Prop :=
   forall t id,
      VarMapMapsTo (mkvar t id) t tyenv ->
      exists a, NatMap.MapsTo id (mkval t a) env /\ type_of_value a = t.

Definition localenv_sound (env: Locals) (prog : stmt): Prop :=
  forall t name,
    StmtVarRespectsT t name prog ->
    exists a, NatMap.find name env = Some (mkval t a).

Lemma localenv_weaken (env: Locals) (prog: stmt):
   forall (t : type) name,
      localenv_sound env prog ->
      StmtVarRespectsT t name prog ->
      NatMap.find name env = None -> False.
Proof.
   intros.
   unfold localenv_sound in H.
   specialize H with (t := t) (name := name).
   specialize (H H0).
   destruct H as [a H].
   rewrite H1 in H.
   discriminate.
Qed.

Lemma localenv_weaken2 (env: Locals) (prog: stmt):
   forall (t : type) name,
      localenv_sound env prog ->
      StmtVarRespectsT t name prog ->
      (forall t' a, NatMap.find name env = Some (mkval t' a) -> t' = t).
Proof.
   intros.
   unfold localenv_sound in H.
   specialize H with (t := t) (name := name).
   specialize (H H0).
   destruct H as [a' H].
   rewrite H1 in H.
   injection H; auto.
Qed.


(*
Lemma localenv_weaken_new (env: Locals) (prog: stmt):
   forall tyenv tyenv' name,
      localenv_sound_x env prog ->
      VarsScopedStmt tyenv prog tyenv' ->
      NatMap.find name env = None -> False.
Proof.
   intros.
   unfold localenv_sound_x in H.
   specialize H with (id := name) (tyenv := tyenv) (tyenv' := tyenv').
   specialize (H H0).
   destruct H as [a H].
   rewrite H1 in H.
   discriminate.
Qed.

Lemma localenv_weaken2_new (env: Locals) (prog: stmt):
   forall tyenv tyenv' name,
      localenv_sound_x env prog ->
      VarsScopedStmt tyenv prog tyenv' ->
      (forall t' a, NatMap.find name env = Some (mkval t' a) -> t' = t).
Proof.
   intros.
   unfold localenv_sound in H.
   specialize H with (t := t) (name := name).
   specialize (H H0).
   destruct H as [a' H].
   rewrite H1 in H.
   injection H; auto.
Qed.
*)

(* preservation *)
Lemma StmtStepsPreserves :
  forall h l s,
    localenv_sound l s ->
    (forall t name, StmtVarRespectsT t name s) ->
    forall h' l' s',
      StmtSteps h l s h' l' s' ->
      localenv_sound l' s' /\ (forall t name, StmtVarRespectsT t name s').
Proof.
  intros.
  induction H1.
  - split.
    + assert (localenv_sound loc' s1').
      {
        apply IHStmtSteps.
        * unfold localenv_sound.
          eauto.
        * intros.
          specialize (H0 t name).
          inversion H0; auto.
      }
      {
        unfold localenv_sound.
        intros.
        inversion H3; subst; clear H3.
        eauto.
      }
    + intros.
      constructor.
      {
        apply IHStmtSteps.
        * unfold localenv_sound.
          eauto.
        * intros.
          specialize (H0 t0 name0).
          inversion H0; auto.
      }
      {
        specialize (H0 t name).
        inversion H0; auto.
      }
  - split.
    + unfold localenv_sound.
      eauto.
    + intros.
      specialize (H0 t name).
      inversion H0; auto.
  - split.
    + unfold localenv_sound in *.
      intros.
      specialize (H0 t name).
      inversion H0; subst.
      * exists a.
        rewrite NatMapFacts.add_eq_o; auto.
      * rewrite NatMapFacts.add_neq_o; auto.
    + intros; constructor.
  - split.
    + unfold localenv_sound in *.
      intros.
      specialize (H0 t name).
      inversion H0; subst.
      * exists a.
        rewrite NatMapFacts.add_eq_o; auto.
      * rewrite NatMapFacts.add_neq_o; auto.
    + intros; constructor.
  - split.
    + unfold localenv_sound in *.
      intros.
      specialize (H0 t name).
      inversion H0. (* XXX store also needs an invariant---load/store treated badly *)
    + intros.
      specialize (H0 t name).
      inversion H0.
  - (* scope - not true yet *)
    admit.
  - split.
    + unfold localenv_sound.
      eauto.
    + constructor.
  - split.
    + unfold localenv_sound.
      eauto.
    + intros.
      specialize (H0 t name).
      inversion H0; subst.
      apply svrt_scope; auto.
  - split.
    + unfold localenv_sound.
      eauto.
    + intros.
      specialize (H0 t name).
      inversion H0; subst.
      apply svrt_scope; auto.
  - split.
    + unfold localenv_sound.
      eauto.
    + intros.
      constructor.
      * specialize (H0 t name).
        apply svrt_scope.
        inversion H0; auto.
      * auto.
  - split.
    + unfold localenv_sound.
      eauto.
    + intros.
      constructor.
  - admit. (* XXX local vars not yet handled by invariant *)
Admitted.


(* we are going to prove progress by induction on statements
   and will need to improve the induction principle *)


(* progress *)
Lemma StmtStepsProgress :
  forall h l s,
    localenv_sound l s ->
    (forall t name, StmtVarRespectsT t name s) ->
    s <> s_skip ->
    exists h' l' s',
      StmtSteps h l s h' l' s'.
Proof.
  intros.
Admitted.




Lemma localenv_sound_addition:
   forall tyenv loc t id a,
   type_of_value a = t ->
   localenv_sound_new tyenv loc ->
   ~(VarMapIn (mkvar t id) tyenv) ->
   localenv_sound_new
        (VarMap_add (mkvar t id) t tyenv)
        (NatMap.add id (mkval t a) loc).
Proof.
   unfold localenv_sound_new.
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
   localenv_sound_new tyenv loc ->
   VarMapMapsTo (mkvar t id) t tyenv ->
   localenv_sound_new tyenv (NatMap.add id (mkval t a) loc).
Proof.
   unfold localenv_sound_new.
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

(* XXX this should be put somewhere else *)
Lemma type_dec:
   forall (t1 t2: type),
   {t1 = t2} + {t1 <> t2}.
Proof.
   intro.
   induction t1; intros.
   1-3: destruct t2; subst; auto; right; discriminate.
   - induction t2; subst.
     1-3,5-7: right; discriminate.
     destruct IHt1_1 with (t2 := t2_1);
       destruct IHt1_2 with (t2 := t2_2);
       subst; auto; right; congruence.
   - induction t2; subst.
     1-4,6-7: right; discriminate.
     destruct IHt1 with (t2 := t2);
        subst; auto; right; congruence.
   - induction t2; subst.
     1-5,7: right; discriminate.
     destruct IHt1 with (t2 := t2);
        subst; auto; right; congruence.
   - induction t2; subst.
     1-6: right; discriminate.
     destruct IHt1 with (t2 := t2);
        subst; auto; right; congruence.
Qed.

(* XXX this too *)
Lemma expr_yields_typed_value:
   forall t tyenv e l a,
   VarsScopedExpr t tyenv e -> ExprYields t l e a ->
   type_of_value a = t.
Proof.
   intros; induction H0; inversion H; subst; auto.
Qed.


Lemma StmtStepsPreserves_new :
  forall tyenv tyenv2 h l s,
    VarsScopedStmt tyenv s tyenv2 ->
    localenv_sound_new tyenv l ->
    forall h' l' s',
      StmtSteps h l s h' l' s' ->
      exists tyenv',
        VarsScopedStmt tyenv' s' tyenv2 /\
        localenv_sound_new tyenv' l'.
Proof.
  intros.
  revert H0 H. revert tyenv tyenv2.
  induction H1; intros.
  - inversion H; subst.
    apply IHStmtSteps in H5; auto.
    destruct H5 as [tyenv' [H5a H5b]].
    exists tyenv'.
    split; auto.
    apply vars_scoped_block_cons with (env' := env'); auto.
  - inversion H; subst.
    exists env'.
    split; auto.
    assert (tyenv = env') by (inversion H4; auto).
    subst; auto.
  - exists tyenv2.
    split.
    { apply vars_scoped_block_nil. }
    inversion H1; subst.
    apply localenv_sound_replacement; auto.
    apply expr_yields_typed_value with (tyenv := tyenv2) (l := loc) (e := e); auto.
  - exists tyenv2.
    split.
    { apply vars_scoped_block_nil. }
    inversion H2; subst.
    apply localenv_sound_replacement; auto.
    admit. (* currently don't have types from heap values *)
  - exists tyenv2.
    split.
    { apply vars_scoped_block_nil. }
    inversion H2; subst; auto.
  - exists tyenv2.
    inversion H; subst.
    split; auto.
    admit. admit. (* XXX not true yet *)
  - exists tyenv2.
    inversion H; subst.
    split; auto.
    apply vars_scoped_block_nil.
  - exists tyenv2.
    inversion H1; subst.
    split; auto.
    apply vars_scoped_scope with (env' := env't).
    auto.
  - exists tyenv2.
    inversion H1; subst.
    split; auto.
    apply vars_scoped_scope with (env' := env'f).
    auto.
  - exists tyenv2.
    inversion H1; subst.
    split; auto.
    apply vars_scoped_block_cons with (env' := tyenv2).
    * apply vars_scoped_scope with (env' := env'body); auto.
    * auto.
  - exists tyenv2.
    inversion H1; subst.
    split; auto.
    apply vars_scoped_block_nil.
  - exists tyenv2.
    inversion H2; subst.
    split.
    * apply vars_scoped_block_nil.
    * apply localenv_sound_addition; auto.
Admitted.

Definition ThreadStateSound tyenv t tyenv2 :=
   match t with
   | thread loc stk s =>
        VarsScopedStmt tyenv s tyenv2 /\
        localenv_sound_new tyenv loc (* /\
        stack_sound tyenv stk *)
   end.

Lemma ThreadStepsPreserves_new:
   forall tyenv tyenv2 h t,
      ThreadStateSound tyenv t tyenv2 ->
      forall h' t',
         ThreadSteps h t h' t' ->
         exists tyenv',
            ThreadStateSound tyenv' t' tyenv2.
Proof.
   intros.
   induction H0.
   - unfold ThreadStateSound in *.
     destruct H as [H1 H2].
     apply StmtStepsPreserves_new with
         (h := h) (l := loc) (s := s) (h' := h') (l' := loc') (s' := s') in H1; auto.
   - (* call *)
     unfold ThreadStateSound in *.
     admit.
   - (* return *)
     admit.
Admitted.

Lemma ThreadStepsStartPreserves_new:
   forall tyenv tyenv2 t,
      ThreadStateSound tyenv t tyenv2 ->
      forall t' tnew,
         ThreadStepsStart t t' tnew ->
         exists tyenv' tyenvnew tyenv2new,
            ThreadStateSound tyenv' t' tyenv2 /\
            ThreadStateSound tyenvnew tnew tyenv2new.
Proof.
   intros.
   admit.
Admitted.

Definition MachineEnv := nat. (* XXX *)
Definition MachineStateSound (menv: MachineEnv) (m: Machine) (menv2: MachineEnv) :=
   True. (* XXX *)

Lemma MachineStepsPreserves_new:
   forall menv menv2 m,
      MachineStateSound menv m menv2 ->
      forall m',
         MachineSteps m m' ->
         exists menv',
            MachineStateSound menv' m' menv2.
Proof.
Admitted.


Lemma ExprStepsProgress_new:
  forall t tyenv l e,
    VarsScopedExpr t tyenv e ->
    localenv_sound_new tyenv l ->
    exists a, ExprYields t l e a.
Proof.
   intros. revert H H0. revert tyenv l t.
   (*remember e as e1. revert Heqe1. revert e1.*)
   induction e; intros.
   - subst. exists v. inversion H; subst. apply value_yields.
   - subst. inversion H; subst.
     unfold localenv_sound_new in H0.
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

Lemma StmtStepsProgress_new:
  forall tyenv tyenv2 h l s,
    VarsScopedStmt tyenv s tyenv2 ->
    localenv_sound_new tyenv l ->
    s <> s_skip ->
    (forall p arg, s = s_start p arg -> False) ->
    (forall x p e, s = s_call x p e -> False) ->
    (forall e, s = s_return e -> False) ->
    exists h' l' s',
      StmtSteps h l s h' l' s'.
Proof.
  intros tyenv tyenv2 h l s; revert tyenv tyenv2 h l.
  induction s; intros.
  - contradiction.
  - admit.
  - specialize (H2 p e). contradiction.
  - inversion H; subst.
    apply ExprStepsProgress_new with (l := l) in H8; auto.
    destruct H8 as [a H8].
    exists h, (NatMap.add id (mkval t a) l), s_skip.
    apply step_assign with (h := h) (loc := l) (id := id) (type := t) (e := e) (a := a).
    auto.
  - (* TBD *)
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Definition threadstmt (t: Thread) :=
   match t with
   | thread loc stk s => s
   end.

Lemma ThreadStepsProgress_new:
   forall tyenv tyenv2 h t,
      ThreadStateSound tyenv t tyenv2 ->
      (forall p arg, threadstmt t = s_start p arg -> False) ->
      exists h' t',
         ThreadSteps h t h' t'.
Proof.
Admitted.

Lemma ThreadStepsStartProgress_new:
   forall tyenv tyenv2 t,
      ThreadStateSound tyenv t tyenv2 ->
      (exists p arg, threadstmt t = s_start p arg) ->
      exists t' tnew,
         ThreadStepsStart t t' tnew.
Proof.
Admitted.

Lemma MachineStepsProgress_new:
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
   - apply MachineStepsProgress_new with (menv := menv) (menv2 := menv2).
     auto.
   - apply MachineStepsPreserves_new with (menv := menv).
     auto.
Qed.
