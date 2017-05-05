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

(* ffs there is no standard instance for this *)
Require Import string_as_ot.
Module StringMap := FMapList.Make String_as_OT.
Module StringMapFacts := FMapFacts.WFacts_fun String_as_OT StringMap.

Require Import ast.
Require Import varmap.
Require Import astprops.
Require Import semantics.

(* env is sound relative to tyenv *)
Definition localenv_sound_new (tyenv: VarMap Type) (env: Locals): Prop :=
   forall t id,
      VarMapMapsTo (mkvar t id) t tyenv ->
      exists a, NatMap.MapsTo id (mkval t a) env.

Definition localenv_sound (env: Locals) (prog : Stmt): Prop :=
  forall t name,
    StmtVarRespectsT t name prog ->
    exists a, NatMap.find name env = Some (mkval t a).

Lemma localenv_weaken (env: Locals) (prog: Stmt):
   forall (t : Set) name,
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

Lemma localenv_weaken2 (env: Locals) (prog: Stmt):
   forall (t : Set) name,
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
Lemma localenv_weaken_new (env: Locals) (prog: Stmt):
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

Lemma localenv_weaken2_new (env: Locals) (prog: Stmt):
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
    + assert (localenv_sound loc' s').
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
      * constructor; eauto.
        constructor.
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
    s <> skip ->
    exists h' l' s',
      StmtSteps h l s h' l' s'.
Proof.
  intros.
Admitted.




Lemma localenv_sound_addition:
   forall tyenv loc t id a,
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
     assert (t0 = t) by
        (unfold VarMapMapsTo in *;
         unfold VarMap_add in *;
         unfold var_id in *;
         rewrite varmap.NatMapFacts.add_mapsto_iff in H1;
         destruct H1 as [H1 | H1]; destruct H1;
         try contradiction; auto).
     subst.
     exists a.
     apply NatMap.add_1.
     auto.
   - unfold VarMapMapsTo in *.
     unfold VarMap_add in *.
     unfold var_id in *.
     rewrite varmap.NatMapFacts.add_neq_mapsto_iff in H1; auto.
     apply H in H1.
     destruct H1 as [a0 H1].
     exists a0.
     apply NatMap.add_2; auto.
Qed.

Lemma localenv_sound_replacement:
   forall tyenv loc t id a,
   localenv_sound_new tyenv loc ->
   VarMapMapsTo (mkvar t id) t tyenv ->
   localenv_sound_new tyenv (NatMap.add id (mkval t a) loc).
Proof.
   unfold localenv_sound_new.
   intros.
   destruct (Nat.eq_dec id0 id).
   - subst.
     assert (t0 = t) by
        (unfold VarMapMapsTo in *;
        unfold var_id in *;
        unfold VarMap in tyenv;
        apply varmap.NatMapFacts.MapsTo_fun with (m := tyenv) (x := id);
        auto).
     subst.
     specialize H with (t := t) (id := id).
     apply H in H0.
     destruct H0 as [a0 H0].
     exists a.
     apply NatMap.add_1.
     auto.
   - specialize H with (t := t0) (id := id0).
     apply H in H1.
     destruct H1 as [a0 H1].
     exists a0.
     apply NatMap.add_2; auto.
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
  - exists tyenv2.
    split.
    { apply vars_scoped_block_nil. }
    inversion H3; subst.
    apply localenv_sound_replacement; auto.
  - exists tyenv2.
    split.
    { apply vars_scoped_block_nil. }
    inversion H3; subst; auto.
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
    * apply vars_scoped_block_cons with (env' := tyenv2); auto.
      apply vars_scoped_block_nil.
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
   intros. revert H H0. revert tyenv l.
   remember e as e1. revert Heqe1. revert e1.
   induction e; intros.
   - subst. exists t0. apply value_yields.
   - subst. inversion H; subst.
     unfold localenv_sound_new in H0.
     apply H0 in H4.
     destruct H4 as [a H4].
     exists a.
     apply read_yields with (id := id); auto.
     apply NatMap.find_1.
     auto.
   - (* this is problematic *)
     admit.
Admitted.

Lemma StmtStepsProgress_new:
  forall tyenv tyenv2 h l s,
    VarsScopedStmt tyenv s tyenv2 ->
    localenv_sound_new tyenv l ->
    s <> skip ->
    (forall t p arg, s = start t p arg -> False) ->
    (forall pt rt x p e, s = call pt rt x p e -> False) ->
    (forall rt e, s = return_ rt e -> False) ->
    exists h' l' s',
      StmtSteps h l s h' l' s'.
Proof.
  intros tyenv tyenv2 h l s; revert tyenv tyenv2 h l.
  induction s; intros.
  - destruct l.
    * unfold skip; contradiction.
    * admit.
  - specialize (H2 pt p e). contradiction.
  - inversion H; subst.
    apply ExprStepsProgress_new with (l := l) in H10; auto.
    destruct H10 as [a H10].
    remember v as v1.
    destruct v1.
    exists h, (NatMap.add n (mkval t a) l), skip.
    apply step_assign with (h := h) (loc := l) (id := n) (type := t) (e := e) (a := a).
    assert (e1 = e) by admit.
    subst; auto.
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
      (forall ty p arg, threadstmt t = start ty p arg -> False) ->
      exists h' t',
         ThreadSteps h t h' t'.
Proof.
Admitted.

Lemma ThreadStepsStartProgress_new:
   forall tyenv tyenv2 t,
      ThreadStateSound tyenv t tyenv2 ->
      (exists ty p arg, threadstmt t = start ty p arg) ->
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
