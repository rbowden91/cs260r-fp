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
Require Import semantics.

Definition localenv_sound (env: Locals) (prog : Stmt): Prop :=
  forall t name,
    StmtVarRespectsT t name prog ->
    exists a, StringMap.find name env = Some (mkval t a).

Lemma localenv_weaken (env: Locals) (prog: Stmt):
   forall (t : Set) name,
      localenv_sound env prog ->
      StmtVarRespectsT t name prog ->
      StringMap.find name env = None -> False.
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
      (forall t' a, StringMap.find name env = Some (mkval t' a) -> t' = t).
Proof.
   intros.
   unfold localenv_sound in H.
   specialize H with (t := t) (name := name).
   specialize (H H0).
   destruct H as [a' H].
   rewrite H1 in H.
   injection H; auto.
Qed.


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
        rewrite StringMapFacts.add_eq_o; auto.
      * rewrite StringMapFacts.add_neq_o; auto.
    + intros; constructor.
  - split.
    + unfold localenv_sound in *.
      intros.
      specialize (H0 t name).
      inversion H0; subst.
      * exists a.
        rewrite StringMapFacts.add_eq_o; auto.
      * rewrite StringMapFacts.add_neq_o; auto.
    + intros; constructor.
  - split.
    + unfold localenv_sound in *.
      intros.
      specialize (H0 t name).
      inversion H0. (* XXX store also needs an invariant---load/store treated badly *)
    + intros.
      specialize (H0 t name).
      inversion H0.
  - split.
    + unfold localenv_sound.
      eauto.
    + intros.
      specialize (H0 t name).
      inversion H0; auto.
  - split.
    + unfold localenv_sound.
      eauto.
    + intros.
      specialize (H0 t name).
      inversion H0; auto.
  - split.
    + unfold localenv_sound.
      eauto.
    + intros.
      constructor.
      * specialize (H0 t name).
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