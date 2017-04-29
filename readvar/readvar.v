Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

Require Import OrderedType OrderedTypeEx.
(* ffs there is no standard instance for this *)
Require Import string_as_ot.

Require FMapList.
Require FMapFacts.
Module StringMap := FMapList.Make String_as_OT.
Module StringMapFacts := FMapFacts.WFacts_fun String_as_OT StringMap.


Inductive var (t: Type): Type := mkvar (name : string): var t.

Inductive value: Type := mkvalue (t: Type) (a : t): value.

Definition localenv := StringMap.t value.

Inductive program: Type :=
| Something: program
| UseVar: forall t, var t -> program
| Block: list program -> program
.
Inductive in_program: forall t, var t -> program -> Prop :=
| InProgVar: forall t name, in_program t (mkvar t name) (UseVar t (mkvar t name))
| InProgBlockConsEq: forall t v p ps, in_program t v p -> in_program t v (Block (p :: ps))
| InProgBlockConsNeq: forall t v p ps, in_program t v (Block ps) -> in_program t v (Block (p :: ps))
.

Definition localenv_sound (env: localenv) (prog : program): Prop :=
   forall t name, exists a,
      in_program t (mkvar t name) prog ->
       (StringMap.find name env = Some (mkvalue t a)).

Lemma localenv_weaken (env: localenv) (prog: program):
   forall (t : Type) name,
      localenv_sound env prog ->
      in_program t (mkvar t name) prog ->
      StringMap.find name env = None -> False.
Proof.
   intros.
   unfold localenv_sound in H.
   specialize H with (t := t) (name := name).
   destruct H as [a H].
   apply H in H0.
   rewrite H1 in H0.
   discriminate.
Qed.

Lemma localenv_weaken2 (env: localenv) (prog: program):
   forall (t : Type) name,
      localenv_sound env prog ->
      in_program t (mkvar t name) prog ->
      (forall t' a, StringMap.find name env = Some (mkvalue t' a) -> t' = t).
Proof.
   intros.
   unfold localenv_sound in H.
   specialize H with (t := t) (name := name).
   destruct H as [a' H].
   apply H in H0.
   rewrite H1 in H0.
   congruence.
Admitted.

Definition read {t} (x: var t)
                (env: localenv) (prog: program)
                (P: localenv_sound env prog)
                (P1: in_program t x prog)
           : option t.
Proof.
   destruct x.
   remember (StringMap.find name env) as Q.
   destruct Q.
   - destruct v.
     assert (t0 = t).
     * apply (localenv_weaken2 env prog)
          with (t := t) (name := name) (t' := t0) (a := a); auto.
     * clear HeqQ.
       rewrite H in a.
       refine (Some a).
   - symmetry in HeqQ.
     apply localenv_weaken with (t := t) (name := name) in P; auto.
     contradiction.
Defined.
Check read.

