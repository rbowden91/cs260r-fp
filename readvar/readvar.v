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

Inductive value: Type := mkvalue (t: Type) (x : var t) (a : t): value.

Definition localenv := StringMap.t value.

Definition localenv_sound (env: localenv): Prop :=
   forall t name x a,
      x = mkvar t name ->
      StringMap.find name env = Some (mkvalue t x a).

Lemma foo t t':
   forall env name x a,
      t ->
      localenv_sound env ->
      x = mkvar t name ->
      StringMap.find name env = Some (mkvalue t' (mkvar t' name) a) -> t = t'.
Proof.
   intros.
   unfold localenv_sound in H.
   specialize H with (t := t) (name := name) (x := x) (a := X).
   apply H in H0.
   rewrite H0 in H1.
   congruence.
Admitted.

Definition launder (t1 t2: Type) (x : t1) (k: t2 = t1): t2.
Proof.
   rewrite <- k in x.
   auto.
Qed.

Definition read {t} {hint: t} (x: var t) (env: localenv) (P: localenv_sound env): option t.
destruct x.
refine (
        match StringMap.find name env with
        | Some (mkvalue t' (mkvar _ name') a) => Some (launder t' t a _)
        | None => None
        end
   
)
.
Proof.
apply (foo t t' env name (mkvar t name) a); auto.
Defined.
Check read.
