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
Require Import typing.
Require Import semantics.

(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                        facts about ast                       *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

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

