Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

Require Import OrderedType OrderedTypeEx.
Require FMapList.
Require FMapFacts.

(* ffs there is no standard instance for this *)
Require Import string_as_ot.

Require Import ast.

(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                            varmap                            *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

(*
 * This is not a Map but a wrapper around one. You can't make
 * an OrderedType instance for Var because Var carries a type
 * around with it.
 *)

Definition var_id {t} (x: Var t) :=
   match x with
   | var _ id => id
   end.

Module StringMap := FMapList.Make String_as_OT.
Module StringMapFacts := FMapFacts.WFacts_fun String_as_OT StringMap.
Module StringMapProperties := FMapFacts.WProperties_fun String_as_OT StringMap.

Definition StringMap_union {t} (m1 m2: StringMap.t t) :=
   StringMap.fold (@StringMap.add t) m2
      (StringMap.fold (@StringMap.add t) m1 (@StringMap.empty t)).

Lemma StringMap_union_correct:
   forall t (k: string) (m1 m2: StringMap.t t),
   (StringMap.In k m1 \/ StringMap.In k m2) <->
      StringMap.In k (StringMap_union m1 m2).
Proof.
Admitted.

Definition VarMap := StringMap.t.
Definition VarMap_empty := StringMap.empty.
Definition VarMap_add {t} {t2} (k: Var t) (v: t2) m := StringMap.add (var_id k) v m.
Definition VarMap_union {t} m1 m2 := @StringMap_union t m1 m2.
Definition VarMapDisjoint := StringMapProperties.Disjoint.
Definition VarMapIn {t} {t2} (k: Var t) (m: StringMap.t t2) :=
   StringMap.In (var_id k) m.

(*
Module NatMap := FMapList.Make Nat_as_OT.
Module NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.

Definition VarMap := NatMap.t.
Definition VarMap_empty := NatMap.empty.
Definition VarMap_add k v m := NatMap.add (var_id k) v m.
Definition VarMap_union m1 m2 := NatMap.union m1 m2.
Definition VarMapIn k m := NatMap.In (var_id k) m.
*)
