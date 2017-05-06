Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

Require Import msl.eq_dec.
Import Relations.

Definition table A B := list (A*B).

Fixpoint table_get {A B}{H: EqDec A} (rho: table A B) (x: A) : option B :=
  match rho with
  | (y,v)::ys => if eq_dec x y then Some v else table_get ys x
  | nil => None
 end.

Definition table_set {A B}{H: EqDec A} (x: A) (v: B) (rho: table A B) : table A B := (x,v)::rho.

Lemma table_gss {A B}{H: EqDec A}: forall rho x (v : B), table_get (table_set x v rho) x = Some v.
Proof.
intros.
simpl. destruct (eq_dec x x); auto. contradiction n; auto.
Qed.

Lemma table_gso {A B}{H: EqDec A}: forall rho x y (v : B), x<>y -> table_get (table_set x v rho) y = table_get rho y.
Proof.
intros.
simpl. destruct (eq_dec y x); auto.  contradiction H0; auto.
Qed.


