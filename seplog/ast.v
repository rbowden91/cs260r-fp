Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

Require Import msl.eq_dec.
Import Relations.

(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                             ast                              *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

(*
 * abstract syntax the code is written in
 *)

Inductive type :=
| t_nat
| t_bool
| t_lock : type -> type
.

Definition var := (nat * type)%type.

(* nat gives the number of elements of type |type| *)
Definition lock := (nat * bool * type)%type.

Inductive value : Type :=
| v_nat (n:nat)
| v_bool (b:bool)
| v_lock (l:lock)
| v_undef
.




Instance EqDec_var : EqDec (var) := _.
Proof.
Admitted.


Instance EqDec_lock : EqDec (lock) := _.
Proof.
Admitted.

Inductive invariant : Type :=
(* Just an example *)
| nat_inv : invariant
.




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


Definition env := table var value.
Definition state := table lock value.

(*
 * expressions produce values
 *)
Inductive expr: Type :=
| e_value: value -> expr
| e_read: var -> expr
| e_cond: expr -> expr -> expr -> expr
.

(*
 * statements don't
 *)
Inductive stmt: Type :=
| s_skip : stmt
| s_seq: stmt -> stmt -> stmt
| s_start: proc -> expr -> stmt
| s_assign: var -> expr -> stmt
| s_load: var -> lock -> stmt
| s_store: lock -> expr -> stmt
| s_if: expr -> stmt -> stmt -> stmt
| s_while: expr -> stmt -> stmt
| s_call: var -> proc -> expr -> stmt
| s_return: expr -> stmt
| s_getlock: lock -> stmt
| s_putlock: lock -> stmt
with

(*
 * procs both take and produce values
 *)
(*Inductive*) proc: Type :=
| p_proc: type -> var -> stmt -> proc
.

Notation "[{ s1 ; s2 ; }]" :=
  (s_seq s1 s2) (at level 90, s1 at next level, s2 at next level, format
"'[v' [{ '[  ' '//' s1 ; '//' s2 ; ']' '//' }] ']'").

