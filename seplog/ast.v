Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

Require Import msl.eq_dec.

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




Inductive invariant : Type :=
(* Just an example *)
| nat_inv : invariant
.




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


Instance EqDec_var : EqDec (var) := _.
Proof.
Admitted.


Instance EqDec_lock : EqDec (lock) := _.
Proof.
Admitted.

