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

(* types are the types of values we can touch directly *)
Inductive type :=
| t_unit : type
| t_nat  : type
| t_bool : type
| t_pair : type -> type -> type
| t_list : type -> type
| t_addr : type -> type
| t_lock : type -> type
.

(* variables are identified by numbers *)
Inductive var: Type :=
| mkvar: type -> nat -> var
.

Definition type_of_var v :=
   match v with
   | mkvar t _ => t
   end.

Inductive WhichHeap: Set :=
| MemoryHeap: WhichHeap
| DiskHeap (disknum: nat): WhichHeap
.

(* heap addresses are also numbers (and which heap, currently a bool) *)
Inductive addr: Type :=
| mkaddr : type -> nat -> WhichHeap -> addr
.

Inductive value : Type :=
| v_unit: value
| v_nat  (n: nat): value
| v_bool (b: bool): value
| v_pair (a: value) (b: value): value
| v_list (t: type) (l: list value): value
| v_addr (a: addr): value
| v_lock (a: addr): value
| v_undef: value
.

Function type_of_value (v: value): type :=
   match v with
   | v_unit => t_unit
   | v_nat _ => t_nat
   | v_bool _ => t_bool
   | v_pair a b => t_pair (type_of_value a) (type_of_value b)
   | v_list t l => t_list t
   | v_addr (mkaddr ty _ _) => t_addr ty
   | v_lock (mkaddr ty _ _) => t_lock ty
   | v_undef => t_unit (* XXX *)
   end.

Inductive invariant : Type :=
(* Just an example *)
| nat_inv : invariant
.

(*
 * expressions produce values
 *)
Inductive expr: Type :=
| e_value: type -> value -> expr
| e_getlockaddr : type -> expr -> expr
| e_read: var -> expr
| e_cond: type -> expr -> expr -> expr -> expr
| e_natbinop: (nat -> nat -> nat) -> expr -> expr -> expr
.

(*
 * statements don't
 *)
Inductive stmt: Type :=
| s_skip: stmt
| s_seq: stmt -> stmt -> stmt
| s_start: proc -> expr -> stmt
| s_assign: var -> expr -> stmt
| s_load: var -> expr -> stmt
| s_store: var -> expr -> stmt
| s_if: expr -> stmt -> stmt -> stmt
| s_while: expr -> stmt -> stmt
| s_call: var -> proc -> expr -> stmt
| s_return: expr -> stmt
| s_getlock: var -> stmt
| s_putlock: var -> stmt
with

(*
 * variable declarations take values
 * (everything needs to be initialized)
 *)
(*Inductive*) vardecl: Type :=
| mkvardecl: var -> expr -> vardecl
with

(*
 * procs both take and produce values
 *)
(*Inductive*) proc: Type :=
| mkproc: type -> var -> list vardecl -> stmt -> proc
.


(*
 * Extended/sugary AST forms
 *)

Definition v_true: value := v_bool true.
Definition v_false: value := v_bool false.

(* doesn't quite work any more
Definition e_coqcall {ta tr : type} (f : ta -> tr) (x : ta): expr tr :=
   e_value tr (f x)
.
*)

(* no longer relevant
Definition s_skip: stmt := s_block nil.
*)

(*
 * Notation
 *)
(* The last statement doesn't take a semicolon *)
Notation "[{ s1 ; .. ; s2 }]" :=
  (s_seq s1 (.. (s_seq s2 s_skip) ..)) (at level 90, s1 at next level, s2 at next level, format
"'[v' [{ '[  ' '//' s1 ; '//' .. ; '//' s2 ']' '//' }] ']'").


Instance EqDec_var : EqDec (var) := _.
Proof.
Admitted.


Instance EqDec_lock : EqDec (addr) := _.
Proof.
Admitted.

