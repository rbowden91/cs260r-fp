Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

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

(* variables are identified with numbers *)
Inductive var: Type :=
| mkvar: type -> nat -> var
.

(* heap addresses are also numbers (and which heap, currently a bool) *)
Inductive addr: Type :=
| mkaddr : type -> nat -> bool -> addr
.

Inductive value: Type :=
| v_unit: value
| v_nat (n: nat): value
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
| e_read: type -> var -> expr
| e_cond: type -> expr -> expr -> expr -> expr
.

(*
 * statements don't
 *)
Inductive stmt: Type :=
| s_block: list stmt -> stmt
| s_start: forall (pt : type), proc -> expr -> stmt (* XXX remove pt *)
| s_assign: forall (t : type), var -> expr -> stmt  (* XXX remove t *)
| s_load: forall (t : type), var -> expr -> stmt  (* XXX remove t *)
| s_store: forall (t : type), var -> expr -> stmt  (* XXX remove t *)
| s_scope: stmt -> stmt
| s_if: expr -> stmt -> stmt -> stmt
| s_while: expr -> stmt -> stmt
| s_call: forall (pt rt : type), var -> proc -> expr -> stmt
          (* XXX remove pt, rt *)
| s_local: forall (t : type), var -> expr -> stmt (* XXX remove t *)
| s_return: forall (t : type), expr -> stmt	 (* XXX remove t *)
| s_getlock: forall (t : type), var -> stmt	 (* XXX remove t *)
| s_putlock: forall (t : type), var -> stmt	 (* XXX remove t *)
with

(*
 * procs both take and produce values
 *)
(*Inductive*) proc: Type :=
| mkproc: forall (pt rt : type), var -> stmt -> proc (* XXX remove pt rt *)
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

Definition s_skip: stmt := s_block nil.

