Require Import String.
Require Import List.
Require Import BinInt.
Import ListNotations.

Definition s_prop := nat.

Definition invariant := (nat * nat)%type.

Inductive lock_type :=
| LockVnode
| LockBuffer
| LockLog
.

Inductive lock : Type :=
| Lock (type : lock_type) (inv : invariant) : lock
.

Definition vnode := Z.

Inductive val : Type -> Type :=
| Vlock (lck : lock) : val lock
| Vvnode (vn : vnode) : val vnode
| Vint (i : Z) : val Z
| Vbool (b : bool) : val bool
| Vundef : val unit
(*| Vproc *)
.


Inductive var : Type -> Type :=
| Var (s : string) : forall t, var t
.

Inductive binop : Type -> Type :=
| BinPlus (n1 : expr Z) (n2 : expr Z) : binop nat
| BinMinus (n1 : expr Z) (n2 : expr Z) : binop nat
| BinMult (n1 : expr Z) (n2 : expr Z) : binop nat
| BinDiv (n1 : expr Z) (n2 : expr Z) : binop nat
| BinMod (n1 : expr Z) (n2 : expr Z) : binop nat
| BinGt (n1 : expr Z) (n2 : expr Z) : binop bool
| BinGte (n1 : expr Z) (n2 : expr Z) : binop bool
| BinEq (n1 : expr Z) (n2 : expr Z) : binop bool
| BinLt (n1 : expr Z) (n2 : expr Z) : binop bool
| BinLte (n1 : expr Z) (n2 : expr Z) : binop bool
| BinAnd (b1 : expr bool) (b2 : expr bool) : binop bool
| BinOr (b1 : expr bool) (b2 : expr bool) : binop bool
(* etc... *)


with unop : Type -> Type :=
| UnopNeg (n : expr nat) : unop nat
| UnopNot (b : expr bool) : unop bool


(*
 * expressions produce values
 *)
with expr : Type -> Type :=
| Value : forall {t}, val t -> expr t
| Read : forall {t}, var t -> expr t
| Unop : forall {t}, unop t -> expr t
| Binop : forall {t}, binop t -> expr t
| Cond : forall {t}, expr bool -> expr t -> expr t -> expr t
.

Function eval_expr {t} (env : forall {t'}, var t' -> val t') (e : expr t) :=
  match e with
  | Value v => false
  (*| @Read t' v => if t' = t then Some env v else None*)
  | Read _ => false
  | Unop u => eval_unop env u
  | Binop b => eval_binop env b
  | Cond b e1 e2 => if eval_binop env b then eval_expr e1
                    else eval_expr e2
  end
with eval_unop {t} (env : var t -> val t) (u : unop t) :=
  match u with
  | UnopNeg e => ~-(eval_expr e)
  | UnopNot e => notb eval_expr e
  end
with eval_binop {t} (env : var t -> val t) (b : binop t) :=
  match b with
  | BinPlus n1 n2 => n1 + n2
  | BinMinus n1 n2 => n1 - n2 (* negative numbers? *)
  | BinMult n1 n2 => n1 * n2
  | BinDiv  n1 n2 => n1 / n2
  | BinMod n1 n2 => n1 % n2
  | BinGt n1 n2 =>  n2 <? n1
  | BinGte n1 n2 => gteb n1 n2
  | BinEq n1 n2 => eqb n1 n2
  | BinLt n1 n2 => ltb n1 n2
  | BinLte n1 n2 => lteb n1 n2
  | BinAnd b1 b2 => andb b1 b2
  | BinOr b1 b2 => orb b1 b2
  end
.

(*
 * statements don't
 *)
Inductive stmt : Type :=
| Block (stmts : list stmt) : stmt
| Start : stmt -> stmt
| Assign : forall t, var t -> expr t -> stmt
| Load : forall t, var t -> expr nat -> stmt
| Store : forall t, expr nat -> expr t -> stmt
| If : expr bool -> stmt -> stmt -> stmt
| While : expr bool -> stmt -> stmt
| Call : forall pt rt, var rt -> proc pt rt -> expr pt -> stmt
| Local : forall t, var t -> stmt
| Return : forall t, expr t -> stmt
(*
| getlock: Lock -> Stmt
| putlock: Lock -> Stmt
| makelock
| freelock
| alloc
| free
*)
with

(*
 * procs both take and produce values
 *)
(*Inductive*) proc: Type -> Type -> Type :=
| Proc: forall pt rt, var pt -> stmt -> proc pt rt
.

(*Inductive prog := list proc.*)

Definition env := nat.
Definition addr := nat.

Inductive hoare_stmt :
  env -> (forall t, expr t -> s_prop) ->
  (lock_type -> addr -> (s_prop * s_prop)) ->
  s_prop -> s_prop -> stmt -> s_prop -> s_prop -> Prop :=

| HtSkip : forall env ret RI,
           forall P C,
           hoare_stmt env ret RI 
                      C P (Block []) C P.

| HtReturn : forall env ret RI,
             forall S E P C el vl,
    eval_expr el = Some vl ->
    ret(vl) ->
    hoare_judgement J R B S E P C (Sreturn el) MFalse.


| HtWhile : forall J R E I C s,
    hoare_stmt J R S E I C s I ->
    hoare_judgement J R B S E I C (Sloop s) MFalse
| HtExit : forall J R B S E C b n,
    nth_error B n = Some b ->
    hoare_judgement J R B S E b C (Sexit n) MFalse
| HtSeq : forall J R B S E P C Q s1 s2 P',
    hoare_judgement J R B S E P C s1 P' ->
    (P' ===> C) -> (* Is this right? *)
    hoare_judgement J R B S E P' C s2 Q ->
    hoare_judgement J R B S E P C (Sseq s1 s2) Q
| HtBlock : forall J R B S E P C Q s,
    hoare_judgement J R (Q::B) S E P C s MFalse ->
    hoare_judgement J R B S E P C (Sblock s) Q


| HtAssign : forall J R B P C,
  is_pure_expr e1 = true ->
  is_pure_expr e2 = true ->
  
  hoare_judgement J R B S E P C (Sassign e1 e2) 

| HtIfThenElse : forall J R B S E P C Q e s1 s2,
    is_pure_expr e = true -> (* Why pure? *)
    hoare_judgement J R B S E (P * lift(e)) C s1 Q -> (* Lift? *)
    hoare_judgement J R B S E (P * lift(e))) C s2 Q -> (* Lift? *)
    hoare_judgement J R B S E P C (Sifthenelse e s1 s2) Q ->


| HtReturn : forall J R B S E P C el vl,
    eval_expr el = Some vl ->
    R(vl) ->
    hoare_judgement J R B S E P C (Sreturn el) MFalse.



| HtStore :
| HtCall :


(* When forking into two threads, divide the (local) heap among them. *)
| HtPar : forall P1 c1 Q1 P2 c2 Q2,
    hoare_triple linvs P1 c1 Q1
    -> hoare_triple linvs P2 c2 Q2
    -> hoare_triple linvs (P1 * P2)%sep (Par c1 c2) (fun _ => Q1 tt * Q2 tt)%sep

| HtAlloc : forall numWords,
    hoare_triple linvs emp%sep (Alloc numWords) (fun r => r |--> zeroes numWords * [| r <> 0 |])%sep
| HtFree : forall a numWords,
    hoare_triple linvs (a |->? numWords)%sep (Free a numWords) (fun _ => emp)%sep

(* Next, how to handle locking: the thread takes ownership of a memory chunk
 * satisfying the lock's invariant. *)
| HtLock : forall a I1 I2,
    lookup linvs a = Some I
    -> hoare_triple linvs emp%sep (Lock a) (fun _ => I)
| HtCreateLock : forall a I1 I2,
    lookup linvs a = Some I
    -> hoare_triple linvs emp%sep (Lock a) (fun _ => I)
| HtDestroyLock : forall a I1 I2,
    lookup linvs a = Some I
    -> hoare_triple linvs emp%sep (Lock a) (fun _ => I)

(* When unlocking, the thread relinquishes ownership of a memory chunk
 * satisfying the lock's invariant. *)
| HtUnlock : forall a I,
    nth_error linvs a = Some I
    -> hoare_triple linvs I (Unlock a) (fun _ => emp)%sep

(* The usual consequence rule. *)
| HtConsequence : forall {result} (c : cmd result) P Q (P' : hprop) (Q' : _ -> hprop),
    hoare_triple linvs P c Q
    -> P' ===> P
    -> (forall r, Q r ===> Q' r)
    -> hoare_triple linvs P' c Q'

| HtFrame : forall {result} (c : cmd result) P Q R,
    hoare_triple linvs P c Q
    -> hoare_triple linvs (P * R)%sep c (fun r => Q r * R)%sep.
