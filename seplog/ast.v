Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.
Add LoadPath "/Users/rbowden/Dropbox (CS50)/courses/cs260r/cs260r-fp/VST".
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

Definition var := nat.
Definition addr := nat.
Definition disk_addr := nat.

Inductive value :=
| v_nat (n:nat)
| v_addr (a:addr)
| v_bool (b:bool)
| v_undef
.


Definition table (A : Type) := list (A*value).

Fixpoint table_get {A}{H: EqDec A} (rho: table A) (x: A) : option value :=
  match rho with
  | (y,v)::ys => if eq_dec x y then Some v else table_get ys x
  | nil => None
 end.

Definition table_set {A}{H: EqDec A} (x: A) (v: value) (rho: table A)  : table A := (x,v)::rho.

Lemma table_gss {A}{H: EqDec A}: forall rho x v, table_get (table_set x v rho) x = Some v.
Proof.
intros.
simpl. destruct (eq_dec x x); auto. contradiction n; auto.
Qed.

Lemma table_gso {A}{H: EqDec A}: forall rho x y v, x<>y -> table_get (table_set x v rho) y = table_get rho y.
Proof.
intros.
simpl. destruct (eq_dec y x); auto.  contradiction H0; auto.
Qed.


Definition env := table var.
Definition heap := table addr.
Definition disk := table disk_addr.


Inductive invariant : Type :=
(* Just an example *)
| nat_inv : invariant
.

(* locks are a special class of variables *)
Inductive lock: Type :=
| mklock : invariant -> lock
.

Definition state := (heap * disk)%type.

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
| s_block: list stmt -> stmt
| s_start: proc -> expr -> stmt
| s_assign: var -> expr -> stmt
| s_load: var -> lock -> stmt
| s_store: lock -> expr -> stmt
| s_if: expr -> stmt -> stmt -> stmt
| s_while: expr -> stmt -> stmt
| s_call: var -> proc -> expr -> stmt
| s_local: var -> expr -> stmt
| s_return: expr -> stmt
| s_getlock: lock -> stmt
| s_putlock: lock -> stmt
with

(*
 * procs both take and produce values
 *)
(*Inductive*) proc: Type :=
| p_proc: var -> stmt -> proc
.

(*

(*
 * Extended/sugary AST forms
 *)

Definition coqcall {ta tr : Set} (f : ta -> tr) (x : ta): Expr tr :=
   value tr (f x)
.
*)
Definition skip: stmt := s_block nil.
(*
(*
 * well-formedness constraints
 *
 * this is (for now) chiefly about insisting that every variable is declared
 * exactly once. types are mostly enforced by the embedding. we ignore scopes
 * when checking for duplicate declarations, at least for now.
 *)

(* check that variable declarations are unique *)
Inductive StmtDeclaresVar: forall t, Stmt -> Var t -> bool -> Prop :=
| block_declares_var_nil: forall t v,
     StmtDeclaresVar t (block []) v false
| block_declares_var_cons_here: forall t s ss v,
     StmtDeclaresVar t s v true -> StmtDeclaresVar t (block ss) v false ->
     StmtDeclaresVar t (block (s :: ss)) v true
| block_declares_var_cons_nothere: forall t s ss v b,
     StmtDeclaresVar t s v false -> StmtDeclaresVar t (block ss) v b ->
     StmtDeclaresVar t (block (s :: ss)) v b
| start_declares_var: forall t s v b pt p e,
     StmtDeclaresVar t s v b ->
     StmtDeclaresVar t (start pt p e) v false
| assign_declares_var: forall t' t e e' v',
     StmtDeclaresVar t' (assign t e e') v' false
| load_declares_var: forall t' t v e v',
     StmtDeclaresVar t' (load t v e) v' false
| store_declares_var: forall t' t v e v',
     StmtDeclaresVar t' (store t v e) v' false
| if_declares_var: forall t e s1 s2 v b1 b2,
     StmtDeclaresVar t s1 v b1 -> StmtDeclaresVar t s2 v b2 ->
     StmtDeclaresVar t (if_ e s1 s2) v (b1 || b2)
| while_declares_var: forall t e s v b,
     StmtDeclaresVar t s v b ->
     StmtDeclaresVar t (while e s) v b
| call_declares_var: forall t' (pt rt : Set) v p e v' b,
     ProcDeclaresVar t' pt rt p v' b ->
     StmtDeclaresVar t' (call pt rt v p e) v' b
| local_declares_var: forall t v e,
     StmtDeclaresVar t (local t v e) v true
| return_declares_var: forall t' t e v',
     StmtDeclaresVar t' (return_ t e) v' false
with
(*Inductive*) ProcDeclaresVar: forall t pt rt, Proc pt rt -> Var t -> bool -> Prop :=
| proc_declares_var_arg: forall pt rt s v,
     StmtDeclaresVar pt s v false ->
     ProcDeclaresVar pt pt rt (proc pt rt v s) v true
| proc_declares_var_nonarg_sametype: forall pt rt s v' v b,
     StmtDeclaresVar pt s v b ->
     v <> v' ->
     ProcDeclaresVar pt pt rt (proc pt rt v' s) v b
| proc_declares_var_nonarg_othertype: forall t pt rt s v' v b,
     StmtDeclaresVar t s v b ->
     t <> pt ->
     ProcDeclaresVar t pt rt (proc pt rt v' s) v b
.

(* check that variable uses are after declarations *)
(*
Inductive StmtLooseVars: forall t, Stmt -> list (Var t) -> Prop :=
| block_loose_vars_nil: forall t,
     StmtLooseVars t (block []) []
| (* TBD *)
*)


(* check that procedure returns are ok *)

Inductive StmtEndsInReturn: Stmt -> Type -> Prop :=
| block_ends_in_return: forall ss t e,
     StmtEndsInReturn (block (ss ++ [return_ t e])) t
| if_ends_in_return: forall s1 s2 t e,
     StmtEndsInReturn s1 t -> StmtEndsInReturn s2 t ->
     StmtEndsInReturn (if_ e s1 s2) t
| return_ends_in_return: forall t e,
     StmtEndsInReturn (return_ t e) t
with
(*Inductive*) ProcReturnOk: forall (pt : Set) rt, Proc pt rt -> Prop :=
| proc_return_ok: forall pt rt v s,
     StmtEndsInReturn s rt ->
     ProcReturnOk pt rt (proc pt rt v s)
.


(* variable gets read by an expression *)
Inductive InExpr : forall t, Var t -> Expr t -> Prop :=
| inexpr_read : forall t v,
    InExpr t v (read t v)
| inexpr_cond : forall t v b e1 e2,
    InExpr t v e1 -> InExpr t v e2 -> InExpr t v (cond t b e1 e2)
.

(* variable gets used in a statement *)
Inductive InStmt : forall t, Var t -> Stmt -> Prop :=
| instmt_block_front : forall t v st sts,
    InStmt t v st -> InStmt t v (block (st :: sts))
| instmt_block_cons : forall t v st sts,
    InStmt t v (block sts) -> InStmt t v (block (st :: sts))
| instmt_start : forall t v p e,
    InExpr t v e -> InStmt t v (start t p e)
| instmt_assign_var : forall t v e,
    InStmt t v (assign t v e)
| instmt_assign_expr : forall t v v' e,
    InExpr t v e -> InStmt t v (assign t v' e)
| instmt_load : forall t v l,
    InStmt t v (load t v l)
| instmt_store : forall t v l e,
    InExpr t v e -> InStmt t v (store t l e)
| instmt_if_cond : forall v b s1 s2,
    InExpr bool v b -> InStmt bool v (if_ b s1 s2)
| instmt_if_body_1 : forall t v b s1 s2,
    InStmt t v s1 -> InStmt t v (if_ b s1 s2)
| instmt_if_body_2 : forall t v b s1 s2,
    InStmt t v s2 -> InStmt t v (if_ b s1 s2)
| instmt_while_cond : forall v b s,
    InExpr bool v b -> InStmt bool v (while b s)
| instmt_while_body : forall t v b s,
    InStmt t v s -> InStmt t v (while b s)
| instmt_call_var : forall t v pt p e,
    InStmt t v (call pt t v p e)
| instmt_call_expr : forall t v rt v' p e,
    InExpr t v e -> InStmt t v (call t rt v' p e)
| instmt_local_var : forall t v e,
    InStmt t v (local t v e)
| instmt_local_expr : forall t v v' e,
    InExpr t v e -> InStmt t v (local t v' e)
| instmt_return : forall t v e,
    InExpr t v e -> InStmt t v (return_ t e)
(* XXX it's never in getlock or putlock? *)
.
(* inspect to see that the constructor types were inferred properly *)
(* Print InStmt. *)

(* XXX assuming the env for the proc and statement are separate,
   so variable use in a proc doesn't contaminate the calling statement whatsoever *)
(* Inductive InProc := . *)

(* does this expression respect the usage of varname s to denote a type t? *)
Inductive ExprVarRespectsT (t : Set) (s : string) : forall t', Expr t' -> Prop :=
| evrt_value : forall t' exp,
    ExprVarRespectsT t s t' (value t' exp)
| evrt_read_eq : (* expr type had better be the same *)
    ExprVarRespectsT t s t (read t (var t s))
| evrt_read_neq : forall t' s', (* don't care about expr type *)
    s <> s' -> ExprVarRespectsT t s t' (read t' (var t' s'))
| evrt_cond : forall t' b exp1 exp2,
    ExprVarRespectsT t s bool b -> ExprVarRespectsT t s t' exp1 -> ExprVarRespectsT t s t' exp2 ->
    ExprVarRespectsT t s t' (cond t' b exp1 exp2)
.

(* does this statement respect the usage of varname s to denote a type t? *)
(* XXX note that in both of these, non-usage counts as respectful! *)
Inductive StmtVarRespectsT (t : Set) (s : string) : Stmt -> Prop :=
| svrt_block_nil : StmtVarRespectsT t s (block [])
| svrt_block_cons : forall st sts,
    StmtVarRespectsT t s st -> StmtVarRespectsT t s (block sts) ->
    StmtVarRespectsT t s (block (st :: sts))
| svrt_start : forall pt p e,
    ExprVarRespectsT t s pt e -> StmtVarRespectsT t s (start pt p e)
| svrt_assign_eq : forall e,
    ExprVarRespectsT t s t e -> StmtVarRespectsT t s (assign t (var t s) e)
| svrt_assign_neq : forall t' s' e,
    s <> s' -> ExprVarRespectsT t s t' e -> StmtVarRespectsT t s (assign t' (var t' s') e)
| svrt_load_eq : forall l,
    StmtVarRespectsT t s (load t (var t s) l)
| svrt_load_neq : forall t' s' l,
    s <> s' -> StmtVarRespectsT t s (load t' (var t' s') l)
| svrt_if : forall b s1 s2,
    ExprVarRespectsT t s bool b -> StmtVarRespectsT t s s1 -> StmtVarRespectsT t s s2 ->
    StmtVarRespectsT t s (if_ b s1 s2)
| svrt_while : forall b st,
    ExprVarRespectsT t s bool b -> StmtVarRespectsT t s st -> StmtVarRespectsT t s (while b st)
| svrt_call_eq : forall pt p exp,
    ExprVarRespectsT t s pt exp -> StmtVarRespectsT t s (call pt t (var t s) p exp)
| svrt_call_neq : forall t' s' pt p exp,
    s <> s' -> ExprVarRespectsT t s pt exp -> StmtVarRespectsT t s (call pt t' (var t' s') p exp)
| svrt_local_eq : forall e,
    ExprVarRespectsT t s t e -> StmtVarRespectsT t s (local t (var t s) e)
| svrt_local_neq : forall t' s' e,
    s <> s' -> ExprVarRespectsT t s t' e -> StmtVarRespectsT t s (local t' (var t' s') e)
| svrt_return : forall t' e,
    ExprVarRespectsT t s t' e -> StmtVarRespectsT t s (return_ t' e)
(* XXX *)
| svrt_getlock : forall t' l,
    StmtVarRespectsT t s (getlock t' l)
| svrt_putlock : forall t' l,
    StmtVarRespectsT t s (putlock t' l)
.
(* inspect to see that the constructor types were inferred properly *)
(* Print StmtVarRespectsT. *)

(* does a proc respect variable usage? *)
Inductive ProcVarRespectsT (pt : Set) (rt : Set) : Proc pt rt -> Prop :=
| pvrt : forall s st,
    StmtVarRespectsT pt s st ->
    (forall t s, InStmt t (var t s) st -> StmtVarRespectsT t s st) ->
    ProcVarRespectsT pt rt (proc pt rt (var pt s) st)
.


Definition StmtOk s : Prop :=
   (forall t v (b : bool), StmtDeclaresVar t s v b) /\
   (* (forall t, StmtLooseVars t s []) *) True.

Inductive ProcOk: forall pt rt, Proc pt rt -> Prop :=
| proc_ok: forall pt rt v s,
     StmtOk s ->
     ProcReturnOk pt rt (proc pt rt v s) ->
     ProcOk pt rt (proc pt rt v s)
.

*)
