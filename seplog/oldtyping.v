Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

Require Import ast.
Require Import varmap.

(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                          old typing                          *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

(* variable gets read by an expression *)
Inductive InExpr : forall t, var -> expr -> Prop :=
| inexpr_read : forall t id,
    InExpr t (mkvar t id) (e_read (mkvar t id))
| inexpr_cond : forall t v b e1 e2,
    InExpr t v e1 -> InExpr t v e2 -> InExpr t v (e_cond t b e1 e2)
.

(* variable gets used in a statement *)
Inductive InStmt : forall t, var -> stmt -> Prop :=
| instmt_block_seq_1 : forall t v st1 st2,
    InStmt t v st1 -> InStmt t v (s_seq st1 st2)
| instmt_block_seq_2 : forall t v st1 st2,
    InStmt t v st2 -> InStmt t v (s_seq st1 st2)
| instmt_start : forall t v p e,
    InExpr t v e -> InStmt t v (s_start p e)
| instmt_assign_var : forall t v e,
    InStmt t v (s_assign v e)
| instmt_assign_expr : forall t v v' e,
    InExpr t v e -> InStmt t v (s_assign v' e)
| instmt_load : forall t id l,
    InStmt t (mkvar t id) (s_load (mkvar t id) l)
| instmt_store : forall t id l e,
    InExpr t (mkvar t id) e -> InStmt t (mkvar t id) (s_store l e)
| instmt_if_cond : forall v b s1 s2,
    InExpr t_bool v b -> InStmt t_bool v (s_if b s1 s2)
| instmt_if_body_1 : forall t v b s1 s2,
    InStmt t v s1 -> InStmt t v (s_if b s1 s2)
| instmt_if_body_2 : forall t v b s1 s2,
    InStmt t v s2 -> InStmt t v (s_if b s1 s2)
| instmt_while_cond : forall v b s,
    InExpr t_bool v b -> InStmt t_bool v (s_while b s)
| instmt_while_body : forall t v b s,
    InStmt t v s -> InStmt t v (s_while b s)
| instmt_call_var : forall rt id p e,
    InStmt rt (mkvar rt id) (s_call (mkvar rt id) p e)
| instmt_call_expr : forall t v v' p e,
    InExpr t v e -> InStmt t v (s_call v' p e)
(*
| instmt_local_var : forall t id e,
    InStmt t (mkvar t id) (s_local (mkvar t id) e)
| instmt_local_expr : forall t v v' e,
    InExpr t v e -> InStmt t v (s_local v' e)
*)
| instmt_return : forall t v e,
    InExpr t v e -> InStmt t v (s_return e)
(* XXX need to handle getlock and putlock *)
.
(* inspect to see that the constructor types were inferred properly *)
(* Print InStmt. *)

(*
 * XXX this doesn't work any more because it needs to collect vars from the
 * proc header.
 *)

(* XXX assuming the env for the proc and statement are separate,
   so variable use in a proc doesn't contaminate the calling statement whatsoever *)
(* Inductive InProc := . *)

(* does this expression respect the usage of varname s to denote a type t? *)
Inductive ExprVarRespectsT (t : type) (s : varidtype) : forall t', expr -> Prop :=
| evrt_value : forall t' exp,
    ExprVarRespectsT t s t' (e_value t' exp)
| evrt_read_eq : (* expr type had better be the same *)
    ExprVarRespectsT t s t (e_read (mkvar t s))
| evrt_read_neq : forall t' s', (* don't care about expr type *)
    s <> s' -> ExprVarRespectsT t s t' (e_read (mkvar t' s'))
| evrt_cond : forall t' b exp1 exp2,
    ExprVarRespectsT t s t_bool b -> ExprVarRespectsT t s t' exp1 -> ExprVarRespectsT t s t' exp2 ->
    ExprVarRespectsT t s t' (e_cond t' b exp1 exp2)
.

(* does this statement respect the usage of varname s to denote a type t? *)
(* XXX note that in both of these, non-usage counts as respectful! *)
Inductive StmtVarRespectsT (t : type) (s : varidtype) : stmt -> Prop :=
| svrt_block_nil : StmtVarRespectsT t s s_skip
| svrt_block_cons : forall st1 st2,
    StmtVarRespectsT t s st1 -> StmtVarRespectsT t s st2 ->
    StmtVarRespectsT t s (s_seq st1 st2)
| svrt_start : forall pt p e,
    (* XXX need to check pt against p *)
    ExprVarRespectsT t s pt e -> StmtVarRespectsT t s (s_start p e)
| svrt_assign_eq : forall e,
    ExprVarRespectsT t s t e -> StmtVarRespectsT t s (s_assign (mkvar t s) e)
| svrt_assign_neq : forall t' s' e,
    s <> s' -> ExprVarRespectsT t s t' e -> StmtVarRespectsT t s (s_assign (mkvar t' s') e)
| svrt_load_eq : forall l,
    StmtVarRespectsT t s (s_load (mkvar t s) l)
| svrt_load_neq : forall t' s' l,
    s <> s' -> StmtVarRespectsT t s (s_load (mkvar t' s') l)
| svrt_if : forall b s1 s2,
    ExprVarRespectsT t s t_bool b -> StmtVarRespectsT t s s1 -> StmtVarRespectsT t s s2 ->
    StmtVarRespectsT t s (s_if b s1 s2)
| svrt_while : forall b st,
    ExprVarRespectsT t s t_bool b -> StmtVarRespectsT t s st -> StmtVarRespectsT t s (s_while b st)
| svrt_call_eq : forall pt p exp,
    ExprVarRespectsT t s pt exp -> StmtVarRespectsT t s (s_call (mkvar t s) p exp)
| svrt_call_neq : forall t' s' pt p exp,
    (* XXX does this bind pt properly? *)
    s <> s' -> ExprVarRespectsT t s pt exp -> StmtVarRespectsT t s (s_call (mkvar t' s') p exp)
| svrt_return : forall t' e,
    ExprVarRespectsT t s t' e -> StmtVarRespectsT t s (s_return e)
(* XXX *)
| svrt_getlock : forall t' id,
    StmtVarRespectsT t s (s_getlock (mkvar (t_lock t') id))
| svrt_putlock : forall t' id,
    StmtVarRespectsT t s (s_putlock (mkvar (t_lock t') id))
.
(* inspect to see that the constructor types were inferred properly *)
(* Print StmtVarRespectsT. *)

Inductive DeclsVarRespectsT t id: list vardecl -> Prop :=
| dvrt_nil:
     DeclsVarRespectsT t id []
| dvrt_cons_eq: forall e decls,
     ExprVarRespectsT t id t e ->
     DeclsVarRespectsT t id decls ->
     DeclsVarRespectsT t id ((mkvardecl (mkvar t id) e) :: decls)
| dvrt_cons_neq : forall t' id' e decls,
     id <> id' ->
     ExprVarRespectsT t id t' e ->
     DeclsVarRespectsT t id decls ->
     DeclsVarRespectsT t id ((mkvardecl (mkvar t' id') e) :: decls)
.

(* does a proc respect variable usage? *)
Inductive ProcVarRespectsT pt rt: proc -> Prop :=
| pvrt : forall id decls body,
    StmtVarRespectsT pt id body ->
    DeclsVarRespectsT pt id decls ->
    (forall t id, InStmt t (mkvar t id) body -> StmtVarRespectsT t id body) ->
    ProcVarRespectsT pt rt (mkproc rt (mkvar pt id) decls body)
.
