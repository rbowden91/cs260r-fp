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
(*                           astprops                           *)
(*                                                              *)
(* ************************************************************ *)
(* ************************************************************ *)

(*
 * well-formedness constraints
 *
 * we have the following constraints:
 *   1. scoping: variables must be used only in their scope.
 *   2. uniqueness: (local) variable identifiers must be unique across
 *      each entire proc.
 *   3. flow: variables must be declared before used.
 *   4. typing: each local variable has exactly one type.
 *
 * "VarsScoped" covers #1 and #3.
 * "VarsUnique" covers #2; it's separate because its environment is
 *     different.
 * "VarsTyped" covers #4.
 *
 * A proc is well-formed if it satisfies all these properties.
 *
 * this is (for now) chiefly about insisting that every variable is declared
 * exactly once. types are mostly enforced by the embedding. we ignore scopes
 * when checking for duplicate declarations, at least for now.
 *)

(* scoping *)
Inductive VarsScopedExpr: forall (t: type), VarMap type -> expr t -> Prop :=
| vars_scoped_value: forall (t: type) env k,
     VarsScopedExpr t env (e_value t k)
| vars_scoped_read: forall (t: type) env id,
     VarMapMapsTo (mkvar t id) t env ->
     VarsScopedExpr t env (e_read t (mkvar t id))
| vars_scoped_cond: forall t env pred te fe,
     VarsScopedExpr t_bool env pred ->
     VarsScopedExpr t env te ->
     VarsScopedExpr t env fe ->
     VarsScopedExpr t env (e_cond t pred te fe)
.

Inductive VarsScopedStmt: VarMap type -> stmt -> VarMap type -> Prop :=
| vars_scoped_block_nil: forall env,
     VarsScopedStmt env (s_block []) env
| vars_scoped_block_cons: forall env s env' ss env'',
     VarsScopedStmt env s env' ->
     VarsScopedStmt env' (s_block ss) env'' ->
     VarsScopedStmt env (s_block (s :: ss)) env''
| vars_scoped_start: forall env pt p e,
     VarsScopedExpr pt env e ->
     VarsScopedStmt env (s_start pt p e) env
| vars_scoped_assign: forall t env id e,
     VarsScopedExpr t env e ->
     VarMapMapsTo (mkvar t id) t env ->
     VarsScopedStmt env (s_assign t (mkvar t id) e) env
| vars_scoped_load: forall t env id l,
     VarMapMapsTo (mkvar t id) t env ->
     VarsScopedStmt env (s_load t (mkvar t id) l) env
| vars_scoped_store: forall t env id l e,
     @VarMapMapsTo t type (mkvar t id) t env ->
     VarsScopedExpr t env e ->
     VarsScopedStmt env (s_store t l e) env
| vars_scoped_scope: forall env s env',
     VarsScopedStmt env s env' ->
     VarsScopedStmt env (s_scope s) env
| vars_scoped_if: forall env pred ts fs env't env'f,
     VarsScopedExpr t_bool env pred ->
     VarsScopedStmt env ts env't ->
     VarsScopedStmt env fs env'f ->
     VarsScopedStmt env (s_if pred ts fs) env
| vars_scoped_while: forall env pred body env'body,
     VarsScopedExpr t_bool env pred ->
     VarsScopedStmt env body env'body ->
     VarsScopedStmt env (s_while pred body) env
| vars_scoped_call: forall env pt rt id p arg,
     VarsScopedProc pt rt p ->
     VarsScopedExpr pt env arg ->
     VarMapMapsTo (mkvar rt id) rt env ->
     VarsScopedStmt env (s_call pt rt (mkvar rt id) p arg) env
| vars_scoped_local: forall t env id e,
     VarsScopedExpr t env e ->
     ~(VarMapIn (mkvar t id) env) ->
     VarsScopedStmt env (s_local t (mkvar t id) e) (VarMap_add (mkvar t id) t env)
| vars_scoped_return: forall t env e,
     VarsScopedExpr t env e ->
     VarsScopedStmt env (s_return t e) env
| vars_scoped_getlock: forall t env l,
     VarsScopedStmt env (s_getlock t l) env
| vars_scoped_putlock: forall t env l,
     VarsScopedStmt env (s_getlock t l) env
with
(*Inductive*) VarsScopedProc: forall pt rt, proc pt rt -> Prop :=
| vars_scoped_proc: forall pt rt id body env',
     VarsScopedStmt (VarMap_add (mkvar pt id) pt (VarMap_empty type)) body env' ->
     VarsScopedProc pt rt (mkproc pt rt (mkvar pt id) body)
.

(* uniqueness *)

(*
 * This differs in that the environment doesn't nest. Also,
 * it doesn't reason about exprs; it relies on VarsScoped to
 * make sure they refer only to variables that exist.
 *)

Inductive VarsUniqueStmt: stmt -> VarMap unit -> Prop :=
| vars_unique_block_nil:
     VarsUniqueStmt (s_block []) (VarMap_empty unit)
| vars_unique_block_cons: forall s env ss env',
     VarsUniqueStmt s env ->
     VarsUniqueStmt (s_block ss) env' ->
     VarMapDisjoint unit env env' ->
     VarsUniqueStmt (s_block (s :: ss)) (VarMap_union env env')
| vars_unique_start: forall pt p e,
     VarsUniqueStmt (s_start pt p e) (VarMap_empty unit)
| vars_unique_assign: forall t x e,
     VarsUniqueStmt (s_assign t x e) (VarMap_empty unit)
| vars_unique_load: forall t x l,
     VarsUniqueStmt (s_load t x l) (VarMap_empty unit)
| vars_unique_store: forall t l e,
     VarsUniqueStmt (s_store t l e) (VarMap_empty unit)
| vars_unique_if: forall pred ts fs env't env'f,
     VarsUniqueStmt ts env't ->
     VarsUniqueStmt fs env'f ->
     VarMapDisjoint unit env't env'f ->
     VarsUniqueStmt (s_if pred ts fs) (VarMap_union env't env'f)
| vars_unique_while: forall cond body env'body,
     VarsUniqueStmt body env'body ->
     VarsUniqueStmt (s_while cond body) env'body
| vars_unique_call: forall pt rt x p arg,
     VarsUniqueProc pt rt p ->
     VarsUniqueStmt (s_call pt rt x p arg) (VarMap_empty unit)
| vars_unique_local: forall t x e,
     VarsUniqueStmt (s_local t x e) (VarMap_add x tt(*unit*) (VarMap_empty unit))
| vars_unique_return: forall t e,
     VarsUniqueStmt (s_return t e) (VarMap_empty unit)
| vars_unique_getlock: forall t l,
     VarsUniqueStmt (s_getlock t l) (VarMap_empty unit)
| vars_unique_putlock: forall t l,
     VarsUniqueStmt (s_getlock t l) (VarMap_empty unit)
with
(*Inductive*) VarsUniqueProc: forall pt rt, proc pt rt -> Prop :=
| vars_unique_proc: forall pt rt x body env',
     VarMapDisjoint unit (VarMap_add x tt(*unit*) (VarMap_empty unit)) env' ->
     VarsUniqueStmt body env' ->
     VarsUniqueProc pt rt (mkproc pt rt x body)
.


(* check that procedure returns are ok *)

Inductive StmtEndsInReturn: stmt -> type -> Prop :=
| block_ends_in_return: forall ss t e,
     StmtEndsInReturn (s_block (ss ++ [s_return t e])) t
| if_ends_in_return: forall s1 s2 t e,
     StmtEndsInReturn s1 t -> StmtEndsInReturn s2 t ->
     StmtEndsInReturn (s_if e s1 s2) t
| return_ends_in_return: forall t e,
     StmtEndsInReturn (s_return t e) t
with
(*Inductive*) ProcReturnOk: forall pt rt, proc pt rt -> Prop :=
| proc_return_ok: forall pt rt v s,
     StmtEndsInReturn s rt ->
     ProcReturnOk pt rt (mkproc pt rt v s)
.


(* variable gets read by an expression *)
Inductive InExpr : forall t, var t -> expr t -> Prop :=
| inexpr_read : forall t v,
    InExpr t v (e_read t v)
| inexpr_cond : forall t v b e1 e2,
    InExpr t v e1 -> InExpr t v e2 -> InExpr t v (e_cond t b e1 e2)
.

(* variable gets used in a statement *)
Inductive InStmt : forall t, var t -> stmt -> Prop :=
| instmt_block_front : forall t v st sts,
    InStmt t v st -> InStmt t v (s_block (st :: sts))
| instmt_block_cons : forall t v st sts,
    InStmt t v (s_block sts) -> InStmt t v (s_block (st :: sts))
| instmt_start : forall t v p e,
    InExpr t v e -> InStmt t v (s_start t p e)
| instmt_assign_var : forall t v e,
    InStmt t v (s_assign t v e)
| instmt_assign_expr : forall t v v' e,
    InExpr t v e -> InStmt t v (s_assign t v' e)
| instmt_load : forall t v l,
    InStmt t v (s_load t v l)
| instmt_store : forall t v l e,
    InExpr t v e -> InStmt t v (s_store t l e)
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
| instmt_call_var : forall t v pt p e,
    InStmt t v (s_call pt t v p e)
| instmt_call_expr : forall t v rt v' p e,
    InExpr t v e -> InStmt t v (s_call t rt v' p e)
| instmt_local_var : forall t v e,
    InStmt t v (s_local t v e)
| instmt_local_expr : forall t v v' e,
    InExpr t v e -> InStmt t v (s_local t v' e)
| instmt_return : forall t v e,
    InExpr t v e -> InStmt t v (s_return t e)
(* XXX it's never in getlock or putlock? *)
.
(* inspect to see that the constructor types were inferred properly *)
(* Print InStmt. *)

(* XXX assuming the env for the proc and statement are separate,
   so variable use in a proc doesn't contaminate the calling statement whatsoever *)
(* Inductive InProc := . *)

(* does this expression respect the usage of varname s to denote a type t? *)
Inductive ExprVarRespectsT (t : type) (s : varidtype) : forall t', expr t' -> Prop :=
| evrt_value : forall t' exp,
    ExprVarRespectsT t s t' (e_value t' exp)
| evrt_read_eq : (* expr type had better be the same *)
    ExprVarRespectsT t s t (e_read t (mkvar t s))
| evrt_read_neq : forall t' s', (* don't care about expr type *)
    s <> s' -> ExprVarRespectsT t s t' (e_read t' (mkvar t' s'))
| evrt_cond : forall t' b exp1 exp2,
    ExprVarRespectsT t s t_bool b -> ExprVarRespectsT t s t' exp1 -> ExprVarRespectsT t s t' exp2 ->
    ExprVarRespectsT t s t' (e_cond t' b exp1 exp2)
.

(* does this statement respect the usage of varname s to denote a type t? *)
(* XXX note that in both of these, non-usage counts as respectful! *)
Inductive StmtVarRespectsT (t : type) (s : varidtype) : stmt -> Prop :=
| svrt_block_nil : StmtVarRespectsT t s (s_block [])
| svrt_block_cons : forall st sts,
    StmtVarRespectsT t s st -> StmtVarRespectsT t s (s_block sts) ->
    StmtVarRespectsT t s (s_block (st :: sts))
| svrt_start : forall pt p e,
    ExprVarRespectsT t s pt e -> StmtVarRespectsT t s (s_start pt p e)
| svrt_assign_eq : forall e,
    ExprVarRespectsT t s t e -> StmtVarRespectsT t s (s_assign t (mkvar t s) e)
| svrt_assign_neq : forall t' s' e,
    s <> s' -> ExprVarRespectsT t s t' e -> StmtVarRespectsT t s (s_assign t' (mkvar t' s') e)
| svrt_load_eq : forall l,
    StmtVarRespectsT t s (s_load t (mkvar t s) l)
| svrt_load_neq : forall t' s' l,
    s <> s' -> StmtVarRespectsT t s (s_load t' (mkvar t' s') l)
| svrt_scope : forall s1,
    StmtVarRespectsT t s s1 ->
    StmtVarRespectsT t s (s_scope s1)
| svrt_if : forall b s1 s2,
    ExprVarRespectsT t s t_bool b -> StmtVarRespectsT t s s1 -> StmtVarRespectsT t s s2 ->
    StmtVarRespectsT t s (s_if b s1 s2)
| svrt_while : forall b st,
    ExprVarRespectsT t s t_bool b -> StmtVarRespectsT t s st -> StmtVarRespectsT t s (s_while b st)
| svrt_call_eq : forall pt p exp,
    ExprVarRespectsT t s pt exp -> StmtVarRespectsT t s (s_call pt t (mkvar t s) p exp)
| svrt_call_neq : forall t' s' pt p exp,
    s <> s' -> ExprVarRespectsT t s pt exp -> StmtVarRespectsT t s (s_call pt t' (mkvar t' s') p exp)
| svrt_local_eq : forall e,
    ExprVarRespectsT t s t e -> StmtVarRespectsT t s (s_local t (mkvar t s) e)
| svrt_local_neq : forall t' s' e,
    s <> s' -> ExprVarRespectsT t s t' e -> StmtVarRespectsT t s (s_local t' (mkvar t' s') e)
| svrt_return : forall t' e,
    ExprVarRespectsT t s t' e -> StmtVarRespectsT t s (s_return t' e)
(* XXX *)
| svrt_getlock : forall t' l,
    StmtVarRespectsT t s (s_getlock t' l)
| svrt_putlock : forall t' l,
    StmtVarRespectsT t s (s_putlock t' l)
.
(* inspect to see that the constructor types were inferred properly *)
(* Print StmtVarRespectsT. *)

(* does a proc respect variable usage? *)
Inductive ProcVarRespectsT pt rt: proc pt rt -> Prop :=
| pvrt : forall s st,
    StmtVarRespectsT pt s st ->
    (forall t s, InStmt t (mkvar t s) st -> StmtVarRespectsT t s st) ->
    ProcVarRespectsT pt rt (mkproc pt rt (mkvar pt s) st)
.


Definition StmtOk s : Prop :=
   (forall env env', VarsScopedStmt env s env') /\
   (forall env', VarsUniqueStmt s env')
.

Definition ProcOk pt rt (p: proc pt rt): Prop :=
   (VarsScopedProc pt rt p) /\
   (VarsUniqueProc pt rt p) /\
   ProcReturnOk pt rt p
.
