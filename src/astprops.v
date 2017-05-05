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
Inductive VarsScopedExpr: forall (t: Type), VarMap Type -> Expr t -> Prop :=
| vars_scoped_value: forall (t: Type) env k,
     VarsScopedExpr t env (value t k)
| vars_scoped_read: forall (t: Type) env id,
     VarMapMapsTo (var t id) t env ->
     VarsScopedExpr t env (read t (var t id))
| vars_scoped_cond: forall t env pred te fe,
     VarsScopedExpr bool env pred ->
     VarsScopedExpr t env te ->
     VarsScopedExpr t env fe ->
     VarsScopedExpr t env (cond t pred te fe)
.

Inductive VarsScopedStmt: VarMap Type -> Stmt -> VarMap Type -> Prop :=
| vars_scoped_block_nil: forall env,
     VarsScopedStmt env (block []) env
| vars_scoped_block_cons: forall env s env' ss env'',
     VarsScopedStmt env s env' ->
     VarsScopedStmt env' (block ss) env'' ->
     VarsScopedStmt env (block (s :: ss)) env''
| vars_scoped_start: forall env pt p e,
     VarsScopedExpr pt env e ->
     VarsScopedStmt env (start pt p e) env
| vars_scoped_assign: forall t env id e,
     VarsScopedExpr t env e ->
     VarMapMapsTo (var t id) t env ->
     VarsScopedStmt env (assign t (var t id) e) env
| vars_scoped_load: forall t env id l,
     VarMapMapsTo (var t id) t env ->
     VarsScopedStmt env (load t (var t id) l) env
| vars_scoped_store: forall t env id l e,
     @VarMapMapsTo t Type (var t id) t env ->
     VarsScopedExpr t env e ->
     VarsScopedStmt env (store t l e) env
| vars_scoped_scope: forall env s env',
     VarsScopedStmt env s env' ->
     VarsScopedStmt env (scope s) env
| vars_scoped_if: forall env pred ts fs env't env'f,
     VarsScopedExpr bool env pred ->
     VarsScopedStmt env ts env't ->
     VarsScopedStmt env fs env'f ->
     VarsScopedStmt env (if_ pred ts fs) env
| vars_scoped_while: forall env pred body env'body,
     VarsScopedExpr bool env pred ->
     VarsScopedStmt env body env'body ->
     VarsScopedStmt env (while pred body) env
| vars_scoped_call: forall env pt rt id p arg,
     VarsScopedProc pt rt p ->
     VarsScopedExpr pt env arg ->
     VarMapMapsTo (var rt id) rt env ->
     VarsScopedStmt env (call pt rt (var rt id) p arg) env
| vars_scoped_local: forall t env id e,
     VarsScopedExpr t env e ->
     ~(VarMapIn (var t id) env) ->
     VarsScopedStmt env (local t (var t id) e) (VarMap_add (var t id) t env)
| vars_scoped_return: forall t env e,
     VarsScopedExpr t env e ->
     VarsScopedStmt env (return_ t e) env
| vars_scoped_getlock: forall t env l,
     VarsScopedStmt env (getlock t l) env
| vars_scoped_putlock: forall t env l,
     VarsScopedStmt env (getlock t l) env
with
(*Inductive*) VarsScopedProc: forall pt rt, Proc pt rt -> Prop :=
| vars_scoped_proc: forall pt rt id body env',
     VarsScopedStmt (VarMap_add (var pt id) pt (VarMap_empty Type)) body env' ->
     VarsScopedProc pt rt (proc pt rt (var pt id) body)
.

(* uniqueness *)

(*
 * This differs in that the environment doesn't nest. Also,
 * it doesn't reason about exprs; it relies on VarsScoped to
 * make sure they refer only to variables that exist.
 *)

Inductive VarsUniqueStmt: Stmt -> VarMap unit -> Prop :=
| vars_unique_block_nil:
     VarsUniqueStmt (block []) (VarMap_empty unit)
| vars_unique_block_cons: forall s env ss env',
     VarsUniqueStmt s env ->
     VarsUniqueStmt (block ss) env' ->
     VarMapDisjoint unit env env' ->
     VarsUniqueStmt (block (s :: ss)) (VarMap_union env env')
| vars_unique_start: forall pt p e,
     VarsUniqueStmt (start pt p e) (VarMap_empty unit)
| vars_unique_assign: forall t x e,
     VarsUniqueStmt (assign t x e) (VarMap_empty unit)
| vars_unique_load: forall t x l,
     VarsUniqueStmt (load t x l) (VarMap_empty unit)
| vars_unique_store: forall t l e,
     VarsUniqueStmt (store t l e) (VarMap_empty unit)
| vars_unique_if: forall pred ts fs env't env'f,
     VarsUniqueStmt ts env't ->
     VarsUniqueStmt fs env'f ->
     VarMapDisjoint unit env't env'f ->
     VarsUniqueStmt (if_ pred ts fs) (VarMap_union env't env'f)
| vars_unique_while: forall cond body env'body,
     VarsUniqueStmt body env'body ->
     VarsUniqueStmt (while cond body) env'body
| vars_unique_call: forall pt rt x p arg,
     VarsUniqueProc pt rt p ->
     VarsUniqueStmt (call pt rt x p arg) (VarMap_empty unit)
| vars_unique_local: forall t x e,
     VarsUniqueStmt (local t x e) (VarMap_add x tt(*unit*) (VarMap_empty unit))
| vars_unique_return: forall t e,
     VarsUniqueStmt (return_ t e) (VarMap_empty unit)
| vars_unique_getlock: forall t l,
     VarsUniqueStmt (getlock t l) (VarMap_empty unit)
| vars_unique_putlock: forall t l,
     VarsUniqueStmt (getlock t l) (VarMap_empty unit)
with
(*Inductive*) VarsUniqueProc: forall pt rt, Proc pt rt -> Prop :=
| vars_unique_proc: forall pt rt x body env',
     VarMapDisjoint unit (VarMap_add x tt(*unit*) (VarMap_empty unit)) env' ->
     VarsUniqueStmt body env' ->
     VarsUniqueProc pt rt (proc pt rt x body)
.


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
(*Inductive*) ProcReturnOk: forall pt rt, Proc pt rt -> Prop :=
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
Inductive ExprVarRespectsT (t : Type) (s : string) : forall t', Expr t' -> Prop :=
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
Inductive StmtVarRespectsT (t : Type) (s : string) : Stmt -> Prop :=
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
| svrt_scope : forall s1,
    StmtVarRespectsT t s s1 ->
    StmtVarRespectsT t s (scope s1)
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
Inductive ProcVarRespectsT pt rt: Proc pt rt -> Prop :=
| pvrt : forall s st,
    StmtVarRespectsT pt s st ->
    (forall t s, InStmt t (var t s) st -> StmtVarRespectsT t s st) ->
    ProcVarRespectsT pt rt (proc pt rt (var pt s) st)
.


Definition StmtOk s : Prop :=
   (forall env env', VarsScopedStmt env s env') /\
   (forall env', VarsUniqueStmt s env')
.

Definition ProcOk pt rt (p: Proc pt rt): Prop :=
   (VarsScopedProc pt rt p) /\
   (VarsUniqueProc pt rt p) /\
   ProcReturnOk pt rt p
.
