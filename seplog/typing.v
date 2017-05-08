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
(*                            typing                            *)
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

(*
 * scoping
 *)

Inductive VarsScopedExpr: forall (t: type), VarMap type -> expr -> Prop :=
| vars_scoped_value: forall (t: type) env k,
     type_of_value k = t ->
     VarsScopedExpr t env (e_value t k)
| vars_scoped_read: forall (t: type) env id,
     VarMapMapsTo (mkvar t id) t env ->
     VarsScopedExpr t env (e_read (mkvar t id))
| vars_scoped_cond: forall t env pred te fe,
     VarsScopedExpr t_bool env pred ->
     VarsScopedExpr t env te ->
     VarsScopedExpr t env fe ->
     VarsScopedExpr t env (e_cond t pred te fe)
.

Inductive VarsScopedStmt: VarMap type -> stmt -> Prop :=
| vars_scoped_skip: forall env,
     VarsScopedStmt env s_skip
| vars_scoped_seq: forall env s1 s2,
     VarsScopedStmt env s1 ->
     VarsScopedStmt env s2 ->
     VarsScopedStmt env (s_seq s1 s2)
| vars_scoped_start: forall env pt p e,
     VarsScopedProc pt t_unit p ->
     VarsScopedExpr pt env e ->
     VarsScopedStmt env (s_start p e)
| vars_scoped_assign: forall t env id e,
     VarsScopedExpr t env e ->
     VarMapMapsTo (mkvar t id) t env ->
     VarsScopedStmt env (s_assign (mkvar t id) e)
| vars_scoped_load: forall t env id e,
     VarsScopedExpr (t_addr t) env e ->
     VarMapMapsTo (mkvar t id) t env ->
     VarsScopedStmt env (s_load (mkvar t id) e)
| vars_scoped_store: forall t env lid e,
     VarMapMapsTo (mkvar (t_addr t) lid) (t_addr t) env ->
     VarsScopedExpr t env e ->
     VarsScopedStmt env (s_store (mkvar (t_addr t) lid) e)
| vars_scoped_if: forall env pred ts fs,
     VarsScopedExpr t_bool env pred ->
     VarsScopedStmt env ts ->
     VarsScopedStmt env fs ->
     VarsScopedStmt env (s_if pred ts fs)
| vars_scoped_while: forall env pred body,
     VarsScopedExpr t_bool env pred ->
     VarsScopedStmt env body ->
     VarsScopedStmt env (s_while pred body)
| vars_scoped_call: forall env pt rt id p arg,
     VarsScopedProc pt rt p ->
     VarsScopedExpr pt env arg ->
     VarMapMapsTo (mkvar rt id) rt env ->
     VarsScopedStmt env (s_call (mkvar rt id) p arg)
| vars_scoped_return: forall t env e,
     (* XXX this doesn't check against the proc type... *)
     VarsScopedExpr t env e ->
     VarsScopedStmt env (s_return e)
| vars_scoped_getlock: forall t env id,
     VarsScopedStmt env (s_getlock (mkvar (t_lock t) id))
| vars_scoped_putlock: forall t env id,
     VarsScopedStmt env (s_getlock (mkvar (t_lock t) id))
with

(*Inductive*) VarsScopedVardecl: VarMap type -> vardecl ->
                                 VarMap type -> Prop :=
| vars_scoped_vardecl: forall t env id e,
     VarsScopedExpr t env e ->
     ~(VarMapIn (mkvar t id) env) ->
     VarsScopedVardecl env (mkvardecl (mkvar t id) e) (VarMap_add (mkvar t id) t env)
with

(*Inductive*) VarsScopedVardecls: VarMap type -> list vardecl ->
                                  VarMap type -> Prop :=
| vars_scoped_vardecls_nil: forall env,
     VarsScopedVardecls env [] env
| vars_scoped_vardecls_cons: forall env decl env' decls env'',
     VarsScopedVardecl env decl env' ->
     VarsScopedVardecls env' decls env'' ->
     VarsScopedVardecls env (decl :: decls) env''
with

(*Inductive*) VarsScopedProc: forall pt rt, proc -> Prop :=
| vars_scoped_proc: forall pt rt id decls body env,
     VarsScopedVardecls (VarMap_add (mkvar pt id) pt (VarMap_empty type))
                        decls env ->
     VarsScopedStmt env body ->
     VarsScopedProc pt rt (mkproc rt (mkvar pt id) decls body)
.


(*
 * uniqueness
 *)

(*
 * This differs in that the environment doesn't nest. Also,
 * it doesn't reason about exprs; it relies on VarsScoped to
 * make sure they refer only to variables that exist.
 *)

Inductive VarsUniqueStmt: stmt -> VarMap unit -> Prop :=
| vars_unique_skip:
     VarsUniqueStmt s_skip (VarMap_empty unit)
| vars_unique_seq: forall s1 env s2 env',
     VarsUniqueStmt s1 env ->
     VarsUniqueStmt s2 env' ->
     VarMapDisjoint unit env env' ->
     VarsUniqueStmt (s_seq s1 s2) (VarMap_union env env')
| vars_unique_start: forall p e,
     VarsUniqueProc p ->
     VarsUniqueStmt (s_start p e) (VarMap_empty unit)
| vars_unique_assign: forall x e,
     VarsUniqueStmt (s_assign x e) (VarMap_empty unit)
| vars_unique_load: forall x l,
     VarsUniqueStmt (s_load x l) (VarMap_empty unit)
| vars_unique_store: forall l e,
     VarsUniqueStmt (s_store l e) (VarMap_empty unit)
| vars_unique_if: forall pred ts fs env't env'f,
     VarsUniqueStmt ts env't ->
     VarsUniqueStmt fs env'f ->
     VarMapDisjoint unit env't env'f ->
     VarsUniqueStmt (s_if pred ts fs) (VarMap_union env't env'f)
| vars_unique_while: forall cond body env'body,
     VarsUniqueStmt body env'body ->
     VarsUniqueStmt (s_while cond body) env'body
| vars_unique_call: forall x p arg,
     VarsUniqueProc p ->
     VarsUniqueStmt (s_call x p arg) (VarMap_empty unit)
| vars_unique_return: forall e,
     VarsUniqueStmt (s_return e) (VarMap_empty unit)
| vars_unique_getlock: forall t id,
     VarsUniqueStmt (s_getlock (mkvar (t_lock t) id)) (VarMap_empty unit)
| vars_unique_putlock: forall t id,
     VarsUniqueStmt (s_getlock (mkvar (t_lock t) id)) (VarMap_empty unit)
with

(*Inductive*) VarsUniqueVardecls: list vardecl -> VarMap unit -> Prop :=
| vars_unique_vardecls_nil:
     VarsUniqueVardecls [] (VarMap_empty unit)
| vars_unique_vardecls_cons: forall x e env0 decls env,
     env0 = VarMap_add x tt(*unit*) (VarMap_empty unit) ->
     VarsUniqueVardecls decls env ->
     VarMapDisjoint unit env0 env ->
     VarsUniqueVardecls ((mkvardecl x e) :: decls) (VarMap_union env0 env)
with

(*Inductive*) VarsUniqueProc: proc -> Prop :=
| vars_unique_proc: forall rt x decls body env_a env_d env_b,
     env_a = (VarMap_add x tt(*unit*) (VarMap_empty unit)) ->
     VarsUniqueVardecls decls env_d ->
     VarMapDisjoint unit env_a env_d ->
     VarsUniqueStmt body env_b ->
     VarMapDisjoint unit env_a env_b ->
     VarMapDisjoint unit env_d env_b ->
     VarsUniqueProc (mkproc rt x decls body)
.


(* check that procedure returns are ok *)

Inductive StmtEndsInReturn: stmt -> type -> Prop :=
| block_ends_in_return: forall s t e,
     StmtEndsInReturn (s_seq s (s_return e)) t
| if_ends_in_return: forall s1 s2 t e,
     StmtEndsInReturn s1 t -> StmtEndsInReturn s2 t ->
     StmtEndsInReturn (s_if e s1 s2) t
| return_ends_in_return: forall t e,
     StmtEndsInReturn (s_return e) t
with
(*Inductive*) ProcReturnOk: forall rt, proc -> Prop :=
| proc_return_ok: forall rt param decls body,
     StmtEndsInReturn body rt ->
     ProcReturnOk rt (mkproc rt param decls body)
.




Definition StmtOk s : Prop :=
   (forall env, VarsScopedStmt env s) /\
   (forall env, VarsUniqueStmt s env)
.

Definition ProcOk pt rt (p: proc): Prop :=
   (VarsScopedProc pt rt p) /\
   (VarsUniqueProc p) /\
   ProcReturnOk rt p
.
