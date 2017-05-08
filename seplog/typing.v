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
 * we have the following major constraints:
 *   1. scoping: variables must be used only in their scope and not
 *      redefined when in scope.
 *   2. uniqueness: (local) variable identifiers must be unique across
 *      each entire proc. Nowadays this is an immediate consequence of #1.
 *   3. flow: variables must be declared before used.
 *   4. typing: each local variable has exactly one type.
 *
 * These are all now covered by the *Typed props.
 *
 * We have the additional constraint that the body of a proc must
 * end in a return so that the proc can't fall of the end without
 * providing a return value. (In principle the end could also be
 * unreachable, or the proc could always diverge, but we don't try
 * to reason about those cases.)
 *)

(*
 * scoping
 *)

Inductive ExprTyped: forall (t: type), VarMap type -> expr -> Prop :=
| e_value_typed: forall (t: type) env k,
     type_of_value k = t ->
     ExprTyped t env (e_value t k)
| e_read_typed: forall (t: type) env id,
     VarMapMapsTo (mkvar t id) t env ->
     ExprTyped t env (e_read (mkvar t id))
| e_cond_typed: forall t env pred te fe,
     ExprTyped t_bool env pred ->
     ExprTyped t env te ->
     ExprTyped t env fe ->
     ExprTyped t env (e_cond t pred te fe)
.

Inductive StmtTyped: VarMap type -> stmt -> Prop :=
| s_skip_typed: forall env,
     StmtTyped env s_skip
| s_seq_typed: forall env s1 s2,
     StmtTyped env s1 ->
     StmtTyped env s2 ->
     StmtTyped env (s_seq s1 s2)
| s_start_typed: forall env pt p e,
     ProcTyped pt t_unit p ->
     ExprTyped pt env e ->
     StmtTyped env (s_start p e)
| s_assign_typed: forall t env id e,
     ExprTyped t env e ->
     VarMapMapsTo (mkvar t id) t env ->
     StmtTyped env (s_assign (mkvar t id) e)
| s_load_typed: forall t env id e,
     ExprTyped (t_addr t) env e ->
     VarMapMapsTo (mkvar t id) t env ->
     StmtTyped env (s_load (mkvar t id) e)
| s_store_typed: forall t env lid e,
     VarMapMapsTo (mkvar (t_addr t) lid) (t_addr t) env ->
     ExprTyped t env e ->
     StmtTyped env (s_store (mkvar (t_addr t) lid) e)
| s_if_typed: forall env pred ts fs,
     ExprTyped t_bool env pred ->
     StmtTyped env ts ->
     StmtTyped env fs ->
     StmtTyped env (s_if pred ts fs)
| s_while_typed: forall env pred body,
     ExprTyped t_bool env pred ->
     StmtTyped env body ->
     StmtTyped env (s_while pred body)
| s_call_typed: forall env pt rt id p arg,
     ProcTyped pt rt p ->
     ExprTyped pt env arg ->
     VarMapMapsTo (mkvar rt id) rt env ->
     StmtTyped env (s_call (mkvar rt id) p arg)
| s_return_typed: forall t env e,
     (* XXX this doesn't check against the proc type... *)
     ExprTyped t env e ->
     StmtTyped env (s_return e)
| s_getlock_typed: forall t env id,
     StmtTyped env (s_getlock (mkvar (t_lock t) id))
| s_putlock_typed: forall t env id,
     StmtTyped env (s_getlock (mkvar (t_lock t) id))
with

(*Inductive*) VardeclTyped: VarMap type -> vardecl ->
                                 VarMap type -> Prop :=
| vardecl_typed: forall t env id e,
     ExprTyped t env e ->
     ~(VarMapIn (mkvar t id) env) ->
     VardeclTyped env (mkvardecl (mkvar t id) e) (VarMap_add (mkvar t id) t env)
with

(*Inductive*) VardeclsTyped: VarMap type -> list vardecl ->
                                  VarMap type -> Prop :=
| vardecls_nil_typed: forall env,
     VardeclsTyped env [] env
| vardecls_cons_typed: forall env decl env' decls env'',
     VardeclTyped env decl env' ->
     VardeclsTyped env' decls env'' ->
     VardeclsTyped env (decl :: decls) env''
with

(*Inductive*) ProcTyped: forall pt rt, proc -> Prop :=
| proc_typed: forall pt rt id decls body env,
     VardeclsTyped (VarMap_add (mkvar pt id) pt (VarMap_empty type))
                        decls env ->
     StmtTyped env body ->
     ProcTyped pt rt (mkproc rt (mkvar pt id) decls body)
.



(* check that procedure returns are ok *)

Inductive StmtEndsInReturn: stmt -> type -> Prop :=
| seq_ends_in_return: forall s t e,
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



(* this is of questionable merit *)
Definition StmtOk s : Prop :=
   forall env, StmtTyped env s
.

Definition ProcOk pt rt (p: proc): Prop :=
   (ProcTyped pt rt p) /\
   ProcReturnOk rt p
.
