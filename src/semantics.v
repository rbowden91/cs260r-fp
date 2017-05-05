Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Import ListNotations.

Require Import OrderedType OrderedTypeEx.
Require FMapList.
Require FMapFacts.
Module NatMap := FMapList.Make Nat_as_OT.
Module NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.

(* ffs there is no standard instance for this *)
Require Import string_as_ot.
Module StringMap := FMapList.Make String_as_OT.
Module StringMapFacts := FMapFacts.WFacts_fun String_as_OT StringMap.

Require Import ast.

(* ************************************************************ *)
(* ************************************************************ *)
(*                                                              *)
(*                          semantics                           *)
(*                                                              *)
(* ************************************************************ *)	
(* ************************************************************ *)

(*
 * We define the semantics in terms of an abstract machine, which
 * includes the evaluation state as well as the program.
 *
 * A machine has a heap and a list of threads.
 * A thread is a lits of stack frames.
 * A stack frame is a local store plus a statement to execute.
 *
 * Statements are executed destructively.
 *)

(* XXX placeholders *)
Hypotheses addr_from_lock: forall t, lock t -> nat.

(**************************************************************)	
(* stores *)

Section Stores.

Inductive val: Type := mkval (t: Type) (a : t): val.

Definition Heap := NatMap.t val.
Definition Locals := NatMap.t val.

End Stores.

(**************************************************************)	
(* expressions *)

Section Expressions.

Inductive ExprYields: forall t, Locals -> expr t -> t -> Prop :=
| value_yields: forall loc t a, ExprYields t loc (value t a) a
| read_yields: forall loc t (x : var t) id a,
    x = mkvar t id -> NatMap.find id loc = Some (mkval t a) ->
    ExprYields t loc (read t x) a
| cond_true_yields: forall t loc e et ef a,
    ExprYields bool loc e true ->
    ExprYields t loc et a ->
    ExprYields t loc (cond t e et ef) a
| cond_false_yields: forall t loc e et ef a,
    ExprYields bool loc e false ->
    ExprYields t loc ef a ->
    ExprYields t loc (cond t e et ef) a
.

End Expressions.

(**************************************************************)	
(* statements *)

Section Statements.

(* call, return, and start appear at higher levels *)
Inductive StmtSteps: Heap -> Locals -> stmt -> Heap -> Locals -> stmt -> Prop :=
| step_in_block: forall h loc s h' loc' s' more,
     StmtSteps h loc s h' loc' s' ->
     StmtSteps h loc (block (s :: more)) h' loc' (block (s' :: more))
| step_next: forall h loc more,
     StmtSteps h loc (block (skip :: more)) h loc (block more)
| step_assign: forall h loc id type e a,
     ExprYields type loc e a ->
     StmtSteps h loc (assign type (mkvar type id) e) h (NatMap.add id (mkval type a) loc) skip
| step_load: forall h loc id type inv lk addr a,
     lk = mklock type inv -> addr_from_lock type lk = addr -> (* XXX *)
     NatMap.find addr h = Some (mkval type a) ->
     StmtSteps h loc (load type (mkvar type id) lk) h (NatMap.add id (mkval type a) loc) skip
| step_store: forall h loc type inv lk addr e a,
     lk = mklock type inv -> addr_from_lock type lk = addr -> (* XXX *)
     ExprYields type loc e a ->
     StmtSteps h loc (store type lk e) (NatMap.add addr (mkval type a) h) loc skip
| step_scope: forall h loc s h' loc' s',
     StmtSteps h loc s h' loc' s' ->
     StmtSteps h loc (scope s) h' loc' (scope s')
| step_endscope: forall h loc,
     StmtSteps h loc (scope skip) h loc skip
| step_if_true: forall h loc e st sf,
     ExprYields bool loc e true ->
     StmtSteps h loc (if_ e st sf) h loc (scope st)
| step_if_false: forall h loc e st sf,
     ExprYields bool loc e false ->
     StmtSteps h loc (if_ e st sf) h loc (scope sf)
| step_while_true: forall h loc e body,
     ExprYields bool loc e true ->
     StmtSteps h loc (while e body)
               h loc (block [scope body; while e body])
| step_while_false: forall h loc e body,
     ExprYields bool loc e false ->
     StmtSteps h loc (while e body) h loc skip
| step_local: forall h loc id type e a,
     NatMap.find id loc = None ->
     ExprYields type loc e a ->
     StmtSteps h loc (local type (mkvar type id) e) h (NatMap.add id (mkval type a) loc) skip
(* XXX
| step_getlock: ?
| step_putlock: ?
*)
.

End Statements.

(**************************************************************)
(* stacks *)

Section Stacks.

Inductive Stack: Type :=
| stack_empty: Stack
| stack_pending: forall t, Locals -> var t -> Stack -> Stack
.

End Stacks.

(**************************************************************)	
(* threads *)

Section Threads.

Inductive Thread: Type :=
| thread: Locals -> Stack -> stmt -> Thread
.

Inductive ThreadSteps: Heap -> Thread -> Heap -> Thread -> Prop :=
| thread_steps_stmt: forall h loc stk s h' loc' s',
     StmtSteps h loc s h' loc' s' ->
     ThreadSteps h (thread loc stk s) h' (thread loc' stk s')
| thread_steps_call: forall h loc stk retid rt paramid pt body arg argval,
     ExprYields pt loc arg argval ->
     ThreadSteps h (thread
			loc
			stk
			(call pt rt
				(mkvar rt retid)
				(mkproc pt rt (mkvar pt paramid) body)
				arg)
		 )
		 h (thread
			(NatMap.add paramid (mkval pt argval) (NatMap.empty val))
			(stack_pending rt loc (mkvar rt retid) stk)
			body
		 )
| thread_steps_return: forall h loc loc' rt retid stk ret retval retvalXXX,
     ExprYields rt loc ret retval ->
     ThreadSteps h (thread loc (stack_pending rt loc' (mkvar rt retid) stk) (return_ rt ret))
                 h (thread loc' stk (assign rt (mkvar rt retid) (value rt retvalXXX)))
.

(* this is its own thing because it needs a different signature *)
Inductive ThreadStepsStart: Thread -> Thread -> Thread -> Prop :=
| thread_steps_start: forall loc stk pt paramid body arg argval,
     ExprYields pt loc arg argval ->
     ThreadStepsStart
	(thread loc stk (start pt (mkproc pt unit (mkvar pt paramid) body) arg))
        (thread loc stk skip)
	(thread (NatMap.add paramid (mkval pt argval) (NatMap.empty val)) stack_empty body)
.

End Threads.

(**************************************************************)	
(* machines *)

Section Machines.

Inductive Machine: Type :=
| machine: Heap -> list Thread -> Machine
.

Inductive MachineSteps: Machine -> Machine -> Prop :=
| machine_steps_plain: forall h t h' t' ts1 ts2,
     ThreadSteps h t h' t' ->
     MachineSteps (machine h (ts1 ++ [t] ++ ts2))
		  (machine h' (ts1 ++ [t'] ++ ts2))
| machine_steps_start: forall h t t1 t2 ts1 ts2,
     ThreadStepsStart t t1 t2 ->
     MachineSteps (machine h (ts1 ++ [t] ++ ts2))
		  (machine h (ts1 ++ [t1; t2] ++ ts2))
.

End Machines.
