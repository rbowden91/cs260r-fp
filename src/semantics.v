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

(**************************************************************)	
(* stores *)

Section Stores.

(* old form that used coq types directly
Inductive val: Type := mkval (t: Type) (a : t): val.

Definition Heap := NatMap.t val.
Definition Locals := NatMap.t val.
*)

(* XXX kill this off *)
Inductive val: Type := mkval (t: type) (a : value): val.

Definition Heap := NatMap.t val.
Definition Locals := NatMap.t val.

End Stores.

(**************************************************************)	
(* expressions *)

Section Expressions.

Inductive ExprYields: forall t, Locals -> expr -> value -> Prop :=
| value_yields: forall loc t a,
    ExprYields t loc (e_value t a) a
| read_yields: forall loc t (x : var) id a,
    (* XXX tidy this *)
    type_of_value a = t ->
    x = mkvar t id -> NatMap.find id loc = Some (mkval t a) ->
    ExprYields t loc (e_read x) a
| cond_true_yields: forall t loc e et ef a,
    ExprYields t_bool loc e v_true ->
    ExprYields t loc et a ->
    ExprYields t loc (e_cond t e et ef) a
| cond_false_yields: forall t loc e et ef a,
    ExprYields t_bool loc e v_false ->
    ExprYields t loc ef a ->
    ExprYields t loc (e_cond t e et ef) a
.

End Expressions.

(**************************************************************)	
(* statements *)

Section Statements.

(* call, return, and start appear at higher levels *)
Inductive StmtSteps: Heap -> Locals -> stmt -> Heap -> Locals -> stmt -> Prop :=
| step_in_seq: forall h loc s1 s2 h' loc' s1',
     StmtSteps h loc s1 h' loc' s1' ->
     StmtSteps h loc (s_seq s1 s2) h' loc' (s_seq s1' s2)
| step_next: forall h loc s2,
     StmtSteps h loc (s_seq s_skip s2) h loc s2
| step_assign: forall h loc id type e a,
     ExprYields type loc e a ->
     StmtSteps h loc (s_assign (mkvar type id) e) h (NatMap.add id (mkval type a) loc) s_skip
| step_load: forall h loc type lid e hid heapnum a,
     (* XXX this is wrong (needs to handle heapnum) *)
     ExprYields type loc e (v_addr (mkaddr type hid heapnum)) ->
     NatMap.find hid h = Some (mkval type a) ->
     StmtSteps h loc (s_load (mkvar type lid) e) h (NatMap.add lid (mkval type a) loc) s_skip
| step_store: forall h loc type lid e hid heapnum a,
     (* XXX this is wrong (needs to handle heapnum) *)
     ExprYields type loc e a ->
     ExprYields type loc (e_read (mkvar type lid)) (v_addr (mkaddr type hid heapnum)) ->
     StmtSteps h loc (s_store (mkvar type lid) e) (NatMap.add hid (mkval type a) h) loc s_skip
| step_scope: forall h loc s h' loc' s',
     StmtSteps h loc s h' loc' s' ->
     StmtSteps h loc (s_scope s) h' loc' (s_scope s')
| step_endscope: forall h loc,
     StmtSteps h loc (s_scope s_skip) h loc s_skip
| step_if_true: forall h loc e st sf,
     ExprYields t_bool loc e v_true ->
     StmtSteps h loc (s_if e st sf) h loc (s_scope st)
| step_if_false: forall h loc e st sf,
     ExprYields t_bool loc e v_false ->
     StmtSteps h loc (s_if e st sf) h loc (s_scope sf)
| step_while_true: forall h loc e body,
     ExprYields t_bool loc e v_true ->
     StmtSteps h loc (s_while e body)
               h loc (s_seq (s_scope body) (s_while e body))
| step_while_false: forall h loc e body,
     ExprYields t_bool loc e v_false ->
     StmtSteps h loc (s_while e body) h loc s_skip
| step_local: forall h loc id type e a,
     NatMap.find id loc = None ->
     ExprYields type loc e a ->
     StmtSteps h loc (s_local (mkvar type id) e) h (NatMap.add id (mkval type a) loc) s_skip
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
| stack_pending: forall (t : type), Locals -> var -> Stack -> Stack
.

Inductive CallSteps: Stack -> Locals -> stmt ->
                     Stack -> Locals -> stmt -> Prop :=
| call_steps: forall loc stk retid rt paramid pt body arg argval,
     ExprYields pt loc arg argval ->
     CallSteps stk loc (s_call (mkvar rt retid)
                               (mkproc rt (mkvar pt paramid) body)
                               arg)
               (stack_pending rt loc (mkvar rt retid) stk)
               (NatMap.add paramid (mkval pt argval) (NatMap.empty val))
               body
.

Inductive ReturnSteps: Stack -> Locals -> stmt ->
                        Stack -> Locals -> stmt -> Prop :=
| return_steps: forall loc loc' rt retid stk ret retval,
     ExprYields rt loc ret retval ->
     ReturnSteps (stack_pending rt loc' (mkvar rt retid) stk) loc
                                                              (s_return ret)
                 stk loc' (s_assign (mkvar rt retid) (e_value rt retval))
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
| thread_steps_call_final: forall h loc stk s loc' stk' s',
     CallSteps stk loc s stk' loc' s' ->
     ThreadSteps h (thread loc stk s)
		 h (thread loc' stk' s')
| thread_steps_call_seq: forall h loc stk s s2 loc' stk' s',
     CallSteps stk loc s stk' loc' s' ->
     ThreadSteps h (thread loc stk (s_seq s s2))
		 h (thread loc' stk' (s_seq s' s2))
| thread_steps_return_final: forall h loc stk s loc' stk' s',
     ReturnSteps stk loc s stk' loc' s' ->
     ThreadSteps h (thread loc stk s)
		 h (thread loc' stk' s')
| thread_steps_return_seq: forall h loc stk s s2 loc' stk' s',
     ReturnSteps stk loc s stk' loc' s' ->
     ThreadSteps h (thread loc stk (s_seq s s2))
		 h (thread loc' stk' s')
.

(* this is its own thing because it needs a different signature *)
Inductive ThreadStepsStart: Thread -> Thread -> Thread -> Prop :=
| thread_steps_start: forall loc stk pt paramid body arg argval,
     ExprYields pt loc arg argval ->
     ThreadStepsStart
	(thread loc stk (s_start (mkproc t_unit (mkvar pt paramid) body) arg))
        (thread loc stk s_skip)
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
