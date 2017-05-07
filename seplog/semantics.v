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

Definition Heap := NatMap.t value.
Definition Locals := NatMap.t value.

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
    x = mkvar t id -> NatMap.find id loc = Some a ->
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
     StmtSteps h loc (s_assign (mkvar type id) e) h (NatMap.add id a loc) s_skip
| step_load: forall h loc type lid e hid heapnum a,
     (* XXX this is wrong (needs to handle heapnum) *)
     ExprYields type loc e (v_addr (mkaddr type hid heapnum)) ->
     NatMap.find hid h = Some a ->
     StmtSteps h loc (s_load (mkvar type lid) e) h (NatMap.add lid a loc) s_skip
| step_store: forall h loc type lid e hid heapnum a,
     (* XXX this is wrong (needs to handle heapnum) *)
     ExprYields type loc e a ->
     ExprYields type loc (e_read (mkvar type lid)) (v_addr (mkaddr type hid heapnum)) ->
     StmtSteps h loc (s_store (mkvar type lid) e) (NatMap.add hid a h) loc s_skip
| step_if_true: forall h loc e st sf,
     ExprYields t_bool loc e v_true ->
     StmtSteps h loc (s_if e st sf) h loc st
| step_if_false: forall h loc e st sf,
     ExprYields t_bool loc e v_false ->
     StmtSteps h loc (s_if e st sf) h loc sf
| step_while_true: forall h loc e body,
     ExprYields t_bool loc e v_true ->
     StmtSteps h loc (s_while e body)
               h loc (s_seq body (s_while e body))
| step_while_false: forall h loc e body,
     ExprYields t_bool loc e v_false ->
     StmtSteps h loc (s_while e body) h loc s_skip
(* XXX
| step_getlock: ?
| step_putlock: ?
*)
.

End Statements.

(**************************************************************)
(* vardecls *)

Section Vardecls.

Inductive VardeclsSteps: Locals -> list vardecl -> Locals -> Prop :=
| vardecls_steps_nil: forall loc,
     VardeclsSteps loc [] loc
| vardecls_steps_cons: forall loc t id e a decls loc',
     ExprYields t loc e a ->
     VardeclsSteps (NatMap.add id a loc) decls loc' ->
     VardeclsSteps loc ((mkvardecl (mkvar t id) e) :: decls) loc'
.

End Vardecls.

(**************************************************************)
(* stacks *)

Section Stacks.

Inductive Stack: Type :=
| stack_empty: Stack
| stack_pending: Locals -> Stack -> stmt -> Stack
| stack_top: Locals -> Stack -> stmt -> Stack
.

Inductive CallSteps: Stack -> Locals -> stmt ->
                     Stack -> Locals -> stmt -> Prop :=
| call_steps: forall loc arg argval stk retid rt paramid pt decls newloc body,
     ExprYields pt loc arg argval ->
     VardeclsSteps (NatMap.add paramid argval (NatMap.empty value))
                   decls
                   newloc ->
     CallSteps stk loc (s_call (mkvar rt retid)
                               (mkproc rt (mkvar pt paramid) decls body)
                               arg)
               (stack_pending loc stk (s_assign (mkvar rt retid) (e_value rt v_undef)))
               newloc
               body
.

Inductive ReturnSteps: Stack -> Locals -> stmt ->
                        Stack -> Locals -> stmt -> Prop :=
| return_steps: forall loc loc' rt retid stk ejunk ret retval,
     ExprYields rt loc ret retval ->
     ReturnSteps (stack_pending loc' stk (s_assign (mkvar rt retid) ejunk)) loc (s_return ret)
                 stk loc' (s_assign (mkvar rt retid) (e_value rt retval))
.

Inductive StackSteps: Heap -> Stack -> Heap -> Stack -> Prop :=
| stack_steps_stmt: forall h loc stk s h' loc' s',
     StmtSteps h loc s h' loc' s' ->
     StackSteps h (stack_top loc stk s) h' (stack_top loc' stk s')
| stack_steps_call_final: forall h loc stk s loc' stk' s',
     CallSteps stk loc s stk' loc' s' ->
     StackSteps h (stack_top loc stk s)
		 h (stack_top loc' stk' s')
| stack_steps_call_seq: forall h loc stk s s2 loc' stk' s',
     CallSteps stk loc s stk' loc' s' ->
     StackSteps h (stack_top loc stk (s_seq s s2))
		 h (stack_top loc' stk' (s_seq s' s2))
| stack_steps_return_final: forall h loc stk s loc' stk' s',
     ReturnSteps stk loc s stk' loc' s' ->
     StackSteps h (stack_top loc stk s)
		 h (stack_top loc' stk' s')
| stack_steps_return_seq: forall h loc stk s s2 loc' stk' s',
     ReturnSteps stk loc s stk' loc' s' ->
     StackSteps h (stack_top loc stk (s_seq s s2))
		 h (stack_top loc' stk' s')
.

(* this is its own thing because it needs a different signature *)
(* XXX make sure the constraint that started procs return unit gets into the types *)
Inductive StackStepsStart: Stack -> Stack -> Stack -> Prop :=
| stack_steps_start: forall pt loc stk proc arg newloc argval,
     ExprYields pt loc arg argval ->
     newloc = NatMap.add 0 v_unit (NatMap.empty value) ->
     StackStepsStart
	      (stack_top loc stk (s_start proc arg))
        (stack_top loc stk s_skip)
        (stack_top newloc stack_empty (s_call (mkvar t_unit 0) proc (e_value pt argval)))
.

End Stacks.

(**************************************************************)	
(* threads *)

Section Threads.

Inductive Thread: Type :=
| thread: Stack -> Thread
.

Inductive ThreadSteps: Heap -> Thread -> Heap -> Thread -> Prop :=
| thread_steps: forall h s h' s',
     StackSteps h s h' s' -> 
     ThreadSteps h (thread s) h' (thread s')
.

Inductive ThreadStepsStart: Thread -> Thread -> Thread -> Prop :=
| thread_steps_start: forall s s' s2,
     StackStepsStart s s' s2 -> 
     ThreadStepsStart (thread s) (thread s') (thread s2)
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

