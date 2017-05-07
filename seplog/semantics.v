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

Inductive LockState: Set :=
| LockHeld: LockState (* XXX: keep track of who holds it? *)
| LockAvailable: LockState
.

(* old form that used coq types directly
Inductive val: Type := mkval (t: Type) (a : t): val.

Definition Heap := NatMap.t val.
Definition Locals := NatMap.t val.
*)

Definition Lockenv := NatMap.t LockState.
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
Inductive StmtSteps: Lockenv -> Heap -> Locals -> stmt ->
                     Lockenv -> Heap -> Locals -> stmt -> Prop :=
| step_in_seq: forall le h loc s1 s2 le' h' loc' s1',
     StmtSteps le h loc s1 le' h' loc' s1' ->
     StmtSteps le h loc (s_seq s1 s2) le' h' loc' (s_seq s1' s2)
| step_next: forall le h loc s2,
     StmtSteps le h loc (s_seq s_skip s2) le h loc s2
| step_assign: forall le h loc id type e a,
     ExprYields type loc e a ->
     StmtSteps le h loc (s_assign (mkvar type id) e)
               le h (NatMap.add id a loc) s_skip
| step_load: forall le h loc type lid e hid heapnum a,
     (* XXX this is wrong (needs to handle heapnum) *)
     ExprYields type loc e (v_addr (mkaddr type hid heapnum)) ->
     NatMap.find hid h = Some a ->
     StmtSteps le h loc (s_load (mkvar type lid) e)
               le h (NatMap.add lid a loc) s_skip
| step_store: forall le h loc type lid e hid heapnum a,
     (* XXX this is wrong (needs to handle heapnum) *)
     ExprYields type loc e a ->
     ExprYields type loc (e_read (mkvar type lid)) (v_addr (mkaddr type hid heapnum)) ->
     StmtSteps le h loc (s_store (mkvar type lid) e)
               le (NatMap.add hid a h) loc s_skip
| step_if_true: forall le h loc e st sf,
     ExprYields t_bool loc e v_true ->
     StmtSteps le h loc (s_if e st sf) le h loc st
| step_if_false: forall le h loc e st sf,
     ExprYields t_bool loc e v_false ->
     StmtSteps le h loc (s_if e st sf) le h loc sf
| step_while_true: forall le h loc e body,
     ExprYields t_bool loc e v_true ->
     StmtSteps le h loc (s_while e body)
               le h loc (s_seq body (s_while e body))
| step_while_false: forall le h loc e body,
     ExprYields t_bool loc e v_false ->
     StmtSteps le h loc (s_while e body) le h loc s_skip
| step_getlock: forall le h loc t id heapaddr whichheap,
     (* XXX whichheap should be restricted to memory *)
     NatMap.find id loc = Some (v_lock (mkaddr t heapaddr whichheap)) ->
     NatMap.find heapaddr le = Some LockAvailable ->
     StmtSteps le h loc (s_getlock (mkvar (t_lock t) id))
               (NatMap.add heapaddr LockHeld le) h loc (s_skip)
| step_putlock: forall le h loc t id heapaddr whichheap,
     (* XXX whichheap should be restricted to memory *)
     NatMap.find id loc = Some (v_lock (mkaddr t heapaddr whichheap)) ->
     (* XXX shouldn't we require that we hold the lock? *)
     NatMap.find heapaddr le = Some LockHeld ->
     StmtSteps le h loc (s_putlock (mkvar (t_lock t) id))
               (NatMap.add heapaddr LockAvailable le) h loc (s_skip)
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
| stack_frame: Locals -> Stack -> stmt -> Stack
.

Inductive StackSteps: Lockenv -> Heap -> Stack ->
                      Lockenv -> Heap -> Stack -> Prop :=

| stack_steps_stmt: forall le h loc stk s le' h' loc' s',
     StmtSteps le h loc s
               le' h' loc' s' ->
     StackSteps le h (stack_frame loc stk s)
                le' h' (stack_frame loc' stk s')

| stack_steps_call_final: forall h le loc stk x proc arg,
     (* gross but avoids duplicating the call frame logic *)
     StackSteps le h (stack_frame loc stk (s_call x proc arg))
                le h (stack_frame loc stk (s_seq (s_call x proc arg) s_skip))

| stack_steps_call_seq: forall
                            le h loc stk s s2
                            rt retid pt paramid decls body arg argval
                            s' new'loc,
     (* restrict the form of the call statement *)
     s = (s_seq (s_call (mkvar rt retid)
                    (mkproc rt (mkvar pt paramid) decls body)
                    arg)
                 s2) ->
     (* the new statement for the outer frame *)
     s' = s_seq (s_assign (mkvar rt retid) (e_value rt v_undef)) s2 ->

     (* evaluate the arg in the outer frame *)
     ExprYields pt loc arg argval ->

     (* create the locals for the new inner frame *)
     VardeclsSteps (NatMap.add paramid argval (NatMap.empty value))
                   decls
                   new'loc ->

     (* make a new frame to evaluate the procedure body *)
     StackSteps le h (stack_frame loc stk s)
                le h (stack_frame new'loc (stack_frame loc stk s') body)

| stack_steps_return_seq: forall le h loc stk e s2,
     (* return followed by crap is just return *)
     StackSteps le h (stack_frame loc stk (s_seq (s_return e) s2))
                le h (stack_frame loc stk (s_return e))

| stack_steps_return_final: forall le h
                                loc loc' stk' s' s''
                                rt ret retval
                                x ejunk,
     (* evaluate the return expression in the inner frame *)
     ExprYields rt loc ret retval ->

     (* the statement in the outer frame must be an assignment *)
     s' = s_assign x ejunk ->

     (* and gets updated with the return value *)
     s'' = s_assign x (e_value rt retval) ->

     (* pop the frame *)
     StackSteps le h (stack_frame loc (stack_frame loc' stk' s') (s_return ret))
                le h (stack_frame loc' stk' s'')
.

(* this is its own thing because it needs a different signature *)
(* XXX make sure the constraint that started procs return unit gets into the types *)
Inductive StackStepsStart: Stack -> Stack -> Stack -> Prop :=
| stack_steps_start: forall pt loc stk proc arg newloc argval,
     ExprYields pt loc arg argval ->
     newloc = NatMap.add 0 v_unit (NatMap.empty value) ->
     StackStepsStart
        (stack_frame loc stk (s_start proc arg))
        (stack_frame loc stk s_skip)
        (stack_frame newloc stack_empty (s_call (mkvar t_unit 0) proc (e_value pt argval)))
.

Inductive StackDone: Stack -> Prop :=
| stack_done: forall loc,
     StackDone (stack_frame loc stack_empty s_skip)
.

End Stacks.

(**************************************************************)
(* threads *)

Section Threads.

Inductive Thread: Type :=
| thread: Stack -> Thread
.

Inductive ThreadSteps: Lockenv -> Heap -> Thread ->
                       Lockenv -> Heap -> Thread -> Prop :=
| thread_steps: forall le h s le' h' s',
     StackSteps le h s le' h' s' -> 
     ThreadSteps le h (thread s) le' h' (thread s')
.

Inductive ThreadStepsStart: Thread -> Thread -> Thread -> Prop :=
| thread_steps_start: forall s s' s2,
     StackStepsStart s s' s2 -> 
     ThreadStepsStart (thread s) (thread s') (thread s2)
.

Inductive ThreadDone: Thread -> Prop :=
| thread_done: forall stk,
     StackDone stk ->
     ThreadDone (thread stk)
.

End Threads.

(**************************************************************)
(* machines *)

Section Machines.

Inductive Machine: Type :=
| machine: Lockenv -> Heap -> list Thread -> Machine
.

(*
 * XXX: how do we reason about properties like "a thread may not exit
 * while it holds locks"?
 *)

Inductive MachineSteps: Machine -> Machine -> Prop :=
| machine_steps_plain: forall le h t le' h' t' ts1 ts2,
     ThreadSteps le h t le' h' t' ->
     MachineSteps (machine le h (ts1 ++ [t] ++ ts2))
                  (machine le' h' (ts1 ++ [t'] ++ ts2))
| machine_steps_start: forall le h t t1 t2 ts1 ts2,
     ThreadStepsStart t t1 t2 ->
     MachineSteps (machine le h (ts1 ++ [t] ++ ts2))
                  (machine le h (ts1 ++ [t1; t2] ++ ts2))
| machine_steps_exit: forall le h t ts1 ts2,
     ThreadDone t ->
     MachineSteps (machine le h (ts1 ++ [t] ++ ts2))
                  (machine le h (ts1 ++ ts2))
.

End Machines.
