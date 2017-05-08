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

Inductive Heap :=
| mkheap (memory: NatMap.t value)
         (lockenv: NatMap.t LockState)
         (disks: NatMap.t (NatMap.t value)):
       Heap
.

Definition Locals := NatMap.t value.

Definition get_locals (rho : Locals) (v : var) : option value :=
  match v with
  | mkvar t n => NatMap.find n rho
  end.
Definition set_locals (v : var) (val : value) (rho : Locals) : Locals :=
  match v with
  | mkvar t n => NatMap.add n val rho
  end.

Definition heap_get_data (whichheap: WhichHeap) (index: nat) (h: Heap):
                                option value :=
   match h with
   | mkheap memory _ disks =>
        match whichheap with
        | MemoryHeap => NatMap.find index memory
        | DiskHeap disknum =>
             match NatMap.find disknum disks with
             | Some disk => NatMap.find index disk
             (* XXX we should have something that prevents getting here *)
             | None => None
             end
        end
   end.

Definition heap_set_data (whichheap: WhichHeap) (index: nat)
                         (val: value) (h: Heap): Heap :=
   match h with
   | mkheap memory lockenv disks =>
        match whichheap with
        | MemoryHeap =>
             mkheap (NatMap.add index val memory) lockenv disks
        | DiskHeap disknum =>
             match NatMap.find disknum disks with
             | Some disk =>
                  let disk' := (NatMap.add index val disk) in
                  mkheap memory lockenv (NatMap.add disknum disk' disks)
             | None => mkheap memory lockenv disks
             end
        end
   end.

Definition get_heap (rho : Heap) (a : addr) : option value :=
  match a with
  | mkaddr t n which => heap_get_data which n rho
  end.
  (*
  match rho with
  | mkheap mem lk disks =>
    match a with
    | mkaddr t n which =>
      match which with
      | MemoryHeap => NatMap.find n mem
      | DiskHeap d =>
        match NatMap.find d disks with
        | None => None
        | Some disk => NatMap.find n disk
        end
      end
    end
  end.*)

Definition set_heap (a : addr) (val : value) (rho : Heap) : Heap :=
  match a with
  | mkaddr t n which => heap_set_data which n val rho
  end.
  (*
  match rho with
  | mkheap mem lk disks =>
    match a with
    | mkaddr t n which =>
      match which with
      | MemoryHeap => mkheap (NatMap.add n val mem) lk disks
      | DiskHeap d =>
        match NatMap.find d disks with
        (* XXX write errors for missing disks? *)
        | None => rho
        | Some disk => mkheap mem lk (NatMap.add d (NatMap.add n val disk) disks)
        end
      end
    end
  end.*)

Definition heap_get_lockstate (index: nat) (h: Heap): option LockState :=
   match h with
   | mkheap _ lockenv _ => NatMap.find index lockenv
   end.

Definition heap_set_lockstate (index: nat) (val: LockState) (h: Heap): Heap :=
   match h with
   | mkheap memory lockenv disks =>
        mkheap memory (NatMap.add index val lockenv) disks
   end.

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
Inductive StmtSteps: Heap -> Locals -> stmt ->
                     Heap -> Locals -> stmt -> Prop :=
| step_in_seq: forall h loc s1 s2 h' loc' s1',
     StmtSteps h loc s1 h' loc' s1' ->
     StmtSteps h loc (s_seq s1 s2) h' loc' (s_seq s1' s2)
| step_next: forall h loc s2,
     StmtSteps h loc (s_seq s_skip s2) h loc s2
| step_assign: forall h loc id type e a,
     ExprYields type loc e a ->
     StmtSteps h loc (s_assign (mkvar type id) e)
               h (NatMap.add id a loc) s_skip
| step_load: forall h loc type lid e hid whichheap a,
     ExprYields type loc e (v_addr (mkaddr type hid whichheap)) ->
     heap_get_data whichheap hid h = Some a ->
     StmtSteps h loc (s_load (mkvar type lid) e)
               h (NatMap.add lid a loc) s_skip
| step_store: forall h loc type lid e hid whichheap a,
     ExprYields type loc e a ->
     ExprYields type loc (e_read (mkvar type lid)) (v_addr (mkaddr type hid whichheap)) ->
     StmtSteps h loc (s_store (mkvar type lid) e)
               (heap_set_data whichheap hid a h) loc s_skip
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
| step_getlock: forall h loc t id heapaddr,
     NatMap.find id loc = Some (v_lock (mkaddr t heapaddr MemoryHeap)) ->
     heap_get_lockstate heapaddr h = Some LockAvailable ->
     StmtSteps h loc (s_getlock (mkvar (t_lock t) id))
               (heap_set_lockstate heapaddr LockHeld h) loc (s_skip)
| step_putlock: forall h loc t id heapaddr,
     NatMap.find id loc = Some (v_lock (mkaddr t heapaddr MemoryHeap)) ->
     (* XXX shouldn't we require that we hold the lock? *)
     (* (XXX: maybe we can't; see notes elsewhere *)
     heap_get_lockstate heapaddr h = Some LockHeld ->
     StmtSteps h loc (s_putlock (mkvar (t_lock t) id))
               (heap_set_lockstate heapaddr LockAvailable h) loc (s_skip)
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

Inductive StackSteps: Heap -> Stack ->
                      Heap -> Stack -> Prop :=

| stack_steps_stmt: forall h loc stk s h' loc' s',
     StmtSteps h loc s
               h' loc' s' ->
     StackSteps h (stack_frame loc stk s)
                h' (stack_frame loc' stk s')

| stack_steps_call_final: forall h loc stk x proc arg,
     (* gross but avoids duplicating the call frame logic *)
     StackSteps h (stack_frame loc stk (s_call x proc arg))
                h (stack_frame loc stk (s_seq (s_call x proc arg) s_skip))

| stack_steps_call_seq: forall
                            h loc stk s s2
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
     StackSteps h (stack_frame loc stk s)
                h (stack_frame new'loc (stack_frame loc stk s') body)

| stack_steps_return_seq: forall h loc stk e s2,
     (* return followed by crap is just return *)
     StackSteps h (stack_frame loc stk (s_seq (s_return e) s2))
                h (stack_frame loc stk (s_return e))

| stack_steps_return_final: forall h
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
     StackSteps h (stack_frame loc (stack_frame loc' stk' s') (s_return ret))
                h (stack_frame loc' stk' s'')
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

Inductive ThreadSteps: Heap -> Thread ->
                       Heap -> Thread -> Prop :=
| thread_steps: forall h s h' s',
     StackSteps h s h' s' -> 
     ThreadSteps h (thread s) h' (thread s')
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
| machine: Heap -> list Thread -> Machine
.

(*
 * XXX: how do we reason about properties like "a thread may not exit
 * while it holds locks"?
 *)

Inductive MachineSteps: Machine -> Machine -> Prop :=
| machine_steps_plain: forall h t h' t' ts1 ts2,
     ThreadSteps h t h' t' ->
     MachineSteps (machine h (ts1 ++ [t] ++ ts2))
                  (machine h' (ts1 ++ [t'] ++ ts2))
| machine_steps_start: forall h t t1 t2 ts1 ts2,
     ThreadStepsStart t t1 t2 ->
     MachineSteps (machine h (ts1 ++ [t] ++ ts2))
                  (machine h (ts1 ++ [t1; t2] ++ ts2))
| machine_steps_exit: forall h t ts1 ts2,
     ThreadDone t ->
     MachineSteps (machine h (ts1 ++ [t] ++ ts2))
                  (machine h (ts1 ++ ts2))
.

End Machines.
