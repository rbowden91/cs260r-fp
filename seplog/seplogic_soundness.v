Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Require Import Program.
Import ListNotations.

Require Import ast.
Require Import semantics.
Require Import fo_seplogic.

(* unify types... *)
Module NatMap := semantics.NatMap.
Module NatMapFacts := semantics.NatMapFacts.


Inductive StmtStepsMany : Heap -> Locals -> stmt ->
                          Heap -> Locals -> stmt -> Prop :=
| stmtsteps_refl : forall h rho s, StmtStepsMany h rho s h rho s
| stmtsteps_trans : forall h rho s h' rho' s',
    StmtStepsMany h rho s h' rho' s' ->
    forall h'' rho'' s'',
      StmtSteps h' rho' s' h'' rho'' s'' ->
      StmtStepsMany h rho s h'' rho'' s''.

Definition heap_lookup (h : Heap) (a : addr) : option value := get_heap h a.

Definition respects_all_invariants : predicates_sa.pred world := fun x => False (*XXX ????? *).
  

(* intended to be a strengthened version of the main soundness statement.
   We continue to ignore return conditions in this setting.
   *)
(* XXX XXX XXX XXX XXX XXX XXX XXX XXX XXX *)
  (* we need to assume a heap that's consistent w.r.t. the PC, P, and all lock invariants *)
  (* that is, a part of the heap obeys P /\ PC, and the PC implies the invariants for all of
     the held locks, and the rest of the heap obeys the invariants for all the unheld locks *)
  (* then we can step the statement over this heap *)
  (* then we can show that there are new PC' and P' that maintain
     the consistency of the resulting heap over all the lock invariants---again. *)
  (* the unfortunate thing is trying to say the heap is consistent w.r.t. the invariants on
     all the locks, which themselves live inside the heap. and it is difficult to write down
     an assertion that captures the invariants for ALL these locks, as by *ing them together. *)
  (* However, the conclusion takes the form: *)
  (* exists PC P, hoare_stmt retC ret lk_invs PC P s' QC Q /\
                  PC constrains contents of P to obey the invariants of held locks /\
                  the rest of the heap obeys the invariants of unheld locks *)


(*
      ((PC /\ P) * (other_part_which_respects_invariants)) h ->
      forall h' rho' s',
        StmtStepsMany h rho s h' rho' s' ->
        exists PC P, hoare_stmt retC ret lk_invs PC P s' QC Q /\
                     PC rho' (get_heap h') /\ (* XXX does this actually preserve invariants *)
                     P rho' (get_heap h').
      

      (* satisfies crash precondition *)
      PC rho (get_heap h) ->
      (* satisfies precondition *)
      P rho (get_heap h) -> 
      (* satisfies all lock invariants on THE REST of the heap *)
      (forall a l,
          heap_lookup (mkheap mem lk disk) a = Some (v_lock l) ->
          crash_inv (v_lock l) lk_invs (heap_lookup (mkheap mem lk disk))) ->
      forall h' rho' s',
        StmtStepsMany h rho s h' rho' s' ->
        (* XXX except this needs to also state that invariants are maintained
               and enforced by the selected PC' *)
        exists PC' P', hoare_stmt retC ret lk_invs PC' P' s' QC Q /\
                     PC rho' (get_heap h') /\
                     P rho' (get_heap h').
*)
(* perhaps "(P * R) h, and forall addresses that map to locks in P,
            if the lock is not held then R had better imply the lock invariant associated w/
            that lock" *)
(* no because then you will step to pull in another lock from R, and that lock will be pointing
   at blank heap or something instead of something that actually satisfies its invariants *)
            
(* XXX XXX XXX XXX XXX XXX XXX XXX XXX XXX *)

(* heap and locals state respect preconditions and lock invariants *)
(* THIS is what is hard to state *)
Definition state_good (h : Heap) (rho : Locals)
           (PC : assertion) (P : assertion) (lk_invs : lk_inv_map) : Prop := False.

(* one assertion does not violate another *)
Definition obeys (a : assertion) (b : assertion) :=
  forall h rho, ~ (a rho (heap_lookup h) -> ~ (b rho (heap_lookup h))).

(* lock at address x is held *)
Definition held (x : addr) := False.

Lemma stmt_step_sound' :
  forall retC ret lk_invs PC P s QC Q,
    hoare_stmt retC ret lk_invs PC P s QC Q ->
    forall (h : Heap) (rho : Locals),
      state_good h rho PC P lk_invs ->
      forall h' rho' s',
        StmtStepsMany h rho s h' rho' s' ->
        exists PC' P', obeys P' PC' /\
                       (forall t a,
                           held a ->
                           forall rho h, PC' rho h -> (crash_inv t a lk_invs) h) /\
                       state_good h' rho' PC' P' lk_invs /\
                       hoare_stmt retC ret lk_invs PC' P' s' QC Q.

Admitted.


(* The statement is that a hoare_stmt with some set of lock invariants lk_invs and:
   1. the weakest possible return conditions,
   2. the weakest possible crash precondition,
   3. any precondition, postcondition, and crash postcondition,
   when run on a heap and locals satisfying its precondition,
   AND which satisfies the lock invariants globally,
   from a lock environment where everything begins unlocked,
   will never step to a state violating a lock invariant! *)
Lemma stmt_step_sound :
  forall lk_invs P s QC Q,
    hoare_stmt (fun v w => True) (* retC *)
               (fun v w => True) (* ret *)
               lk_invs (* lock invariants *)
               (fun rho w => True) (* crash pre *)
               P s QC Q ->
    forall mem lk disk locals,
      (* all locks begin unlocked *)
      (forall n, NatMap.In n lk -> NatMap.find n lk = Some LockAvailable) ->
      (* heap meets precondition and lock invariants *)
      state_good (mkheap mem lk disk) locals (fun rho w => True) P lk_invs ->
      forall heap' locals' s',
        StmtStepsMany (mkheap mem lk disk) locals s heap' locals' s' ->
        (* ALL lock invariants are satisfied *)
        state_good heap' locals' (fun rho w => True) (fun rho w => True) lk_invs.

Admitted.
  (*
        (* the strong invariant of any lock on the heap is satisfied *)
        (* XXX this should be *ing them together, or maybe we need to go intuitionistic *)
        forall a l t,
          heap_lookup heap' a = Some (v_lock l) ->
          crash_inv t l lk_invs (heap_lookup heap').
*)


Inductive ThreadStepsMany : Heap -> Thread -> Heap -> Thread -> Prop :=
| threadsteps_refl : forall h t, ThreadStepsMany h t h t
| threadsteps_trans : forall h t h' t',
    ThreadStepsMany h t h' t' ->
    forall h'' t'',
      ThreadSteps h' t' h'' t'' ->
      ThreadStepsMany h t h'' t''.

(* analogous statement for thread stepping: very similar
   proof will have to account for calls *)
Lemma thread_step_sound :
  forall lk_invs P s QC Q,
    hoare_stmt (fun v => fun w => True) (* retC *)
               (fun v => fun w => True) (* ret *)
               lk_invs (* lock invariants *)
               (fun rho => fun w => True) (* crash pre *)
               P s QC Q ->
    forall mem lk disk locals,
      (* all locks begin unlocked *)
      (forall n, NatMap.In n lk -> NatMap.find n lk = Some LockAvailable) ->
      (* heap meets preconditions *)
      P locals (heap_lookup (mkheap mem lk disk)) ->
      forall heap' s',
        ThreadStepsMany (mkheap mem lk disk) (thread (stack_frame locals stack_empty s))
                        heap' s' ->
        (* the strong invariant of any lock on the heap is satisfied *)
        forall a l t,
          heap_lookup heap' a = Some (v_lock l) ->
          crash_inv t l lk_invs (heap_lookup heap').
Admitted.

(* TODO: machine steps soundness
   This may or may not even be related to stmt stepping soundness above
   (connecting them would require a statement that if single threads adhered to hoare tuples,
   so does the whole multithreaded machine) *)
(* in order to properly discuss the heap, will have to go through and * all the thread
   preconditions together... *)