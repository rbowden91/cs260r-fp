Require Import msl.base.

Require Import msl.msl_direct.
Require Import msl.seplog.

Require Import msl.alg_seplog_direct.


Require Import msl.Coqlib2.
Require Import msl.log_normalize.

Require Import ast.
Require Import semantics.
Require Import List.
Import ListNotations.

Require Import OrderedType OrderedTypeEx.
Require FMapList.
Require FMapFacts.
Module NatMap := FMapList.Make Nat_as_OT.
Module NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.


Definition world := (addr -> option value)%type.

Instance Join_world: Join world :=
	Join_fun addr (option value) (Join_lower (Join_discrete value)).


Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Sep_alg world := _.
Instance Canc_world : Canc_alg world := _.
Proof.
Admitted.

Instance Sing_world : Sing_alg world := _.
Proof.
Admitted.

Instance Disj_world : Disj_alg world := _.
Proof.
Admitted.

Instance Cw: ClassicalSep (pred world) := _.
Instance Nw: NatDed (pred world) := _.

Definition assertion := Locals -> pred world.

(* Definition den (s: state) : world := get_heap s. *)

Definition defined (x: var) : assertion :=
   fun rho => fun w => exists v, get_locals rho x = Some v.

Definition subst (x : var) (y : value) (P: assertion) : assertion :=
   fun rho => fun w => P (set_locals x y rho) w.

Definition mapsto (x:addr) (y:value) : pred world :=
 fun w =>
    exists v, w x = Some v /\
    y = v
.

Definition ex_mapsto (x:addr) : pred world :=
 EX v:value, mapsto x v
.

(* Original mapsto:
    exists ax, get_stack w x = Some (v_addr ax) /\
    exists ay, get_stack w y = Some ay /\
    forall a, if eq_dec a ax then get_heap w a = Some ay else get_heap w a = None.
*)

Definition equal (x y: addr) : pred world :=
            fun w => w x = w y.

(* XXX more stuff goes here *)
Inductive modvars : stmt -> var -> Prop :=
| mod_assign: forall x e, modvars (s_assign x e) x
| mod_load: forall x l, modvars (s_load x l) x
| mod_call: forall x p e, modvars (s_call x p e) x
| mod_seq1: forall x s1 s2, modvars s1 x -> modvars (s_seq s1 s2) x
| mod_seq2: forall x s1 s2, modvars s2 x -> modvars (s_seq s1 s2) x
(* XXX can say something about e evaluating to true/false? *)
| mod_if1: forall x e s1 s2, modvars s1 x -> modvars (s_if e s1 s2) x
| mod_if2: forall x e s1 s2, modvars s2 x -> modvars (s_if e s1 s2) x
| mod_while: forall x e s, modvars s x -> modvars (s_while e s) x
.

Definition nonfreevars (P: assertion) (x: var) : Prop :=
  forall rho w v, P rho w -> P (set_locals x v rho) w.

Definition subset (S1 S2: var -> Prop) :=
  forall x, S1 x -> S2 x.

Function eval_expr (e : expr) (rho : Locals) : value :=
  match e with
  | e_read v =>
    match get_locals rho v with
    | Some val => val
    | None => v_undef
    end
  | e_getlockaddr _ e =>
    match eval_expr e rho with
    | v_lock a => v_addr a
    | _ => v_undef
    end
  | e_value ty v => v
  | e_cond ty b e1 e2 =>
    match eval_expr b rho with
    | v_bool true => eval_expr e1 rho
    | v_bool false => eval_expr e2 rho
    | _ => v_undef
    end
  | e_natbinop f e1 e2 =>
    match (eval_expr e1 rho, eval_expr e2 rho) with
    | (v_nat n1, v_nat n2) => v_nat (f n1 n2)
    | _ => v_undef
    end
  end
.

Definition typeof_val (v : value) (t : type) : Prop :=
  match v with
  | v_unit => t_unit = t
  | v_nat _ => t_nat = t
  | v_bool _ => t_bool = t
  | v_pair _ _ => False (* XXX notyet *)
  | v_list t' _ => t_list t' = t
  | v_addr (mkaddr t' _ _) => t_addr t' = t
  | v_lock (mkaddr t' _ _) => t_lock t' = t
  | v_undef => False
  end.

Function typeof_expr (e : expr) (rho : Locals) (t : type) : Prop :=
  match e with
  | e_read v => match get_locals rho v with
                | None => False
                | Some _ => type_of_var v = t
                end
  | e_natbinop _ _ _ => t_nat = t
  | e_value ty _ => ty = t 
  | e_getlockaddr ty _ => ty = t
  | e_cond ty _ _ _ => ty = t
  end.

(* XXX this is a preserved invariant --- move to a soundness file *)
Lemma tt_sound :
  forall {v} {a : value} {rho : Locals}, get_locals rho v = Some a ->
  typeof_val a (type_of_var v).
Proof.
Admitted.

Notation ETT := (fun (_ : Locals) => TT).
Notation ATT := (fun (_ : value) => TT).
Notation ARTT := (fun (_ : value) => fun (_ : value) => TT).
Notation EFF := (fun (_ : Locals) => FF).
Notation AFF := (fun (_ : value) => FF).
Notation ARFF := (fun (_ : value) => fun (_ : value) => FF).

Notation e_emp := (fun (_ : Locals) => emp).
Notation a_emp := (fun (_ : value) => emp).
Notation ar_emp := (fun (_ : value) => fun (_ : value) => emp).

Local Open Scope logic.

(* XXX make this an option (pred world * pred world)? Some kind of type checking
       on the address? We want to keep t_lock t_nat and t_nat in different address
       spaces. *)
Notation lk_inv_map := (type -> addr -> pred world * pred world).

Definition crash_inv (lktype:type) (resource:addr) (lk_invs : lk_inv_map) :=
  fst (lk_invs lktype resource).

Definition reg_inv (lktype:type) (resource:addr) (lk_invs : lk_inv_map) :=
  snd (lk_invs lktype resource).

Inductive hoare_stmt :
  (value -> pred world) -> (* retC *)
  (value -> pred world) -> (* ret *)
  lk_inv_map -> (* lk_invs *)
  assertion -> assertion -> stmt -> assertion -> assertion -> Prop :=

| ht_skip : forall retC ret lk_invs,
            forall P C,
            hoare_stmt retC ret lk_invs
                       C P (s_skip) C P

| ht_seq : forall retC ret lk_invs,
             forall PC RC QC P R Q s1 s2,
             hoare_stmt retC ret lk_invs
                        PC P s1 RC R ->
             hoare_stmt retC ret lk_invs
                        RC R s2 QC Q ->
             hoare_stmt retC ret lk_invs
                        PC P (s_seq s1 s2) QC Q

| ht_if : forall retC ret lk_invs,
          forall PC QC P Q e_b s1 s2,
          hoare_stmt retC ret lk_invs
                     PC (fun rho => P rho && !!((eq (v_bool true) (eval_expr e_b rho)))) s1 QC Q ->
          hoare_stmt retC ret lk_invs
                     PC (fun rho => P rho && !!((eq (v_bool false) (eval_expr e_b rho)))) s2 QC Q ->
          hoare_stmt retC ret lk_invs
                     PC P (s_if e_b s1 s2) QC Q

| ht_return : forall retC ret lk_invs,
              forall e PC P,
              (forall rho, retC (eval_expr e rho) |-- PC rho) ->
              (forall rho, P rho |-- ret (eval_expr e rho)) ->
              hoare_stmt retC ret lk_invs
                         PC P (s_return e) ETT EFF

| ht_while : forall retC ret lk_invs,
             forall C P e_b s,
             hoare_stmt retC ret lk_invs
                        C (fun rho => P rho && !!(eq (v_bool true) (eval_expr e_b rho))) s C P ->
             hoare_stmt retC ret lk_invs
                        C P (s_while e_b s) C (fun rho => P rho && !!(eq (v_bool false) (eval_expr e_b rho)))

| ht_assign : forall {retC ret lk_invs},
              forall {C P v e},
              P |-- (fun rho => !!(typeof_expr e rho (type_of_var v))) ->
              hoare_stmt retC ret lk_invs
                           C P
                             (s_assign v e)
                           C (fun rho =>
                              !!(get_locals rho v = Some (eval_expr e rho))
                              && P rho)
(* XXX For now, SSA. We'll just write a transformation to enforce that. *)
(*
                           C (EX old:value, (fun rho =>
                              !!(get_locals rho v = Some (eval_expr e (set_locals v old rho)))
                              && P (set_locals v old rho)))
*)

(* XXX special frame for PC and QC. Also, this seems to weakly constrain the old rv... *)
(* XXX XXX XXX Just force rv to be a new var for now... *)
(* XXX I blithely inserted decls in the mkproc without thinking, please fix *)
| ht_call : forall {retC ret lk_invs},
            forall {PC PC' P P' QC QC' Q Q' rv rt pv decls s e val},
            hoare_proc lk_invs PC P (mkproc rt pv decls s) QC Q ->
            (forall rho, PC' rho |-- PC (eval_expr e rho)) ->
            (forall rho, P' rho |-- P (eval_expr e rho)) ->
            hoare_stmt retC ret lk_invs
                       PC'
                       P'
                           (s_call rv (mkproc rt pv decls s) e)
                       (fun rho => QC' rho *
                                   QC (eval_expr e rho) val)
                       (fun rho => !!(get_locals rho rv = Some val) &&
                                   Q' rho *
                                   Q (eval_expr e rho) val)

(*
                       (fun rho => !!(table_get rho rv = Some val) &&
                                   EX old:value,
                                       (QC' (table_set rv old rho) *
                                       QC (eval_expr e (table_set rv old rho)) val))
                       (fun rho => !!(table_get rho rv = Some val) &&
                                   EX old:value,
                                       (Q' (table_set rv old rho) *
                                       Q (eval_expr e (table_set rv old rho)) val))
*)

| ht_getlock : forall {retC ret lk_invs},
               forall {v P P' C},
               forall lkptr lktype,
               P |-- (fun rho => !!(type_of_var v = t_addr (t_lock lktype))) ->
               P |-- (fun rho => !!(get_locals rho v = Some (v_addr lkptr))) ->
               P' |-- (fun rho => ex_mapsto lkptr) -> (* XXX this should be exact. can also include P' above *)
               (fun rho => ex_mapsto lkptr) |-- C ->
               hoare_stmt retC ret lk_invs
                          C (fun rho => P rho * P' rho)
                            (s_getlock v)
                          (EX resource:addr, (fun rho => C rho * mapsto lkptr (v_lock resource) * crash_inv lktype resource lk_invs))
                          (EX resource:addr, (fun rho => P rho * mapsto lkptr (v_lock resource) * reg_inv lktype resource lk_invs))

| ht_putlock : forall retC ret lk_invs,
               forall {P P' v C},
               forall lkptr lk lktype resource,
               P |-- (fun rho => !!(type_of_var v = t_addr (t_lock lktype))) ->
               P |-- (fun rho => !!(get_locals rho v = Some (v_addr lkptr))) ->
               P |-- (fun rho => !!(lk = v_lock resource)) ->
               P' |-- (fun rho => mapsto lkptr lk * reg_inv lktype resource lk_invs) ->
               C |-- (fun rho => ex_mapsto lkptr * crash_inv lktype resource lk_invs) ->
               hoare_stmt retC ret lk_invs
                          C
                          (fun rho => P rho * P' rho)
                            (s_putlock v)
                          (fun rho => ex_mapsto lkptr)
                          (fun rho => P rho * mapsto lkptr lk)

(* XXX Also SSA *)
| ht_load : forall {retC ret lk_invs},
            forall {P C e v P'},
            forall ptr,
            P |-- (fun rho => !!(typeof_expr e rho (t_addr (type_of_var v)))) ->
            P |-- (fun rho => !!(eval_expr e rho = v_addr ptr)) ->
            P' |-- (fun rho => ex_mapsto ptr) -> (* XXX *)
            hoare_stmt retC ret lk_invs
                           C (fun rho => P rho * P' rho)
                              (s_load v e)
                          C
                          (EX a:value, (fun rho =>
                             !! (get_locals rho v = Some a)
                             && P rho
                             * mapsto ptr a))
                 

| ht_store : forall {retC ret lk_invs},
            forall {P C e v P'},
            forall ptr t val,
            (fun rho => P rho * P' rho) |-- !!(type_of_var v = t_addr t) ->
            (fun rho => P rho * P' rho)  |-- (fun rho => !!(typeof_expr e rho t)) ->
            (fun rho => P rho * P' rho)  |-- (fun rho => !!(get_locals rho v = Some (v_addr ptr))) ->
            (fun rho => P rho * P' rho)  |-- (fun rho => !!(eval_expr e rho = val)) ->
            P' |-- (fun rho => ex_mapsto ptr) -> (* XXX *)
            (fun rho => P rho && mapsto ptr val) |-- C ->
            hoare_stmt retC ret lk_invs
                           C
                           (fun rho => P rho * P' rho)
                              (s_store v e)
                           C
                           (fun rho => P rho * mapsto ptr val)

(* XXX First, we can pass off crash conditions in the same way we frame them.
       Second, locks need to be able to be split. *)
(* XXX I blithely inserted decls in the mkproc without thinking, please fix *)
| ht_start: forall {retC ret lk_invs},
            forall {F P P' rt pv decls s e},
            hoare_proc lk_invs a_emp P (mkproc rt pv decls s) ar_emp ar_emp ->
            (forall rho, P' rho |-- P (eval_expr e rho)) ->
            hoare_stmt retC ret lk_invs
                       e_emp
                       (fun rho => F rho * P' rho)
                           (s_start (mkproc rt pv decls s) e)
                       e_emp
                       F

(* Stmt rules not directly related to the language *)

| ht_consequence : forall retC ret lk_invs,
                   forall PC PC' QC QC' P P' Q Q' s,
                   hoare_stmt retC ret lk_invs
                              PC P s QC Q ->
                   (forall rho, PC rho |-- PC' rho) -> 
                   (forall rho, QC' rho |-- QC rho) -> 
                   (* XXX should we need to enforce that this doesn't violate the crash condition? *)
                   (forall rho, P' rho |-- P rho) ->
                   (forall rho, Q rho |-- Q' rho) ->
                   hoare_stmt retC ret lk_invs
                              PC' P' s QC' Q'

(* XXX something about modified vars in R? *)
| ht_frame : forall retC ret lk_invs,
             forall PC QC P Q R s,
             hoare_stmt retC ret lk_invs
                        PC P s QC Q ->
             hoare_stmt retC ret lk_invs
                        PC (fun rho => (P rho) * (R rho)) s QC (fun rho => (Q rho) * (R rho))

| ht_frame_lock : forall retC ret lk_invs,
                  forall PC QC P Q s lkptr lktype n h lk resource,
                  hoare_stmt retC ret lk_invs
                             PC P s QC Q ->
                  hoare_stmt retC ret lk_invs
                             (fun rho => mapsto lkptr lk
                                         * crash_inv lktype resource lk_invs
                                         * PC rho)
                             (fun rho => !!(lk = v_lock resource)
                                         && !!(resource = mkaddr lktype n h)
                                         && mapsto lkptr lk
                                         * reg_inv lktype resource lk_invs
                                         * P rho)
                                 s
                             (fun rho => mapsto lkptr lk
                                         * crash_inv lktype resource lk_invs
                                         * QC rho)
                             (fun rho => !!(lk = v_lock resource)
                                         && !!(resource = mkaddr lktype n h)
                                         && mapsto lkptr lk
                                         * reg_inv lktype resource lk_invs
                                         * Q rho)


(* XXX semax_extract_prop? *)

(* These *don't* take assertions, because (for now) they don't need to take
 * the environment (argument / return value are explicitly passed in) *)
(* XXX I inserted decls in the mkproc without thinking, please fix *)
with hoare_proc :
  lk_inv_map ->
  (value -> pred world) -> (value -> pred world) -> proc -> 
  (value -> value -> pred world) -> (value -> value -> pred world) -> Prop :=
| ht_proc : forall PC QC P Q t v decls s lk_invs,
               (forall a, hoare_stmt (QC a) 
                                     (fun r => !!(typeof_val r t) && Q a r)
                                     lk_invs
                                     (fun rho => PC a)
                                     (fun rho => !!(typeof_val a (type_of_var v)) && 
                                                 !!(get_locals rho v = Some a) && P a)
                                     s
                                     ETT
                                     EFF) ->
               hoare_proc lk_invs PC P (mkproc t v decls s) QC Q.

Notation "{{ retC }} {{ ret }} {{ lk_invs }} ||- {{ PC }} {{ P }} s {{ QC }} {{ Q }}" :=
  (hoare_stmt retC ret lk_invs PC P s QC Q) (at level 90, s at next level).

Notation "'Return-Crash:' retC 'Return:' ret 'Lock-Invs:' lk_invs 'Pre-Crash:' PC 'Pre:' P 'Post-Crash:' QC 'Post:' Q 'Stmt:' s" :=
  (hoare_stmt retC ret lk_invs PC P s QC Q) (at level 89, s at next level, format
      "'[v' 'Return-Crash:' '[  ' '/'  retC ']' '//' 'Return:' '[  ' '/'  ret ']' '//' 'Lock-Invs:' '[  ' '/'  lk_invs ']' '//' 'Pre-Crash:' '[  ' '/'  PC ']' '//' 'Pre:' '[  ' '/'  P ']' '//' 'Post-Crash:' '[  ' '/'  QC ']' '//' 'Post:' '[  ' '/'  Q ']' '//' 'Stmt:' '[  ' '/'  s ']' ']'").

Notation "{{{ lk_invs }}} {{{ PC }}} {{{ P }}} p {{{ QC }}} {{{ Q }}}" :=
  (hoare_proc lk_invs PC P p QC Q) (at level 90, p at next level).

Lemma ht_getlock_noex : forall {retC ret lk_invs},
   forall {v P C},
   forall lkptr lktype a,
   P |-- (fun rho => !!(type_of_var v = t_addr (t_lock lktype))) ->
   P |-- (fun rho => !!(get_locals rho v = Some (v_addr lkptr))) ->
   (fun rho => ex_mapsto lkptr) |-- C ->
   hoare_stmt retC ret lk_invs
              C (fun rho => P rho * mapsto lkptr (v_lock a))
                (s_getlock v)
              (fun rho => C rho * mapsto lkptr (v_lock a)
                                * crash_inv lktype a lk_invs)
              (fun rho => P rho * mapsto lkptr (v_lock a)
                                * reg_inv lktype a lk_invs).
Proof.
Admitted.

Lemma ht_pc_consequence : forall retC ret lk_invs PC PC' P s QC Q,
  PC |-- PC' ->
  hoare_stmt retC ret lk_invs PC P s QC Q ->
  hoare_stmt retC ret lk_invs PC' P s QC Q.
Proof.
  intros.
  eapply ht_consequence; eauto.
Qed.

Lemma ht_p_consequence : forall retC ret lk_invs PC P P' s QC Q,
  P' |-- P ->
  hoare_stmt retC ret lk_invs PC P s QC Q ->
  hoare_stmt retC ret lk_invs PC P' s QC Q.
Proof.
  intros.
  eapply ht_consequence; eauto.
Qed.

Lemma ht_qc_consequence : forall retC ret lk_invs PC P s QC QC' Q,
  QC' |-- QC ->
  hoare_stmt retC ret lk_invs PC P s QC Q ->
  hoare_stmt retC ret lk_invs PC P s QC' Q.
Proof.
  intros.
  eapply ht_consequence; eauto.
Qed.

Lemma ht_q_consequence : forall retC ret lk_invs PC P s QC Q Q',
  Q |-- Q' ->
  hoare_stmt retC ret lk_invs PC P s QC Q ->
  hoare_stmt retC ret lk_invs PC P s QC Q'.
Proof.
  intros.
  eapply ht_consequence; eauto.
Qed.
(*
(* Need to have a hypothesis that nothing touches rv *)
Lemma ht_call_nf : forall {retC ret},
            forall {PC P QC Q rv rt pv s e val},
            hoare_proc PC P (p_proc rt pv s) QC Q ->
            hoare_stmt retC ret
                       (fun rho => PC (eval_expr e rho))
                       (fun rho => P (eval_expr e rho))
                           (s_call rv (p_proc rt pv s) e)
                       (fun rho => QC (eval_expr e rho) val)
                       (fun rho => !!(table_get rho rv = Some val) &&
                                   Q (eval_expr e rho) val).
*)

Definition example1 :=
  mkproc t_nat (mkvar t_nat 4) [] ([{
    s_return (e_read (mkvar t_nat 4)) ;
    s_skip
  }]).

Lemma pre_false : forall rc r lk_invs s QC Q,
  {{ rc }} {{ r }} {{ lk_invs }} ||-
  {{ ETT }} {{ EFF }} s {{ QC }} {{ Q }}.
Proof.
  intros.
  revert QC Q.
  induction s; intros.
  - apply ht_p_consequence with (P:=Q).
    intro.
    normalize.
    apply ht_qc_consequence with (QC:=TT); normalize.
    apply ht_skip.
  - eapply ht_seq.
    instantiate (1:=FF); instantiate (1:=TT); normalize.
    apply IHs2.
  - admit. (* s_start *)
  - admit. (* s_assign *)
  - admit. (* s_load *)
  - admit. (* s_store *)
  - apply ht_if.
    apply ht_p_consequence with (P:=(fun _ => FF)).
    intro. normalize.
    trivial.
    apply ht_p_consequence with (P:=(fun _ => FF)).
    intro. normalize.
    trivial.
  - admit. (* s_while *)
  - admit. (* s_call... shoot, how to handle induction on p? *)
  - admit. (* s_return *)
  - admit. (* s_getlock *)
  - admit. (* s_putlock *)
Admitted.


Lemma example1_sound : forall lk_invs,
  {{{ lk_invs }}}
  {{{ a_emp }}} {{{ a_emp }}} example1
    {{{ ar_emp }}} {{{ fun a => fun r => !!(r = a)}}}.
Proof.
  unfold example1.
  intro.
  apply ht_proc.
  intro.
  apply ht_seq with (RC:=ETT) (R:=EFF).
  apply ht_return; normalize.
  intros.
  unfold eval_expr.
  rewrite H0.
  normalize.
  apply pre_false.
Qed.

Definition example2 :=
  mkproc t_nat (mkvar t_nat 4) [] ([{
    s_call (mkvar t_nat 5) example1 (e_read (mkvar t_nat 4)) ;
    s_return (e_read (mkvar t_nat 5))
  }]).

Lemma example2_sound : forall lk_invs,
  {{{ lk_invs }}}
  {{{ a_emp }}} {{{ a_emp }}} example2 
    {{{ ar_emp }}} {{{ fun a => fun r => !!(r = a)}}}.
Proof.
  intro; unfold example2; apply ht_proc; intros.
  eapply ht_seq.
  pose proof example1_sound.
  unfold example1 in *.
  eapply (ht_call (H lk_invs)); normalize.

  (* Shouldn't it know this was the arg? *)
  instantiate (1:=a).
  eapply ht_seq.
  apply ht_return; normalize.
  instantiate (1:=e_emp).
  intros; intro; intro; trivial.
  intros.
  instantiate (1:=e_emp).
  apply andp_right;
  unfold eval_expr.
  rewrite H.
  apply tt_sound in H.
  simpl in H.
  eapply prop_right; eauto.
  eapply prop_right.
  unfold eval_expr.
  rewrite H.
  trivial.
  apply ht_skip.
Qed.

(* Make this notation so that it shows up like this in the proffs... *)
Notation lne_lkptr := (mkvar (t_addr (t_lock t_nat)) 0).
Notation lk := (mkvar (t_lock t_nat) 1).
Notation counterptr := (mkvar (t_addr t_nat) 2).
Notation counter1 := (mkvar (t_nat) 3).
Notation counter2 := (mkvar (t_nat) 4).
Notation counter3 := (mkvar (t_nat) 5).
Notation add2 v := (e_natbinop (fun x => fun y => x + y)
                           (e_read v) (e_value t_nat (v_nat 2))).
Notation minus2 v := (e_natbinop (fun x => fun y => x - y)
                           (e_read v) (e_value t_nat (v_nat 2))).


(* XXX need to fix list vardecls *)
Definition lock_nat_even :=
(*
  let lne_lkptr := (mkvar (t_addr (t_lock t_nat)) 0) in
  let lk := (mkvar (t_lock t_nat) 1) in
  let counterptr := (mkvar (t_addr t_nat) 2) in
  let counter1 := (mkvar (t_nat) 3) in
  let counter2 := (mkvar (t_nat) 4) in
  let counter3 := (mkvar (t_nat) 5) in
  let add2 v := (e_natbinop (fun x => fun y => x + y)
                           (e_read v) (e_value t_nat (v_nat 2))) in
  let minus2 v := (e_natbinop (fun x => fun y => x - y)
                           (e_read v) (e_value t_nat (v_nat 2))) in
*)
  mkproc t_nat lne_lkptr [] ([{
    (* Ugh, framing out the lock is annoying, so just load first instead... *)
    s_load lk (e_read lne_lkptr) ;
    s_assign counterptr (e_getlockaddr (t_addr t_nat) (e_read lk)) ;
    s_getlock lne_lkptr ;
    s_load counter1 (e_read counterptr) ;
    s_assign counter2 (add2 counter1) ;
    s_store counterptr (e_read counter2) ;
    s_assign counter3 (minus2 counter2) ;
    s_store counterptr (e_read counter3) ;
    s_putlock lne_lkptr ;
    s_return (e_value t_nat (v_nat 0))
  }]).

Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
    odd_S : forall n, even n -> odd (S n).

Definition lne_lkinvs :=
  fun (t : type) => fun (a : addr) =>
    match t with
    | t_nat => ((ex_mapsto a && (fun (w : world) =>
                   match (w a) with
                   | Some (v_nat n) => even n
                   | _ => False
                   end)),
                 (ex_mapsto a && fun (w : world) =>
                   match (w a) with
                   | Some (v_nat n) => n = 4
                   | _ => False
                   end))
    | _ => (fun (w : world) => False, fun (w : world) => False)
    end.

Lemma mapsto_imp_ex_mapsto: forall ptr target w,
  mapsto ptr target w -> ex_mapsto ptr w.
Proof.
  intros.
  unfold ex_mapsto.
  exists target.
  unfold mapsto.
  inversion H.
  destruct H0.
  unfold mapsto in H.
  apply H. (* XXX this all should be auto'd somehow. *)
Qed.

Lemma lift_exists : forall CR R L CP s CQ Q A P,
  (forall (a:A), hoare_stmt CR R L CP (P a) s CQ Q) ->
  hoare_stmt CR R L CP (EX a:A, (P a)) s CQ Q.
Admitted.


Lemma lock_nat_even_sound : forall lkptr,
  {{{ lne_lkinvs }}}
  {{{ (fun a =>
        ex_mapsto lkptr)
  }}}
  {{{ (fun a =>
        !!(a = v_addr lkptr)
        && ex_mapsto lkptr)
  }}}
    lock_nat_even
  {{{ (fun a => fun r =>
        ex_mapsto lkptr)
  }}}
  {{{ (fun a => fun r =>
        !!(a = v_addr lkptr)
        && ex_mapsto lkptr)
  }}}.
Proof.
  intro; unfold example2; apply ht_proc; intros.
  unfold type_of_var.
  eapply ht_seq.
  apply ht_p_consequence with (P:=(fun rho : Locals =>
       !! typeof_val a (t_addr (t_lock t_nat)) &&
       !! (get_locals rho (mkvar (t_addr (t_lock t_nat)) 0) = Some a) &&
       !! (a = v_addr lkptr) * ex_mapsto lkptr)).
  intro. normalize. rewrite sepcon_comm. normalize.

  eapply ht_load; intro; normalize.
  unfold typeof_expr; rewrite H0; unfold type_of_var; auto.
  unfold eval_expr; rewrite H0; auto.

  (* Need to do this *before* the eapply *)
  apply lift_exists; intro.

  eapply ht_seq.

  eapply ht_assign.
  intro; normalize.
  unfold type_of_var.
  unfold typeof_expr.
  repeat intro; unfold prop; simpl; auto.

  eapply ht_seq.

  (* XXX annoying parenthesization issue *)
  eapply ht_p_consequence with (P:=(fun rho : Locals =>
       (!! (get_locals rho (mkvar (t_addr t_nat) 2) =
           Some
             (eval_expr
                (e_getlockaddr (t_addr t_nat)
                   (e_read (mkvar (t_lock t_nat) 1))) rho)) &&
       (!! (get_locals rho (mkvar (t_lock t_nat) 1) = Some a0) &&
        (!! typeof_val a (t_addr (t_lock t_nat)) &&
         !! (get_locals rho (mkvar (t_addr (t_lock t_nat)) 0) = Some a) &&
         !! (a = v_addr lkptr))) * mapsto lkptr a0))); normalize.
  intro.
  normalize.

  eapply ht_getlock.
  instantiate (1:=t_nat).
  intro.
  normalize.
  intro. normalize.
  instantiate (1:=lkptr). normalize.

  intro; normalize.
  intro.
  apply mapsto_imp_ex_mapsto.

  intro. normalize.
  apply lift_exists. intro.
  eapply ht_seq.
  eapply ht_load; intro; normalize.
  unfold typeof_expr.
  rewrite H.
  unfold type_of_var.
  repeat intro; simpl; auto.
  unfold eval_expr. rewrite H.
  unfold eval_expr. rewrite H0.

  (* XXX Type soundness ugh... *)
  intro. intro.
  apply tt_sound in H0.
  unfold typeof_val in H0. unfold type_of_var in H0.
  destruct a0; try discriminate; try contradiction.
  destruct a0; try discriminate.
  (* XXX need some kind of "read some value from heap twice returns
         same thing twice" lemma *)
  instantiate (1:=a1).
  admit.
  unfold reg_inv; unfold snd. unfold lne_lkinvs.

  intro.
  rewrite andp_comm.
  normalize.
  destruct H.
  auto.

  apply lift_exists.
  intro.

  eapply ht_seq.
  eapply ht_assign; intro; normalize.

  unfold typeof_expr. unfold type_of_var.
  repeat intro; simpl; auto.

  eapply ht_seq.

  (* XXX more parenthesization issues... *)
  apply ht_p_consequence with (P:=(fun rho : Locals =>((
       !! (get_locals rho counter2 = Some (eval_expr (add2 counter1) rho)) &&
       (!! (get_locals rho counter1 = Some a2) &&
        (!! (get_locals rho counterptr =
             Some (eval_expr (e_getlockaddr (t_addr t_nat) (e_read lk)) rho)) &&
         (!! (get_locals rho lk = Some a0) &&
          (!! typeof_val a (t_addr (t_lock t_nat)) &&
           !! (get_locals rho lne_lkptr = Some a) && !! (a = v_addr lkptr))) *
         mapsto lkptr (v_lock a1))))) * mapsto a1 a2)).
  intro; normalize.

  (* type soundness *)
  assert (exists n1, a2 = v_nat n1) by admit.
  assert (exists a, a0 = v_lock a) by admit.
  destruct H. destruct H0.
  assert (a1 = x0) by admit. (* lost this somewhere *)

  eapply ht_store; intro; subst; normalize;

  unfold eval_expr; unfold typeof_expr; unfold type_of_var.
  instantiate (1:=t_nat).
  repeat intro; simpl; auto.

  rewrite H.
  repeat intro; simpl; auto.

  rewrite H1.
  unfold eval_expr.
  rewrite H2.
  instantiate (1:=a1).
  repeat intro; simpl; auto.

  rewrite H.
  unfold eval_expr.
  rewrite H0.
  instantiate (1:=a). (* XXX this is wrong!!! have to figure out how to make coq happy *)
  (* XXX same double-heap-read issue as above *)
  admit.

  intro; apply mapsto_imp_ex_mapsto.

  intro. intro.

  unfold eval_expr.
  unfold crash_inv.
  unfold fst. unfold lne_lkinvs.
  exists x0.
  admit.

  eapply ht_seq.
  eapply ht_assign.
  intro; normalize. unfold typeof_expr. unfold type_of_var.
  repeat intro; simpl; auto.

  eapply ht_seq.

  (* Parentheses weeeee *)
  apply ht_p_consequence with (P:=fun rho : Locals =>
       !! (get_locals rho counter3 = Some (eval_expr (minus2 counter2) rho)) &&
       (!! (get_locals rho counter2 = Some (eval_expr (add2 counter1) rho)) &&
        (!! (get_locals rho counter1 = Some a2) &&
         (!! (get_locals rho counterptr =
              Some (eval_expr (e_getlockaddr (t_addr t_nat) (e_read lk)) rho)) &&
          (!! (get_locals rho lk = Some a0) &&
           (!! typeof_val a (t_addr (t_lock t_nat)) &&
            !! (get_locals rho lne_lkptr = Some a) && !! (a = v_addr lkptr))) *
          mapsto lkptr (v_lock a1)))) * mapsto a1 a). intro; normalize.

  (* XXX another store, so alllll the same issues as above *)
  assert (exists n1, a2 = v_nat n1) by admit.
  assert (exists a, a0 = v_lock a) by admit.
  destruct H. destruct H0.
  assert (a1 = x0) by admit.

  eapply ht_store; intro; normalize;
  unfold eval_expr; unfold typeof_expr; unfold type_of_var.

  instantiate (1:=t_nat).
  repeat intro; simpl; auto.

  rewrite H2.
  repeat intro; simpl; auto.

  instantiate (1:=a1).
  rewrite H5.
  unfold eval_expr.
  rewrite H6.
  rewrite H0.
  rewrite H1.
  repeat intro; simpl; auto.
  rewrite H2.
  unfold eval_expr.
  rewrite H3.
  unfold eval_expr.
  rewrite H4.
  rewrite H.
  assert (x = x + 2 - 2) by omega.
  rewrite <- H9.
  instantiate (1:=a2).
  repeat intro; simpl; auto.

  intro; apply mapsto_imp_ex_mapsto.
  repeat intro.
  exists a1. admit.
  eapply ht_seq.

  (* parensss *)
  apply ht_p_consequence with (P:=(fun rho : Locals =>
       !! (get_locals rho counter3 = Some (eval_expr (minus2 counter2) rho)) &&
       (!! (get_locals rho counter2 = Some (eval_expr (add2 counter1) rho)) &&
        (!! (get_locals rho counter1 = Some a2) &&
         (!! (get_locals rho counterptr =
              Some (eval_expr (e_getlockaddr (t_addr t_nat) (e_read lk)) rho)) &&
          (!! (get_locals rho lk = Some a0) &&
           (!! typeof_val a (t_addr (t_lock t_nat)) &&
            !! (get_locals rho lne_lkptr = Some a) && !! (a = v_addr lkptr)))))) *
          mapsto lkptr (v_lock a1) * mapsto a1 a2)).
  intro; normalize.

  assert (exists n1, a = v_addr n1) by admit.
  destruct H.

  eapply ht_putlock; intro; normalize;
  unfold eval_expr; unfold type_of_var; unfold typeof_expr; subst.
  instantiate (1:=t_nat).
  repeat intro; simpl; auto.

  rewrite H6.
  instantiate (1:=lkptr).
  rewrite sepcon_left_corable; normalize.
  rewrite H.
  repeat intro; simpl; auto.
  instantiate (1:=a1).
  instantiate (1:=a0).
  admit.
  
  unfold reg_inv; unfold snd; unfold lne_lkinvs.
  (* Ugh, need the other props here... *)
  admit. admit.

  eapply ht_seq.
  eapply ht_return.
  intro; normalize.
  intro; normalize.
  rewrite sepcon_assoc.
  rewrite sepcon_left_corable; normalize.
  (* somehow I got two lkptrs starred together ........ *)
  admit.

  eapply ht_skip.
Admitted.




(*
  eapply ht

  

  unfold eval_expr. unfold e_getlockaddr.
  eapply ht_getlock_noex.
  po












(* XXX the below is from before changing to SSA. *)
Lemma lock_nat_even_sound' : forall lkptr,
  {{{ lne_lkinvs }}}
  {{{ (fun a =>
        ex_mapsto lkptr)
  }}}
  {{{ (fun a =>
        !!(a = v_addr lkptr)
        && ex_mapsto lkptr)
  }}}
    lock_nat_even
  {{{ (fun a => fun r =>
        ex_mapsto lkptr)
  }}}
  {{{ (fun a => fun r =>
        !!(a = v_addr lkptr)
        && ex_mapsto lkptr)
  }}}.
Proof.
  intro; unfold example2; apply ht_proc; intros.
  unfold lne_lkptr.
  unfold type_of_var.
  eapply ht_seq.
  apply ht_p_consequence with (P:=(fun rho : Locals =>
       !! typeof_val a (t_addr (t_lock t_nat)) &&
       !! (get_locals rho (mkvar (t_addr (t_lock t_nat)) 0) = Some a) &&
       !! (a = v_addr lkptr) * ex_mapsto lkptr)).
  intro. normalize. rewrite sepcon_comm. normalize.

  eapply ht_load; intro; normalize.
  unfold typeof_expr; rewrite H0; unfold type_of_var; auto.
  unfold eval_expr; rewrite H0; auto.

  (* Need to do this *before* the eapply *)
  apply lift_exists; intro.
  apply lift_exists; intro.

  eapply ht_seq.
  apply ht_p_consequence with (P:=(fun rho : Locals =>
       !! (eval_expr (e_read (mkvar (t_addr (t_lock t_nat)) 0))
             (set_locals (mkvar (t_lock t_nat) 1) a0 rho) = v_addr lkptr) &&
       (!! typeof_val a (t_addr (t_lock t_nat)) &&
        !! (get_locals (set_locals (mkvar (t_lock t_nat) 1) a0 rho)
              (mkvar (t_addr (t_lock t_nat)) 0) = Some a) &&
        !! (a = v_addr lkptr)) *
       !! (get_locals rho (mkvar (t_lock t_nat) 1) = Some a1) *
       ex_mapsto lkptr)).
  intro. normalize.
  rewrite sepcon_prop_prop.
  rewrite sepcon_left_corable; normalize.
  destruct H2.
  rewrite sepcon_comm.
  intro.
  intro.
  inversion H4.
  unfold ex_mapsto.
  destruct H5.
  exists x0. exists x1.
  destruct H5. destruct H6.
  repeat split; auto.
  exists a1. apply H7. (* XXX WHY WAS THIS SO ANNOYING *)

  eapply ht_getlock.
  instantiate (1:=t_nat).
  (* XXX some kind of type soundness. Ignore. *)
  admit.

  intro; normalize.
  repeat intro.
  (* don't feel like finding the relevant NatMap lemmas rn *)
  assert ( get_locals x
       (mkvar (t_addr (t_lock t_nat)) 0) = Some a) by admit.
  rewrite H3.
  inversion H2.
  destruct H4. destruct H4. destruct H5. inversion H5. simpl. auto. (* really gotta figure out how to pull things out... *)
  intro. intro. intro. exists a. auto.

  apply lift_exists.
  intro.

  eapply ht_seq.
  eapply ht_assign.
  intro.
  normalize.
  unfold typeof_expr.
  unfold type_of_var.
  repeat intro. normalize. simpl; auto.
  apply lift_exists.
  intro.
  instantiate (1:=v_undef).
  eapply ht_seq.
  unfold reg_inv, crash_inv, lne_lkinvs, fst, snd.
  
  unfold ex_mapsto.

  eapply ht_load.

  intro.
  normalize.

  unfold get_locals.
  unfold get_locals, set_locals in H1.
  
  rewrite H1.

  try repeat intro.
  unfold typeof_expr. rewrite H0. simpl. auto.
  unfold eval_expr.
  rewrite H0. normalize.

  unfold assign_forward_load.

  apply ht_p_consequence with (P:=fun rho : Locals =>
             !! (get_locals rho (mkvar (t_lock t_nat) 1) = Some ?a) &&
             (EX old : value,
              !! (eval_expr (e_read (mkvar (t_addr (t_lock t_nat)) 0))
                    (set_locals (mkvar (t_lock t_nat) 1) old rho) =
                  v_addr lkptr) && mapsto lkptr ?a && ex_mapsto lkptr)).
  intro.
  normalize.
  rewrite sepcon_comm.
  normalize.
  eapply ht_getlock; intro; normalize.
  eapply ht_seq.
  

  instantiate (1:=lkptr).

  rewrite sepcon_left_corable in H1; normalize.
  normalize in H1.
  destruct H1; auto.

  rewrite sepcon_left_corable; normalize.

  unfold reg_inv, lne_lkinvs, snd.

  intro.
  intro.

  (* XXX some kind of typechecking here? This is madness... *)
  (*
  simpl in H1.
  unfold predicates_sa.prop in H1.
  inversion H1.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H5.
  simpl in H6.
  remember (x3 resource) as r.
  destruct r; try contradiction.
  destruct v; try contradiction.
  *)

  assert ((mapsto lkptr (v_lock resource) *
      (fun w : world =>
       match w resource with
       | Some v_unit => False
       | Some (v_nat n) => n = 4
       | Some (v_bool _) => False
       | Some (v_pair _ _) => False
       | Some (v_list _ _) => False
       | Some (v_addr _) => False
       | Some (v_lock _) => False
       | Some v_undef => False
       | None => False
       end) * TT)%logic a) by admit.



 normalize.

  normalize.

  destruct (x3 resource).
  destruct t.
  unfold TT in H1.
  unfold prop in H1.

    simpl in H1.

  unfold ex_mapsto. intro. intro.
  exists (v_lock resource).
  unfold reg_inv, lne_lkinvs in H1.
  unfold snd in H1.
  assert (type_of resource = t_nat).


  rewrite <- sepcon_left_corable in H1; normalize in H1.
  rewrite sepcon_comm in H1;
  rewrite sepcon_left_corable in H1; normalize in H1.
  

  eapply ht_load; intro; normalize.
  Search (_ * _ = _ && _).

 inversion H1. destruct H1. intro. intro.
  unfold type_of_var.
  unfold typeof_expr.
  rewrite H0.
  unfold type_of_var.
  normalize. simpl. auto.

  try repeat intro.
  unfold eval_expr.
  rewrite H0.
  simpl. auto.

  eapply ht_seq.
  unfold assign_forward_load.
  intro.
  eapply ht_getlock.

  try repeat intro.
   

  instantiate (1:=(mkvar (t_addr (t_lock t_nat)) 0)).
  unfold typeof_val in H. simpl in H.
  unfold type_of_var.
  eapply ht_getlock with (lkptr0:=lkptr).
  intro.
  repeat apply andp_right; normalize.
  instantiate (1:=lk).
 normalize.
  try repeat intro.
  destruct H. destruct H0. destruct H.
  repeat split; normalize.
  simpl.

  admit.
  
  
  intro.
  intro.
  intro.
  split.
  auto.
  unfold prop.
  simpl.
  inversion H.
  unfold ex_mapsto.
  exists x0.
