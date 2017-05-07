Require Import msl.base.

Require Import msl.msl_direct.
Require Import msl.seplog.

Require Import msl.alg_seplog_direct.


Require Import msl.Coqlib2.
Require Import msl.log_normalize.

Require Import ast.
Require Import List.
Import ListNotations.

Require Import table.

Definition env := table var value.
Definition state := table addr value.



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

Definition assertion := env -> pred world.

Definition den (s: state) : world := (table_get s).

Definition defined (x: var) : assertion :=
   fun rho => fun w => exists v, table_get rho x = Some v.

Definition subst (x : var) (y : value) (P: assertion) : assertion :=
   fun rho => fun w => P (table_set x y rho) w.

Definition mapsto (x:addr) (y:value) : pred world :=
 fun w =>
    exists v, w x = Some v /\
    y = v
.

Definition ex_mapsto (x:addr) : pred world :=
 fun w =>
    exists v, w x = Some v
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
  forall rho w v, P rho w -> P (table_set x v rho) w.

Definition subset (S1 S2: var -> Prop) :=
  forall x, S1 x -> S2 x.

(* XXX XXX XXX Change this *)

Function eval_expr (e : expr) (env : env) : value :=
  match e with
  | e_read v =>
    match table_get env v with
    | Some val => val
    | None => v_undef
    end
  | e_value v => v
  | e_cond b e1 e2 =>
    match eval_expr b env with
    | v_bool true => eval_expr e1 env
    | v_bool false => eval_expr e2 env
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
  | v_list t' => t_list t = t
  | v_addr (_,_,t') => t_addr t' = t
  | v_lock (_,_,t') => t_lock t' = t
  | v_undef => False
  end.

Function typeof_expr (e : expr) (rho : env) (t : type) : Prop :=
  match e with
  | e_read v => match table_get rho v with
                | None => False
                | Some _ => snd v = t
                end
  | e_value v => typeof_val v t
  | e_cond eb e1 e2 =>
    typeof_expr eb rho t_bool /\
    typeof_expr e1 rho t /\
    typeof_expr e2 rho t
  end.

Lemma tt_sound :
  forall {v} {a : value} {rho : env}, table_get rho v = Some a ->
  typeof_val a (snd v).
Proof.
Admitted.

Notation ETT := (fun (_ : env) => TT).
Notation ATT := (fun (_ : value) => TT).
Notation ARTT := (fun (_ : value) => fun (_ : value) => TT).
Notation EFF := (fun (_ : env) => FF).
Notation AFF := (fun (_ : value) => FF).
Notation ARFF := (fun (_ : value) => fun (_ : value) => FF).

Notation e_emp := (fun (_ : env) => FF).
Notation a_emp := (fun (_ : value) => FF).
Notation ar_emp := (fun (_ : value) => fun (_ : value) => FF).

(*
Definition lift0 {B} (P: B) : env -> B := fun _ => P.
Definition lift1 {A1 B} (P: A1 -> B) (f1: env -> A1) : env -> B := fun rho => P (f1 rho).
Definition lift2 {A1 A2 B} (P: A1 -> A2 -> B) (f1: env -> A1) (f2: env -> A2):
   env -> B := fun rho => P (f1 rho) (f2 rho).
*)
(*Definition local: (world -> Prop) -> world -> pred world :=  lift1 prop.*)
Local Open Scope logic.

Definition assign_forward (v : var) (e : expr) (P : assertion) (rho : env) := 
  EX old:value,
    (!!(table_get rho v = Some (eval_expr e (table_set v old rho)))
    && P (table_set v old rho)).

Definition assign_forward_load (v : var) (a:value) (ptr:addr) (e : expr) (P : assertion) (rho : env) := 
  !!(table_get rho v = Some a) && EX old:value, (
     !!(eval_expr e (table_set v old rho) = v_addr ptr)
     && mapsto ptr a
     && P (table_set v old rho)).


(* XXX make this an option (pred world * pred world)? Some kind of type checking
       on the address? We want to keep t_lock t_nat and t_nat in different address
       spaces. *)
Notation lk_inv_map := (value -> pred world * pred world).

Definition crash_inv (lk:value) (lk_invs : lk_inv_map) :=
  fst (lk_invs lk).

Definition reg_inv (lk:value) (lk_invs : lk_inv_map) :=
  snd (lk_invs lk).

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
              (forall rho, PC rho |-- retC (eval_expr e rho)) ->
              (forall rho, P rho |-- ret (eval_expr e rho)) ->
              hoare_stmt retC ret lk_invs
                         PC P (s_return e) ETT EFF

| ht_while : forall retC ret lk_invs,
             forall C P e_b s,
             hoare_stmt retC ret lk_invs
                        C (fun rho => P rho && !!(eq (v_bool true) (eval_expr e_b rho))) s C P ->
             hoare_stmt retC ret lk_invs
                        C P (s_while e_b s) C (fun rho => P rho && !!(eq (v_bool false) (eval_expr e_b rho)))

| ht_assign : forall retC ret lk_invs,
              forall C P v e,
              hoare_stmt retC ret lk_invs
                           C
                           (fun rho => P rho && !!(typeof_expr e rho (snd v)))
                             (s_assign v e)
                           (assign_forward v e C)
                           (assign_forward v e P)

(* XXX special frame for PC and QC. Also, this seems to weakly constrain the old rv... *)
(* XXX XXX XXX Just force rv to be a new var for now... *)
| ht_call : forall {retC ret lk_invs},
            forall {PC PC' P P' QC QC' Q Q' rv rt pv s e val},
            hoare_proc lk_invs PC P (p_proc rt pv s) QC Q ->
            (forall rho, PC' rho |-- PC (eval_expr e rho)) ->
            (forall rho, P' rho |-- P (eval_expr e rho)) ->
            hoare_stmt retC ret lk_invs
                       PC'
                       P'
                           (s_call rv (p_proc rt pv s) e)
                       (fun rho => !!(table_get rho rv = Some val) &&
                                   QC' rho *
                                   QC (eval_expr e rho) val)
                       (fun rho => !!(table_get rho rv = Some val) &&
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

| ht_getlock : forall retC ret lk_invs,
               forall v a lk, (* XXX should this go as an EX? *)
               hoare_stmt retC ret lk_invs
                          (fun rho => emp)
                          (fun rho => EX t:type, (!!(snd v = t_addr (t_lock t))
                                      && !!(table_get rho v = Some (v_addr a))
                                      && mapsto a lk))
                            (s_getlock v)
                          (fun rho => crash_inv lk lk_invs)
                          (fun rho => EX t:type, (!!(snd v = t_addr (t_lock t))
                                      && !!(table_get rho v = Some (v_addr a))
                                      && mapsto a lk * reg_inv lk lk_invs))

| ht_putlock : forall retC ret lk_invs,
               forall v a lk, (* XXX should this go as an EX? *)
               hoare_stmt retC ret lk_invs
                          (fun rho => crash_inv lk lk_invs)
                          (fun rho => EX t:type, (!!(snd v = t_addr (t_lock t))
                                      && !!(table_get rho v = Some (v_addr a))
                                      && mapsto a lk * reg_inv lk lk_invs))
                            (s_putlock v)
                          (fun rho => emp)
                          (fun rho => EX t:type, (!!(snd v = t_addr (t_lock t))
                                      && !!(table_get rho v = Some (v_addr a))
                                      && mapsto a lk))

| ht_load : forall {retC ret lk_invs},
            forall {P C e v},
            forall a ptr,
            hoare_stmt retC ret lk_invs
                           C
                           (fun rho => P rho && !!(typeof_expr e rho (t_addr (snd v)))
                                       && !!(eval_expr e rho = v_addr ptr)
                                       * mapsto ptr a)
                              (s_load v e)
                           (assign_forward_load v a ptr e C)
                           (assign_forward_load v a ptr e P)

| ht_store : forall {retC ret lk_invs},
            forall {P C e v},
            forall ptr t val,
            hoare_stmt retC ret lk_invs
                           C
                           (fun rho => P rho && !!(snd v = t_addr t)
                                       && !!(typeof_expr e rho t)
                                       && !!(table_get rho v = Some (v_addr ptr))
                                       && !!(eval_expr e rho = val)
                                       * ex_mapsto ptr)
                              (s_store v e)
                           C
                           (fun rho => P rho && !!(snd v = t_addr t)
                                       && !!(table_get rho v = Some (v_addr ptr))
                                       * mapsto ptr val)
(* XXX First, we can pass off crash conditions in the same way we frame them.
       Second, locks need to be able to be split. *)
| ht_start: forall {retC ret lk_invs},
            forall {F P P' rt pv s e},
            hoare_proc lk_invs a_emp P (p_proc rt pv s) ar_emp ar_emp ->
            (forall rho, P' rho |-- P (eval_expr e rho)) ->
            hoare_stmt retC ret lk_invs
                       e_emp
                       (fun rho => F rho * P' rho)
                           (s_start (p_proc rt pv s) e)
                       e_emp
                       F

(* Stmt rules not directly related to the language *)

| ht_consequence : forall retC ret lk_invs,
                   forall PC PC' QC QC' P P' Q Q' s,
                   hoare_stmt retC ret lk_invs
                              PC P s QC Q ->
(* XXX  want these? *)
                   (forall rho, PC rho |-- PC' rho) -> 
                   (forall rho, QC' rho |-- QC rho) -> 
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

(* XXX Don't have to frame out other locks due to the resource invariant! *)
| ht_frame_lock : forall retC ret lk_invs,
                  forall PC QC P Q s a l,
                  hoare_stmt retC ret lk_invs
                             PC P s QC Q ->
                  hoare_stmt retC ret lk_invs
                             (fun rho => (PC rho) * crash_inv l lk_invs)
                             (fun rho => (P rho) * reg_inv l lk_invs * mapsto a l) 
                                 s
                             (fun rho => (QC rho) * crash_inv l lk_invs)
                             (fun rho => (Q rho) * reg_inv l lk_invs * mapsto a l)

(* XXX semax_extract_prop? *)

(* These *don't* take assertions, because (for now) they don't need to take
 * the environment (argument / return value are explicitly passed in) *)
with hoare_proc :
  lk_inv_map ->
  (value -> pred world) -> (value -> pred world) -> proc -> 
  (value -> value -> pred world) -> (value -> value -> pred world) -> Prop :=
| ht_proc : forall PC QC P Q t v s lk_invs,
               (forall a, hoare_stmt (QC a) 
                                     (fun r => !!(typeof_val r t) && Q a r)
                                     lk_invs
                                     (fun rho => PC a)
                                     (fun rho => !!(typeof_val a (snd v)) && 
                                                 !!(table_get rho v = Some a) && P a)
                                     s
                                     ETT
                                     EFF) ->
               hoare_proc lk_invs PC P (p_proc t v s) QC Q.

Notation "{{ retC }} {{ ret }} {{ lk_invs }} ||- {{ PC }} {{ P }} s {{ QC }} {{ Q }}" :=
  (hoare_stmt retC ret lk_invs PC P s QC Q) (at level 90, s at next level).

Notation "'Return-Crash:' retC 'Return:' ret 'Lock-Invs:' lk_invs 'Pre-Crash:' PC 'Pre:' P 'Post-Crash:' QC 'Post:' Q 'Stmt:' s" :=
  (hoare_stmt retC ret lk_invs PC P s QC Q) (at level 89, s at next level, format
      "'[v' 'Return-Crash:' '[  ' '/'  retC ']' '//' 'Return:' '[  ' '/'  ret ']' '//' 'Lock-Invs:' '[  ' '/'  lk_invs ']' '//' 'Pre-Crash:' '[  ' '/'  PC ']' '//' 'Pre:' '[  ' '/'  P ']' '//' 'Post-Crash:' '[  ' '/'  QC ']' '//' 'Post:' '[  ' '/'  Q ']' '//' 'Stmt:' '[  ' '/'  s ']' ']'").

Notation "{{{ lk_invs }}} {{{ PC }}} {{{ P }}} p {{{ QC }}} {{{ Q }}}" :=
  (hoare_proc lk_invs PC P p QC Q) (at level 90, p at next level).

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
  p_proc t_nat (4,t_nat) ([{
    s_return (e_read (4,t_nat)) ;
    s_skip ;
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
  {{{ fun _ => emp }}} {{{ fun _ => emp }}} example1
    {{{ fun _ => fun _ => emp }}} {{{ fun a => fun r => !!(r = a)}}}.
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
  p_proc t_nat (4,t_nat) ([{
    s_call (5,t_nat) example1 (e_read (4,t_nat)) ;
    s_return (e_read (5,t_nat)) ;
  }]).

Lemma example2_sound : forall lk_invs,
  {{{ lk_invs }}}
  {{{ fun _ => emp }}} {{{ fun _ => emp }}} example2 
    {{{ fun _ => fun _ => emp }}} {{{ fun a => fun r => !!(r = a)}}}.
Proof.
  intro; unfold example2; apply ht_proc; intros.
  eapply ht_seq.
  pose proof example1_sound.
  unfold example1 in *.
  eapply (ht_call (H lk_invs)); normalize.

  (* Shouldn't it know this was the arg? *)
  instantiate (1:=a).
  apply ht_return; normalize.
  instantiate (1:=(fun _ => emp)).
  intros; intro; intro; trivial.
  intros.
  instantiate (1:=(fun _ => emp)).
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
Qed.


(*
Inductive safe: (list command * state) -> Prop :=
| safe_step: forall cs1 cs2, step' cs1 cs2 -> safe cs2 -> safe cs1
| safe_halt: forall s, safe (nil, s).

Definition guards (P: assertion) (k: list command) : Prop :=
  forall s, P (den s) -> safe (k,s).

Definition semax (P: assertion) (c: command) (Q: assertion) : Prop :=
  forall F, subset (modvars c) (nonfreevars F) ->
  forall k, guards (Q*F) k -> guards (P*F) (c :: k).

Lemma semax_assign: forall P x y,
      semax (defined y && subst x y P) (Assign x y) P.
Proof.
  intros P x y F H k H0 [stk hp] H1.
  destruct H1 as [[stk1 hp1] [[stk2 hp2] [? [[[v ?] ?] ?]]]].
  simpl in *.
 destruct H1 as [[? ?] ?]; simpl in *; subst; auto.
  eapply safe_step.
  econstructor; eauto.
  apply H0.
  exists (fun_set (table_get stk) x (table_get stk y), hp1).
  exists (fun_set (table_get stk) x (table_get stk y), hp2).
  split; [|split].
  split; auto. split; auto.
  simpl; extensionality i.
  unfold var, fun_set.
  destruct (eq_dec i x); auto.
  apply H3.
  apply (H x).
  constructor.
  apply H4.
Qed.

Lemma semax_load: forall x y z, x <> y -> x <> z ->
       semax (mapsto y z)  (Load x y) (mapsto y z && equal x z).
Proof.
  intros x y z Hxy Hxz F H k H0 [stk hp] H1.
 destruct H1 as [[stk1 hp1] [[stk2 hp2] [? [[ax [? [ay [? ?]]]] ?]]]].
 simpl in *.
 destruct H1 as [[? ?] ?]; simpl in *; subst.
 apply safe_step with  (k, (table_set x ay stk, hp)).
 econstructor; eauto.
 generalize (H4 ax); intros.
 destruct (eq_dec ax ax); [ | contradiction n; auto].
 generalize (H7 ax).  rewrite H1; intro. inv H6; auto.  destruct H11.
 apply H0.
 exists (table_get (table_set x ay stk), hp1).
 exists (table_get (table_set x ay stk), hp2).
 repeat split; simpl; auto.
 exists ax; split; simpl; auto.
 destruct (eq_dec y x); [ contradiction Hxy; auto | auto ].
 exists ay; split; simpl; auto.
 destruct (eq_dec z x); [ contradiction Hxz; auto | auto].
 hnf; simpl.
 destruct (eq_dec x x);  [ | contradiction n; auto].
 destruct (eq_dec z x); [ contradiction Hxz; auto | auto].
 apply H; auto. constructor.
Qed.

Lemma semax_store: forall x y z,
         semax (defined y && mapsto x z) (Store x y) (mapsto x y).
Proof.
 intros x y z F H k H0 [stk hp] H1.
 destruct H1 as [[stk1 hp1] [[stk2 hp2] [[[H2a H2b] H2] [[[ay ?] [ax [? [az [? ?]]]]] ?]]]].
 simpl in *; subst.
 apply safe_step with (k, (stk, table_set ax ay hp)).
 econstructor; eauto.
 apply H0.
 exists (table_get stk, fun_set hp1 ax (Some ay)); exists (table_get stk, hp2).
 repeat split; simpl; auto.
 intro i. unfold fun_set.
 specialize (H5 i). specialize (H2 i).
 change adr with nat in H5|-*.
 destruct (@eq_dec nat _ i ax). rewrite H5 in H2.
 inv H2. constructor.  inv H10.  rewrite H5 in *. auto.
 exists ax. split; auto. exists ay; split; auto.
 intro a; specialize (H5 a).
 unfold fun_set; change adr with nat in *. simpl.
 destruct (eq_dec a ax); simpl; auto.
Qed.


Lemma semax_seq: forall P c1 Q c2 R,
  semax P c1 Q -> semax Q c2 R -> semax P (Seq c1 c2) R.
Proof.
 intros P c1 Q c2 R C1 C2 F H k H0 s H1.
 assert (safe (c1::c2::k,s)).
2:  inv H2; eapply safe_step; [constructor | eauto]; auto.
 apply (C1 F); auto.
 intros ? ?; apply H; apply mod_seq1; auto.
 apply C2; auto.
 intros ? ?; apply H; apply mod_seq2; auto.
Qed.


Lemma frame: forall F P c Q,
   subset (modvars c) (nonfreevars F) ->
    semax P c Q -> semax (P * F) c (Q * F).
Proof.
 repeat intro.
 rewrite sepcon_assoc in H2,H3.
 assert (guards (P * (F * F0)) (c::k)).
 apply H0; auto.
 intros ? ?.
 specialize (H _ H4); specialize (H1 _ H4).
 clear - H H1.
 repeat intro.
 destruct H0 as [[stk1 hp1] [[stk2 hp2] [[[? ?] ?] [? ?]]]].
 simpl in *; subst.
 exists (fun_set stk x v, hp1); exists (fun_set stk x v, hp2); split; auto.
 split; auto.
 apply H4;  auto.
Qed.

Lemma semax_pre_post:
  forall P P' c Q' Q,
    P |-- P' -> Q' |-- Q -> semax P' c Q' -> semax P c Q.
Proof.
 repeat intro.
 apply (H1 F); auto.
 intros ? ?. apply H3.
 eapply sepcon_derives; try apply H5; auto.
 eapply sepcon_derives; try apply H4; auto.
Qed.

*)
