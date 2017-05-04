
Require Import msl.msl_direct.
Require Import msl.Coqlib2.
(*Require Import msl.rmaps.*)
(*Require Import msl.rmaps_lemmas.*)
Require Import veric.lift.
Require Import msl.seplog.
Require Import msl.log_normalize.
Require Import ast.
Require Import List.
Import ListNotations.

Definition world := ((addr -> option value) * (disk_addr -> option value))%type.

Instance Join_world: Join world :=
	Join_prod
	    (addr -> option value) (Join_fun addr (option value) (Join_lower (Join_discrete value)))
	    (disk_addr -> option value) (Join_fun disk_addr (option value) (Join_lower (Join_discrete value))).

Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Sep_alg world := _.
Instance Canc_world : Canc_alg world := _.
Proof.
Admitted.
Instance Disj_world : Disj_alg world := _.
Proof.
Admitted.
Instance Nm: NatDed (pred world) := _.
Proof.
Admitted.

Definition assertion := env -> pred world.

Definition get_heap {A B} (w:A*B) := fst w.
Definition get_disk {A B} (w:A*B) := snd w.

Definition den (s: state) : world := (table_get (get_heap s), table_get (get_disk s)).

Definition defined (x: var) : assertion :=
   fun rho => fun w => exists v, table_get rho x = Some v.

Definition subst (x : var) (y : value) (P: assertion) : assertion :=
   fun rho => fun w => P (table_set x y rho) w.
(*
(* XXX *_mapsto has to involve vars? *)
Definition heap_mapsto (x y: var) : pred world :=
 fun w =>
    exists ax, get_stack w x = Some (v_addr ax) /\
    exists ay, get_stack w y = Some ay /\
    forall a, if eq_dec a ax then get_heap w a = Some ay else get_heap w a = None.

Definition disk_mapsto (x y: var) : pred world :=
 fun w =>
    exists ax, get_stack w x = Some (v_addr ax) /\
    exists ay, get_stack w y = Some ay /\
    forall a, if eq_dec a ax then get_disk w a = Some ay else get_disk w a = None.

Definition equal (x y: var) : pred world :=
            fun w => fst w x = fst w y.
*)
(* XXX local?? *)
Inductive modvars : stmt -> var -> Prop :=
| mod_assign: forall x e, modvars (s_assign x e) x
| mod_load: forall x l, modvars (s_load x l) x
| mod_call: forall x p e, modvars (s_call x p e) x
| mod_block1: forall x s ss, modvars s x -> modvars (s_block (s :: ss)) x
| mod_block2: forall x s ss, modvars (s_block ss) x -> modvars (s_block (s :: ss)) x
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

Definition lift0 {B} (P: B) : env -> B := fun _ => P.
Definition lift1 {A1 B} (P: A1 -> B) (f1: env -> A1) : env -> B := fun rho => P (f1 rho).
Definition lift2 {A1 A2 B} (P: A1 -> A2 -> B) (f1: env -> A1) (f2: env -> A2):
   env -> B := fun rho => P (f1 rho) (f2 rho).

(*Definition local: (world -> Prop) -> world -> pred world :=  lift1 prop.*)

Local Open Scope logic.
Inductive hoare_stmt :
  (value -> assertion) -> (* retC *)
  (value -> assertion) -> (* ret *)
  (*(lock_type -> addr -> (s_prop * s_prop)) -> *)
  assertion -> assertion -> stmt -> assertion -> assertion -> Prop :=

| ht_skip : forall retC ret,
            forall P C,
            hoare_stmt retC ret
                       C P (skip) C P

| ht_block : forall retC ret,
             forall PC RC QC P R Q s ss,
             hoare_stmt retC ret
                        PC P s RC R ->
             hoare_stmt retC ret
                        RC R (s_block ss) QC Q ->
             hoare_stmt retC ret
                        PC P (s_block (s::ss)) QC Q

| ht_if : forall retC ret,
          forall PC QC P Q e_b s1 s2,
          hoare_stmt retC ret
                     PC (fun rho => P rho && !!((eq (v_bool true) (eval_expr e_b rho)))) s1 QC Q ->
          hoare_stmt retC ret
                     PC (fun rho => P rho && !!((eq (v_bool true) (eval_expr e_b rho)))) s2 QC Q ->
          hoare_stmt retC ret
                     PC P (s_if e_b s1 s2) QC Q

| ht_consequence : forall retC ret,
                   forall PC PC' QC P P' Q Q' s,
                   hoare_stmt retC ret
                              PC P s QC Q ->
                   (forall rho, PC' rho |-- PC rho) ->
                   (forall rho, P' rho |-- P rho) ->
                   (forall rho, Q rho |-- Q' rho) ->
                   hoare_stmt retC ret
                              PC' P' s QC Q'

| ht_frame : forall retC ret,
             forall PC QC P Q R s,
             hoare_stmt retC ret
                        PC P s QC Q ->
             hoare_stmt retC ret
                        PC (fun rho => (P rho) * (R rho))%pred s QC (fun rho => (Q rho) * (R rho))%pred
(* XXX why pred instead of logic  * *)

| ht_return : forall (retC : value -> assertion) (ret : value -> assertion),
              forall e PC P,
              (forall rho, PC rho |-- retC (eval_expr e rho) rho) ->
              (forall rho, P rho |-- ret (eval_expr e rho) rho) ->
              hoare_stmt retC ret
                         PC P (s_return e) FF FF

| ht_while : forall retC ret,
             forall C P e_b s,
             hoare_stmt retC ret
                        C (fun rho => P rho && !!(eq (v_bool true) (eval_expr e_b rho))) s C P ->
             hoare_stmt retC ret
                        C P (s_while e_b s) C (fun rho => P rho && !!(eq (v_bool false) (eval_expr e_b rho)))

| ht_assign : forall retC ret,
              forall C P v e,
              hoare_stmt retC ret
                         C P (s_assign v e)
                           (fun (rho:env) => EX old:value,
                  (* QC *)   (!!(table_get rho v = Some (eval_expr e (table_set v old rho)))
                              && C (table_set v old rho)))
                           (fun (rho:env) => EX old:value,
                   (* Q *)   (!!(table_get rho v = Some (eval_expr e (table_set v old rho)))
                              && P (table_set v old rho)))

with hoare_proc :
  (value -> assertion) -> (value -> assertion) -> proc -> 
  (value -> value -> assertion) -> (value -> value -> assertion) -> Prop :=
| ht_proc : forall PC QC P Q v s,
               (forall a, hoare_stmt (QC a) (Q a) (PC a) (fun s => !!(table_get s v = Some a) && (P a s)) s FF FF) ->
               hoare_proc PC P (p_proc v s) QC Q.


Notation "{{ retC }} {{ ret }} ||- {{ PC }} {{ P }} c {{ QC }} {{ Q }}" :=
  (hoare_stmt retC ret PC P c QC Q) (at level 90, c at next level).

Notation "{{{ PC }}} {{{ P }}} p {{{ QC }}} {{{ Q }}}" :=
  (hoare_proc PC P p QC Q) (at level 90, p at next level).


Definition example1 :=
  p_proc (4) (s_block [
    s_return (e_read (4))
  ]).

Lemma pre_false : forall rc r s QC Q,
  {{ rc }} {{ r }} ||-
  {{FF}} {{FF}} s {{ QC }} {{ Q }}.
Proof.
  intros.
  induction s; admit.
(*
  induction l.
  apply ht_consequence with (P:=Q)(PC:=QC)(Q:=Q); norm.
  apply ht_skip.

  apply ht_block with (R:=FF) (RC:=FF).
*)
Admitted.

Lemma example1_sound :
  {{{ fun _ => lift0 emp }}} {{{ fun _ => lift0 emp }}} example1 
    {{{ fun _ => fun _ => lift0 emp }}} {{{ fun a => fun r => !!(r = a)}}}.
Proof.
  unfold example1.
  apply ht_proc.
  intro.
  apply ht_block with (RC:=FF) (R:=FF).
  apply ht_return; normalize.
  intros.
  unfold eval_expr.
  rewrite H.
  normalize.
  (* XXX is this hard because of the environment?? *)
  unfold TT.
  unfold lift0.
  unfold prop.
  simpl.
  normalize.

  apply pre_false.
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
