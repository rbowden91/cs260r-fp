Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Export floyd.canon.
Local Open Scope logic.

Arguments sem_cmp c !t1 !t2 / v1 v2.

(**** BEGIN experimental normalize (to replace the one in msl/log_normalize.v ****)

Lemma prop_true_andp' (P: Prop) {A} {NA: NatDed A}:
  forall (Q: A),  P -> (!! P && Q = Q).
Proof with norm.
intros.
apply pred_ext. apply andp_left2...
apply andp_right... apply prop_right...
Qed.

Ltac norm_rewrite := autorewrite with norm.
 (* New version: rewrite_strat (topdown hints norm).
     But this will have to wait for a future version of Coq
    in which rewrite_strat discharges side conditions.
    According to Matthieu Sozeau, in the Coq trunk as of June 5, 2013,
    rewrite_strat is documented AND discharges side conditions.
    It might be about twice as fast, or 1.7 times as fast, as the old autorewrite.
    And then, maybe use "bottomup" instead of "topdown", see if that's better.

   To test whether your version of Coq works, use this:
Lemma L : forall n, n=n -> n + 1 = S n.
Proof. intros. rewrite <- plus_n_Sm ,<- plus_n_O. reflexivity.
Qed.
Hint Rewrite L using reflexivity : test888.
Goal forall n, S n = n + 1.
intros.
rewrite_strat (topdown hints test888).
match goal with |- S n = S n => reflexivity end.
(* should be no extra (n=n) goal here *)
Qed.
 *)

Lemma typed_false_cmp'':
  forall i j op e1 e2,
   typed_false tint (force_val (sem_cmp op tint tint e1  e2 )) ->
   Vint (Int.repr i) = e1 ->
   Vint (Int.repr j) = e2 ->
   repable_signed i ->
   repable_signed j ->
   Zcmp (negate_comparison op) i j.
Proof.
intros. subst.
unfold sem_cmp in H.
unfold classify_cmp in H. simpl in H.
eapply int_cmp_repr; auto.
unfold typed_false in H; simpl in H.
destruct op; simpl in *;
match goal with |- negb ?A = true => destruct A; inv H; auto
                        | |- ?A = true => destruct A; inv H; auto
 end.
Qed.

Lemma typed_true_cmp'':
  forall i j op e1 e2,
   typed_true tint (force_val (sem_cmp op tint tint e1  e2 )) ->
   Vint (Int.repr i) = e1 ->
   Vint (Int.repr j) = e2 ->
   repable_signed i ->
   repable_signed j ->
   Zcmp op i j.
Proof.
intros. subst.
unfold sem_cmp in H.
unfold classify_cmp in H. simpl in H.
eapply int_cmp_repr; auto.
unfold typed_true in H; simpl in H.
destruct (Int.cmp op (Int.repr i) (Int.repr j)); inv H; auto.
Qed.

(* Equality proofs for all constants from the Compcert Int module: *)
Definition int_wordsize_eq : Int.wordsize = 32%nat := eq_refl.
Definition int_zwordsize_eq : Int.zwordsize = 32 := eq_refl.
Definition int_modulus_eq : Int.modulus = 4294967296 := eq_refl.
Definition int_half_modulus_eq : Int.half_modulus = 2147483648 := eq_refl.
Definition int_max_unsigned_eq : Int.max_unsigned = 4294967295 := eq_refl.
Definition int_max_signed_eq : Int.max_signed = 2147483647 := eq_refl.
Definition int_min_signed_eq : Int.min_signed = -2147483648 := eq_refl.

Ltac repable_signed := 
   pose proof int_wordsize_eq;
   pose proof int_zwordsize_eq;
   pose proof int_modulus_eq;
   pose proof int_half_modulus_eq;
   pose proof int_max_unsigned_eq;
   pose proof int_max_signed_eq;
   pose proof int_min_signed_eq;
   unfold repable_signed in *;
   omega.

Lemma typed_false_ptr:
  forall {t a v},  typed_false (Tpointer t a) v -> v=nullval.
Proof.
unfold typed_false, strict_bool_val, nullval; simpl; intros.
destruct v; try discriminate.
pose proof (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); subst; auto.
inv H.
Qed.
Lemma typed_false_cmp':
  forall op i j,
   typed_false tint (force_val (sem_cmp op tint tint i j )) ->
   Int.cmp (negate_comparison op) (force_int i) (force_int j) = true.
Proof.
intros.
unfold sem_cmp in H.
unfold classify_cmp in H. simpl in H.
rewrite Int.negate_cmp.
destruct i; inv H.
destruct j; inv H1.
simpl in *. destruct (Int.cmp op i i0); inv H0; auto.
Qed.


Lemma typed_true_cmp':
  forall op i j,
   typed_true tint (force_val (sem_cmp op tint tint i j)) ->
   Int.cmp op (force_int i) (force_int j) = true.
Proof.
intros.
unfold sem_cmp in H.
unfold classify_cmp in H. simpl in H.
destruct i; inv H. destruct j; inv H1.
simpl in *. destruct (Int.cmp op i i0); inv H0; auto.
Qed.

Lemma typed_true_ptr:
  forall {t a v},  typed_true (Tpointer t a) v -> isptr v.
Proof.
unfold typed_true, strict_bool_val; simpl; intros.
destruct v; try discriminate.
if_tac in H; inv H. simpl. auto.
Qed.

Lemma int_cmp_repr':
 forall op i j, repable_signed i -> repable_signed j ->
   Int.cmp op (Int.repr i) (Int.repr j) = false ->
   Zcmp (negate_comparison op) i j.
Proof.
intros.
apply int_cmp_repr; auto.
rewrite Int.negate_cmp.
rewrite H1; reflexivity.
Qed.

Lemma typed_false_of_bool:
 forall x, typed_false tint (Val.of_bool x) -> (x=false).
Proof.
unfold typed_false; simpl.
unfold strict_bool_val, Val.of_bool; simpl.
destruct x; simpl;  intuition congruence.
Qed.

Lemma typed_true_of_bool:
 forall x, typed_true tint (Val.of_bool x) -> (x=true).
Proof.
unfold typed_true; simpl.
unfold strict_bool_val, Val.of_bool; simpl.
destruct x; simpl;  intuition congruence.
Qed.

Lemma typed_false_tint:
 forall v, typed_false tint v -> v=nullval.
Proof.
intros.
 hnf in H. destruct v; inv H.
 destruct (Int.eq i Int.zero) eqn:?; inv H1.
 apply int_eq_e in Heqb. subst; reflexivity.
Qed.

Lemma typed_true_tint:
 forall v, typed_true tint v -> v<>nullval.
Proof.
intros.
 hnf in H. destruct v; inv H.
 destruct (Int.eq i Int.zero) eqn:?; inv H1.
 unfold nullval; intro. inv H.
 rewrite Int.eq_true in Heqb. inv Heqb.
Qed.

Lemma typed_false_tint_Vint:
  forall v, typed_false tint (Vint v) -> v = Int.zero.
Proof.
intros. apply typed_false_tint in H. apply Vint_inj in H; auto.
Qed.

Lemma typed_true_tint_Vint:
  forall v, typed_true tint (Vint v) -> v <> Int.zero.
Proof.
intros. apply typed_true_tint in H.
contradict H. subst; reflexivity.
Qed.

Ltac intro_redundant_prop :=
  (* do it in this complicated way because the proof will come out smaller *)
match goal with |- ?P -> _ =>
  ((assert P by immediate; fail 1) || fail 1) || intros _
end.

Ltac fancy_intro aggressive :=
 match goal with
 | |- ?P -> _ => match type of P with Prop => idtac end
 | |- ~ _ => idtac
 end;
 let H := fresh in
 intro H;
 try simple apply ptr_eq_e in H;
 try simple apply Vint_inj in H;
 match type of H with
 | ?P => clear H; (((assert (H:P) by immediate; fail 1) || fail 1) || idtac)
                (* do it in this complicated way because the proof will come out smaller *)
 | ?x = ?y => constr_eq aggressive true;
                     first [subst x | subst y
                             | is_var x; rewrite H
                             | is_var y; rewrite <- H
                             | idtac]
 | isptr ?x => let Hx := fresh "P" x in rename H into Hx
 | is_pointer_or_null ?x => let Hx := fresh "PN" x in rename H into Hx
 | typed_false _ _ =>
        first [simple apply typed_false_of_bool in H
               | apply typed_false_tint_Vint in H
               | apply typed_false_tint in H
               | apply typed_false_ptr in H
               | idtac ]
 | typed_true _ _ =>
        first [simple apply typed_true_of_bool in H
               | apply typed_true_tint_Vint in H
               | apply typed_true_tint in H
               | apply typed_true_ptr in H
               | idtac ]
 | locald_denote _ _ => hnf in H
 | _ => try solve [discriminate H]
 end.


Ltac fancy_intros aggressive :=
 repeat match goal with
  | |- (_ <= _ < _) -> _ => fancy_intro aggressive
  | |- (_ < _ <= _) -> _ => fancy_intro aggressive
  | |- (_ <= _ <= _) -> _ => fancy_intro aggressive
  | |- (_ < _ < _) -> _ => fancy_intro aggressive
  | |- (?A /\ ?B) -> ?C => apply (@and_ind A B C) (* For some reason "apply and_ind" doesn't work the same *)
  | |- _ -> _ => fancy_intro aggressive
  end.

Ltac normalize1 :=
         match goal with
            | |- context [@andp ?A (@LiftNatDed ?T ?B ?C) ?D ?E ?F] =>
                      change (@andp A (@LiftNatDed T B C) D E F) with (D F && E F)
            | |- context [@later ?A  (@LiftNatDed ?T ?B ?C) (@LiftIndir ?X1 ?X2 ?X3 ?X4 ?X5) ?D ?F] =>
                   change (@later A  (@LiftNatDed T B C) (@LiftIndir X1 X2 X3 X4 X5) D F)
                     with (@later B C X5 (D F))
            | |- context [@sepcon ?A (@LiftNatDed ?B ?C ?D)
                                                         (@LiftSepLog ?E ?F ?G ?H) ?J ?K ?L] =>
                   change (@sepcon A (@LiftNatDed B C D) (@LiftSepLog E F G H) J K L)
                      with (@sepcon C D H (J L) (K L))
            | |- context [(?P && ?Q) * ?R] => rewrite (corable_andp_sepcon1 P Q R) by (auto with norm)
            | |- context [?Q * (?P && ?R)] => rewrite (corable_sepcon_andp1 P Q R) by (auto with norm)
            | |- context [(?Q && ?P) * ?R] => rewrite (corable_andp_sepcon2 P Q R) by (auto with norm)
            | |- context [?Q * (?R && ?P)] => rewrite (corable_sepcon_andp2 P Q R) by (auto with norm)
            | |-  derives ?A   ?B => match A with
                   | FF => apply FF_left
                   | !! _ => apply derives_extract_prop0
                   | exp (fun y => _) => apply imp_extract_exp_left; (intro y || intro)
                   | !! _ && _ => apply derives_extract_prop
                   | _ && !! _ => apply derives_extract_prop'
                   | context [ ((!! ?P) && ?Q) && ?R ] => rewrite (andp_assoc (!!P) Q R)
                   | context [ ?Q && (!! ?P && ?R)] =>
                                  match Q with !! _ => fail 2 | _ => rewrite (andp_assoc' (!!P) Q R) end
                 (* In the next four rules, doing it this way (instead of leaving it to autorewrite)
                    preserves the name of the "y" variable *)
                   | context [andp (exp (fun y => _)) _] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply imp_extract_exp_left; intro y
                   | context [andp _ (exp (fun y => _))] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply imp_extract_exp_left; intro y
                   | context [sepcon (exp (fun y => _)) _] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply imp_extract_exp_left; intro y
                   | context [sepcon _ (exp (fun y => _))] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                                apply imp_extract_exp_left; intro y
                   | _ => simple apply TT_prop_right
                   | _ => simple apply TT_right
                   | _ => apply derives_refl
                   end
              | |- _ => solve [auto]
              | |- _ |-- !! (?x = ?y) && _ =>
                            (rewrite (prop_true_andp' (x=y))
                                            by (unfold y; reflexivity); unfold y in *; clear y) ||
                            (rewrite (prop_true_andp' (x=y))
                                            by (unfold x; reflexivity); unfold x in *; clear x)
              |  |- ?ZZ -> ?YY => match type of ZZ with
                                               | Prop => fancy_intros true || fail 1
                                               | _ => intros _
                                              end
              | |- ~ _ => fancy_intro true
              | |- _ => progress (norm_rewrite) (*; auto with typeclass_instances *)
              | |- forall _, _ => let x := fresh "x" in (intro x; repeat normalize1; try generalize dependent x)
              end.

Ltac normalize :=
   autorewrite with gather_prop;
   repeat (((repeat simple apply go_lower_lem1'; simple apply go_lower_lem1)
              || simple apply derives_extract_prop
              || simple apply derives_extract_prop');
              fancy_intros true);
   repeat normalize1; try contradiction.

(****** END experimental normalize ******************)


(* The following line should not be needed, and was not needed
 in Coq 8.3, but in Coq 8.4 it seems to be necessary. *)
Hint Resolve (@LiftClassicalSep environ) : typeclass_instances.

Definition func_ptr' f v := func_ptr f v && emp.

Lemma approx_func_ptr': forall (A: Type) fsig0 cc (P Q: A -> environ -> mpred) (v: val) (n: nat),
  compcert_rmaps.RML.R.approx n (func_ptr' (NDmk_funspec fsig0 cc A P Q) v) = compcert_rmaps.RML.R.approx n (func_ptr' (NDmk_funspec fsig0 cc A (fun a rho => compcert_rmaps.RML.R.approx n (P a rho)) (fun a rho => compcert_rmaps.RML.R.approx n (Q a rho))) v).
Proof.
  intros.
  unfold func_ptr'.
  rewrite !approx_andp; f_equal.
  apply (approx_func_ptr A fsig0 cc P Q).
Qed.

Lemma lift0_unfold: forall {A} (f: A)  rho,  lift0 f rho = f.
Proof. reflexivity. Qed.

Lemma lift0_unfoldC: forall {A} (f: A) (rho: environ),  `f rho = f.
Proof. reflexivity. Qed.

Lemma lift1_unfold: forall {A1 B} (f: A1 -> B) a1 rho,
        lift1 f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.

Lemma lift1_unfoldC: forall {A1 B} (f: A1 -> B) a1 (rho: environ),
        `f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.

Lemma lift2_unfold: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: environ),
        lift2 f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma lift2_unfoldC: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: environ),
        `f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma lift3_unfold: forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) a1 a2 a3 (rho: environ),
        lift3 f a1 a2 a3 rho = f (a1 rho) (a2 rho) (a3 rho).
Proof. reflexivity. Qed.

Lemma lift3_unfoldC: forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) a1 a2 a3 (rho: environ),
        `f a1 a2 a3 rho = f (a1 rho) (a2 rho) (a3 rho).
Proof. reflexivity. Qed.

Lemma lift4_unfold: forall {A1 A2 A3 A4 B} (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4 (rho: environ),
        lift4 f a1 a2 a3 a4 rho = f (a1 rho) (a2 rho) (a3 rho) (a4 rho).
Proof. reflexivity. Qed.

Lemma lift4_unfoldC: forall {A1 A2 A3 A4 B} (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4 (rho: environ),
        `f a1 a2 a3 a4 rho = f (a1 rho) (a2 rho) (a3 rho) (a4 rho).
Proof. reflexivity. Qed.

Hint Rewrite @lift0_unfold @lift1_unfold @lift2_unfold @lift3_unfold @lift4_unfold : norm2.
Hint Rewrite @lift0_unfoldC @lift1_unfoldC @lift2_unfoldC @lift3_unfoldC @lift4_unfoldC : norm2.

Lemma subst_lift0: forall {A} id v (f: A),
        subst id v (lift0 f) = lift0 f.
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift0': forall {A} id v (f: A),
        subst id v (fun _ => f) = (fun _ => f).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift0' : subst.

Lemma subst_lift0C:
  forall {B} id (v: environ -> val) (f: B) ,
          subst id v (`f) = `f.
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift0 (*@subst_lift0'*) @subst_lift0C : subst.

Lemma subst_lift1:
  forall {A1 B} id v (f: A1 -> B) a,
          subst id v (lift1 f a) = lift1 f (subst id v a).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift1':
  forall {A1 B} id v (f: A1 -> B) a,
          subst id v (fun rho => f (a rho)) = fun rho => f (subst id v a rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift1C:
  forall {A1 B} id (v: environ -> val) (f: A1 -> B) (a: environ -> A1),
          subst id v (`f a)  = `f (subst id v a).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift1 (*@subst_lift1'*) @subst_lift1C  : subst.

Lemma subst_lift2:
  forall {A1 A2 B} id v (f: A1 -> A2 -> B) a b,
          subst id v (lift2 f a b) = lift2 f (subst id v a) (subst id v b).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift2':
  forall {A1 A2 B} id v (f: A1 -> A2 -> B) a b,
          subst id v (fun rho => f (a rho) (b rho)) = fun rho => f (subst id v a rho) (subst id v b rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift2C:
  forall {A1 A2 B} id (v: environ -> val) (f: A1 -> A2 -> B) (a: environ -> A1) (b: environ -> A2),
          subst id v (`f a b) = `f (subst id v a) (subst id v b).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift2 (*@subst_lift2'*) @subst_lift2C : subst.

Lemma subst_lift3:
  forall {A1 A2 A3 B} id v (f: A1 -> A2 -> A3 -> B) a1 a2 a3,
          subst id v (lift3 f a1 a2 a3) = lift3 f (subst id v a1) (subst id v a2) (subst id v a3).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift3':
  forall {A1 A2 A3 B} id v (f: A1 -> A2 -> A3 -> B) a1 a2 a3,
          subst id v (fun rho => f (a1 rho) (a2 rho) (a3 rho)) =
          fun rho => f (subst id v a1 rho) (subst id v a2 rho) (subst id v a3 rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift3C:
  forall {A1 A2 A3 B} id (v: environ -> val) (f: A1 -> A2 -> A3 -> B)
                  (a1: environ -> A1) (a2: environ -> A2) (a3: environ -> A3),
          subst id v (`f a1 a2 a3) = `f (subst id v a1) (subst id v a2) (subst id v a3).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift3 (*@subst_lift3'*) @subst_lift3C : subst.

Lemma subst_lift4:
  forall {A1 A2 A3 A4 B} id v (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4,
          subst id v (lift4 f a1 a2 a3 a4) = lift4 f (subst id v a1) (subst id v a2) (subst id v a3) (subst id v a4).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift4':
  forall {A1 A2 A3 A4 B} id v (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4,
          subst id v (fun rho => f (a1 rho) (a2 rho) (a3 rho) (a4 rho)) =
          fun rho => f (subst id v a1 rho) (subst id v a2 rho) (subst id v a3 rho) (subst id v a4 rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift4C:
  forall {A1 A2 A3 A4 B} id (v: environ -> val) (f: A1 -> A2 -> A3 -> A4 -> B)
                  (a1: environ -> A1) (a2: environ -> A2) (a3: environ -> A3) (a4: environ -> A4),
          subst id v (`f a1 a2 a3 a4) = `f (subst id v a1) (subst id v a2) (subst id v a3) (subst id v a4).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift4 (*@subst_lift4'*) @subst_lift4C : subst.


Lemma bool_val_int_eq_e:
  forall i j m, Cop.bool_val (Val.of_bool (Int.eq i j)) type_bool m = Some true -> i=j.
Proof.
 intros.
 revert H; case_eq (Val.of_bool (Int.eq i j)); simpl; intros; inv H0.
 pose proof (Int.eq_spec i j).
 revert H H0; case_eq (Int.eq i j); intros; auto.
 simpl in H0; unfold Vfalse in H0. inv H0. rewrite Int.eq_true in H2. inv H2.
Qed.

Lemma bool_val_notbool_ptr:
    forall v t m,
   match t with Tpointer _ _ => True | _ => False end ->
   (Cop.bool_val (force_val (Cop.sem_notbool v t m)) type_bool m = Some true) = (v = nullval).
Proof.
 intros.
 destruct t; try contradiction. clear H.
 apply prop_ext; split; intros.
 destruct v; simpl in H; try discriminate.
 apply bool_val_int_eq_e in H. subst; auto.
 unfold Cop.sem_notbool, Cop.bool_val in H; simpl in H.
 destruct (Memory.Mem.weak_valid_pointer m b (Int.unsigned i)) eqn:?;
  simpl in H; inv H.
 subst. simpl. unfold Cop.bool_val; simpl. reflexivity.
Qed.

Definition retval : environ -> val := eval_id ret_temp.

Hint Rewrite eval_id_same : norm.
Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : norm.

Lemma simpl_get_result1:
 forall (f: val -> Prop) i, @liftx (Tarrow environ (LiftEnviron Prop)) (@liftx (Tarrow val (LiftEnviron Prop))f retval) (get_result1 i) = `f (eval_id i).
Proof.
intros; extensionality rho.
unfold_lift; unfold retval, get_result1.
f_equal.
Qed.
Hint Rewrite simpl_get_result1: norm.

Lemma retval_get_result1:
   forall i rho, retval (get_result1 i rho) = (eval_id i rho).
Proof. intros. unfold retval, get_result1. simpl.
 normalize.
Qed.
Hint Rewrite retval_get_result1 : norm.

Lemma retval_ext_rval:
  forall ge v, retval (make_ext_rval ge v) = force_val v.
Proof.
 intros. unfold retval, eval_id; simpl. unfold make_ext_rval; simpl.
 destruct v; simpl; auto.
Qed.
Hint Rewrite retval_ext_rval : norm.

Lemma retval_lemma1:
  forall rho v,     retval (env_set rho ret_temp v) = v.
Proof.
 intros. unfold retval.  normalize.
Qed.
Hint Rewrite retval_lemma1 : norm.

Lemma retval_make_args:
  forall v rho, retval (make_args (ret_temp::nil) (v::nil) rho) = v.
Proof. intros.  unfold retval, eval_id; simpl. try rewrite Map.gss. reflexivity.
Qed.
Hint Rewrite retval_make_args: norm2.

Lemma andp_makeargs:
   forall (a b: environ -> mpred) d e,
   `(a && b) (make_args d e) = `a (make_args d e) && `b (make_args d e).
Proof. intros. reflexivity. Qed.
Hint Rewrite andp_makeargs: norm2.

Lemma local_makeargs:
   forall (f: val -> Prop) v,
   `(local (`f retval)) (make_args (cons ret_temp nil) (cons v nil))
    = (local (`f `v)).
Proof. intros. reflexivity. Qed.
Hint Rewrite local_makeargs: norm2.

Lemma simpl_and_get_result1:
  forall (Q R: environ->mpred) i,
    `(Q && R) (get_result1 i) = `Q (get_result1 i) && `R (get_result1 i).
Proof. intros. reflexivity. Qed.
Hint Rewrite simpl_and_get_result1 : norm2.

Lemma liftx_local_retval:
  forall (P: val -> Prop) i,
   `(local (`P retval)) (get_result1 i) = local (`P (eval_id i)).
Proof. intros. reflexivity. Qed.
Hint Rewrite liftx_local_retval : norm2.

Lemma ret_type_initialized:
  forall i Delta, ret_type (initialized i Delta) = ret_type Delta.
Proof.
intros.
unfold ret_type; simpl.
unfold initialized; simpl.
destruct ((temp_types Delta) ! i); try destruct p; reflexivity.
Qed.
Hint Rewrite ret_type_initialized : norm.

Hint Rewrite bool_val_notbool_ptr using apply Coq.Init.Logic.I : norm.

Lemma Vint_inj': forall i j,  (Vint i = Vint j) =  (i=j).
Proof. intros; apply prop_ext; split; intro; congruence. Qed.

Lemma TT_andp_right {A}{NA: NatDed A}:
 forall P Q, TT |-- P -> TT |-- Q -> TT |-- P && Q.
Proof.
  intros. apply andp_right; auto.
Qed.

Lemma TT_prop_right {A}{NA: NatDed A}:
  forall P: Prop , P -> TT |-- prop P.
Proof. intros. apply prop_right. auto.
Qed.

Lemma overridePost_normal_right:
  forall P Q R,
   P |-- Q ->
   P |-- overridePost Q R EK_normal None.
Proof. intros.
  intro rho; unfold overridePost; simpl.
  normalize.
Qed.

Fixpoint fold_right_and P0 (l: list Prop) : Prop :=
 match l with
 | nil => P0
 | b::r => b  /\ fold_right_and P0 r
 end.

Lemma typed_true_isptr:
 forall t, match t with Tpointer _ _ => True | Tarray _ _ _ => True | Tfunction _ _ _ => True | _ => False end ->
          typed_true t = isptr.
Proof.
intros. extensionality x; apply prop_ext.
destruct t; try contradiction; unfold typed_true, strict_bool_val;
destruct x; intuition; try congruence;
destruct (Int.eq i Int.zero); inv H0.
Qed.

Hint Rewrite typed_true_isptr using apply Coq.Init.Logic.I : norm.

Ltac super_unfold_lift_in H :=
   cbv delta [liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry lift lift0
    lift1 lift2 lift3] beta iota in H.

Ltac super_unfold_lift' :=
  cbv delta [liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry lift lift0
    lift1 lift2 lift3] beta iota.

Lemma tc_eval_id_i:
  forall Delta t i rho,
               tc_environ Delta rho ->
              (temp_types Delta)!i = Some (t,true) ->
              tc_val t (eval_id i rho).
Proof.
intros.
unfold tc_environ in H.
destruct rho.
destruct H as [? _].
destruct (H i true t H0) as [v [? ?]].
unfold eval_id. simpl in *. rewrite H1. simpl; auto.
destruct H2. inv H2. auto.
Qed.

Lemma is_int_e:
 forall v i s , is_int i s v -> exists n, v = Vint n /\ is_int i s v.
Proof.
intros.
 destruct i,s,v; try inv H; simpl; eauto.
Qed.

Definition name (id: ident) := True.

Tactic Notation "name" ident(s) constr(id) :=
    assert (s: name id) by apply Coq.Init.Logic.I.

Definition reflect_temps_f (rho: environ) (b: Prop) (i: ident) (t: type*bool) : Prop :=
    match t with
    | (t',true) => tc_val t' (eval_id i rho) /\ b
    |  _  => b
   end.

Definition reflect_temps (Delta: tycontext) (rho: environ) : Prop :=
    PTree.fold (reflect_temps_f rho) (temp_types Delta) True.

Lemma reflect_temps_valid:
  forall Delta rho,
    tc_environ Delta rho -> reflect_temps Delta rho.
Proof.
intros.
unfold reflect_temps.
rewrite PTree.fold_spec.
remember  (PTree.elements (temp_types Delta)) as el.
assert (forall i v, In (i,v) el -> (temp_types Delta) ! i = Some v).
 intros. subst el. apply PTree.elements_complete; auto.
clear Heqel.
assert (forall b: Prop, b -> fold_left
  (fun (a : Prop) (p : positive * (type * bool)) =>
   reflect_temps_f rho a (fst p) (snd p)) el b);
  [ | auto].
revert H0; induction el; simpl; intros; auto.
unfold reflect_temps_f at 2.
destruct a as [i [t [|]]]; simpl; auto.
apply IHel; auto.
split; auto.
eapply tc_eval_id_i.
eassumption.
apply H0; auto.
Qed.

Definition abbreviate {A:Type} (x:A) := x.
Arguments abbreviate [A] [x].

Ltac clear_Delta :=
match goal with
| Delta := @abbreviate tycontext _ |- _ =>
   first [clear Delta | clearbody Delta]
| _ => idtac
end;
match goal with
 |  DS := @abbreviate (PTree.t funspec) _  |- _ =>
   first [clear DS | clearbody DS]
 | |- _ => idtac
 end.

Ltac clear_Delta_specs :=
 lazymatch goal with
 |  DS := @abbreviate (PTree.t funspec) _  |- _ => clearbody DS
 | |- _ => idtac
 end.

Ltac findvars :=
 match goal with DD: tc_environ ?Delta ?rho |- _ =>
  let H := fresh in
    assert (H := reflect_temps_valid _ _ DD);
    try (unfold Delta in H);
   cbv beta iota zeta delta [abbreviate PTree.fold PTree.prev PTree.prev_append PTree.xfold temp_types fst snd
             reflect_temps reflect_temps_f] in H;
   simpl in H;
   repeat match goal with
(*  this clause causes some problems when interacting with make_args'
    | |- context [eval_var ?J ?T rho] =>
           try fold J in H;
                let Name := fresh "_id" in forget (eval_var J T rho) as Name
*)
    | Name: name ?J |- context [eval_id ?J rho] =>
            fold J in H;
            clear Name;
           forget (eval_id J rho) as Name
    | |- context [eval_id ?J rho] =>
           try fold J in H;
           let Name := fresh "_id" in forget (eval_id J rho) as Name
    | Name: name _ |- _ =>
          clear Name
     end;
    repeat match type of H with
                | _ (eval_id _ _) /\ _ =>  destruct H as [_ H]
                | is_int _ _ ?i /\ _ => let TC := fresh "TC" in destruct H as [TC H];
                                let i' := fresh "id" in rename i into i';
                               apply is_int_e in TC; destruct TC as [i [? TC]]; subst i';
                                simpl in TC;
                               match type of TC with True => clear TC | _ => idtac end
                | _ /\ _ => destruct H as [?TC H]
                end;
    clear H
 end.

Lemma sem_cast_id:
  forall Delta rho,
      tc_environ Delta rho ->
  forall t1 t3 id,
  Cop.classify_cast t1 t3 = Cop.cast_case_neutral ->
  match (temp_types Delta)!id with Some (Tpointer _ _, true) => true | _ => false end = true ->
  force_val (sem_cast t1 t3 (eval_id id rho)) = eval_id id rho.
Proof.
intros.
 revert H1; case_eq ((temp_types Delta) ! id); intros; try discriminate.
 destruct p as [t2 ?].
 destruct t2; inv H2.
 destruct b; inv H4.
 pose proof (tc_eval_id_i _ _ _ _ H H1).
 destruct (eval_id id  rho); inv H2.
 destruct t1 as [ | [ | | | ] | [ | ] | [ | ] |  | | | | ];
 destruct t3 as [ | [ | | | ] | [ | ] | [ | ] |  | | | | ]; inv H0; try reflexivity.
 destruct t1 as [ | | | [ | ] |  | | | | ]; destruct t3 as [ | | | [ | ] |  | | | | ]; inv H0;
  try (destruct i0; inv H3); try (destruct i1; inv H2); try reflexivity.
Qed.

Lemma sem_cast_pointer2':
  forall (v : val) (t1 t2: type),
  match t1 with Tpointer _ _ | Tint I32 _ _ => True | _ => False end ->
  match t2 with Tpointer _ _ | Tint I32 _ _ => True | _ => False end ->
  is_pointer_or_null v -> force_val (sem_cast t1 t2 v) = v.
Proof.
intros.
unfold sem_cast, classify_cast.
subst.
destruct t1; try contradiction; try destruct i; try contradiction; simpl; auto;
destruct t2; try contradiction; try destruct i; try contradiction; simpl; auto;
destruct v; inv H1; simpl; auto.
Qed.

Hint Rewrite sem_cast_pointer2' using (try apply Coq.Init.Logic.I; try assumption; reflexivity) : norm.

Lemma sem_cast_pointer2:
  forall v t1 t2 t3 t1' t2',
   t1' = Tpointer t1 noattr ->
   t2' = Tpointer t2 noattr ->
   tc_val (Tpointer t3 noattr) v ->
   force_val (sem_cast t1' t2' v) = v.
Proof.
intros.
subst.
hnf in H1. destruct v; inv H1; reflexivity.
Qed.

Lemma force_eval_var_int_ptr :
forall  {cs: compspecs}  Delta rho i t,
tc_environ Delta rho ->
tc_lvalue Delta (Evar i t) rho |--
        !! (force_val
            match eval_var i t rho with
            | Vint _ => Some (eval_var i t rho)
            | Vptr _ _ => Some (eval_var i t rho)
            | _ => None
            end = eval_var i t rho).
Proof.
intros.
eapply derives_trans.
apply typecheck_lvalue_sound; auto.
simpl; normalize.
 destruct (eval_var i t rho); inv H0; simpl; auto.
Qed.

Lemma is_pointer_or_null_force_int_ptr:
   forall v, is_pointer_or_null v -> (force_val
        match v with
        | Vint _ => Some v
        | Vptr _ _ => Some v
        | _ => None
        end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite is_pointer_or_null_force_int_ptr using assumption : norm1.


Lemma is_pointer_force_int_ptr:
   forall v, isptr v -> (force_val
        match v with
        | Vint _ => Some v
        | Vptr _ _ => Some v
        | _ => None
        end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite is_pointer_force_int_ptr using assumption : norm1.


Lemma is_pointer_or_null_match :
   forall v, is_pointer_or_null v ->
        (match v with
        | Vint _ => Some v
        | Vptr _ _ => Some v
        | _ => None
         end) = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite is_pointer_or_null_match using assumption : norm1.

Lemma is_pointer_force_int_ptr2:
   forall v, isptr v ->
        match v with
        | Vint _ => Some v
        | Vptr _ _ => Some v
        | _ => None
         end = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite is_pointer_force_int_ptr2 using assumption : norm1.

Lemma is_pointer_or_null_force_int_ptr2:
   forall v, is_pointer_or_null (force_val
        match v with
        | Vint _ => Some v
        | Vptr _ _ => Some v
        | _ => None
         end) -> (force_val
        match v with
        | Vint _ => Some v
        | Vptr _ _ => Some v
        | _ => None
         end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.

Hint Rewrite is_pointer_or_null_force_int_ptr2 using assumption : norm1.

Lemma isptr_match : forall w0,
is_pointer_or_null
         match
           match w0 with
           | Vint _ => Some w0
           | Vptr _ _ => Some w0
           | _ => None
           end
         with
         | Some v' => v'
         | None => Vundef
         end
= is_pointer_or_null w0.
intros.
destruct w0; auto.
Qed.

Hint Rewrite isptr_match : norm1.

Lemma eval_cast_neutral_tc_val:
   forall v, (exists t, tc_val t v /\ is_pointer_type t = true) ->
       sem_cast_neutral v = Some v.
Proof.
intros. destruct H as [t [? ?]]; destruct t,v; inv H0; inv H; reflexivity.
Qed.

Hint Rewrite eval_cast_neutral_tc_val using solve [eauto] : norm.

Lemma eval_cast_neutral_is_pointer_or_null:
   forall v, is_pointer_or_null v -> sem_cast_neutral v = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite eval_cast_neutral_is_pointer_or_null using assumption : norm.

Lemma is_pointer_or_null_eval_cast_neutral:
  forall v, is_pointer_or_null (force_val (sem_cast_neutral v)) = is_pointer_or_null v.
Proof. destruct v; reflexivity. Qed.
Hint Rewrite is_pointer_or_null_eval_cast_neutral : norm.


Lemma eval_cast_neutral_isptr:
   forall v, isptr v -> sem_cast_neutral v = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite eval_cast_neutral_isptr using assumption : norm.

Ltac eval_cast_simpl :=
    try (try unfold eval_cast; simpl Cop.classify_cast; cbv iota);
     try match goal with H: tc_environ ?Delta ?rho |- _ =>
       repeat first [
   rewrite eval_cast_neutral_isptr by auto
               | rewrite (sem_cast_id Delta rho H); [ | reflexivity | reflexivity ]
               | erewrite sem_cast_pointer2; [ | | | eassumption ]; [ | reflexivity | reflexivity ]
               ]
     end.

Arguments ret_type !Delta /.

Arguments Datatypes.id {A} x / .

Inductive LLRR : Type :=
  | LLLL : LLRR
  | RRRR : LLRR.

Definition tc_LR_strong {cs: compspecs} Delta e lr :=
  match lr with
  | LLLL => tc_lvalue Delta e
  | RRRR => tc_expr Delta e
  end.

Definition tc_LR {cs: compspecs} Delta e lr :=
  match e with
  | Ederef e0 t =>
     match lr with
     | LLLL => denote_tc_assert
                 (tc_andp
                   (typecheck_expr Delta e0)
                   (tc_bool (is_pointer_type (typeof e0))(op_result_type e)))
     | RRRR => denote_tc_assert
                match access_mode t with
                | By_reference =>
                   (tc_andp
                      (typecheck_expr Delta e0)
                      (tc_bool (is_pointer_type (typeof e0))(op_result_type e)))
                | _ => tc_FF (deref_byvalue t)
                end
    end
  | _ => tc_LR_strong Delta e lr
  end.

Definition eval_LR {cs: compspecs} e lr :=
  match lr with
  | LLLL => eval_lvalue e
  | RRRR => eval_expr e
  end.

Lemma tc_LR_tc_LR_strong: forall {cs: compspecs} Delta e lr rho,
  tc_LR Delta e lr rho && !! isptr (eval_LR e lr rho) |-- tc_LR_strong Delta e lr rho.
Proof.
  intros.
  unfold tc_LR, tc_LR_strong.
  destruct e; try solve [apply andp_left1; auto].
  unfold tc_lvalue, tc_expr.
  destruct lr; simpl.
  + rewrite !denote_tc_assert_andp.
    simpl.
    unfold denote_tc_isptr.
    unfold_lift.
    auto.
  + destruct (access_mode t); try solve [apply andp_left1; auto].
    rewrite !denote_tc_assert_andp.
    simpl.
    unfold denote_tc_isptr.
    unfold_lift.
    auto.
Qed.

Ltac unfold_for_go_lower :=
  cbv delta [PROPx LOCALx SEPx locald_denote
                       eval_exprlist eval_expr eval_lvalue cast_expropt
                       sem_cast eval_binop eval_unop force_val1 force_val2
                      tc_expropt tc_expr tc_exprlist tc_lvalue tc_LR tc_LR_strong
                      typecheck_expr typecheck_exprlist typecheck_lvalue
                      function_body_ret_assert frame_ret_assert
                      make_args' bind_ret get_result1 retval
                       classify_cast
                       (* force_val sem_cast_neutral ... NOT THESE TWO!  *)
                      denote_tc_assert (* tc_andp tc_iszero *)
    liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry
     local lift lift0 lift1 lift2 lift3
   ] beta iota.

Lemma grab_tc_environ:
  forall Delta PQR S rho,
    (tc_environ Delta rho -> PQR rho |-- S) ->
    (local (tc_environ Delta) && PQR) rho |-- S.
Proof.
intros.
unfold PROPx,LOCALx in *; simpl in *.
normalize.
unfold local, lift1. normalize.
Qed.

Ltac go_lower0 :=
intros ?rho;
 try (simple apply grab_tc_environ; intro);
 repeat (progress unfold_for_go_lower; simpl).

Ltac old_go_lower :=
 go_lower0;
 autorewrite with go_lower;
 try findvars;
 simpl;
 autorewrite with go_lower;
 try match goal with H: tc_environ _ ?rho |- _ => clear H rho end.

Hint Rewrite eval_id_same : go_lower.
Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : go_lower.
(*Hint Rewrite Vint_inj' : go_lower.*)

(*** New go_lower stuff ****)


Lemma lower_one_temp:
 forall t rho Delta P i v Q R S,
  (temp_types Delta) ! i = Some (t,true) ->
  (tc_val t v -> eval_id i rho = v ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (temp i v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *. unfold_lift.
normalize.
rewrite prop_true_andp in H0 by auto.
apply H0; auto.
apply tc_eval_id_i with Delta; auto.
Qed.

Lemma lower_one_temp_Vint:
 forall t rho Delta P i v Q R S,
  (temp_types Delta) ! i = Some (t,true) ->
  (tc_val t (Vint v) -> eval_id i rho = Vint v ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (temp i (Vint v) :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
eapply lower_one_temp; eauto.
Qed.

Lemma lower_one_lvar:
 forall t rho Delta P i v Q R S,
  (isptr v -> lvar_denote i t v rho ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (lvar i t v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *. unfold_lift.
normalize.
rewrite prop_true_andp in H by auto.
apply H; auto.
hnf in H1.
destruct (Map.get (ve_of rho) i); try contradiction.
destruct p. destruct H1; subst. apply I.
Qed.

Lemma gvar_size_compatible:
  forall {cs: compspecs} i s rho t,
    gvar_denote i s rho ->
    sizeof t <= Int.modulus ->
    size_compatible t s.
Proof.
intros.
hnf in H. destruct (Map.get (ve_of rho) i) as [[? ? ] | ]; try contradiction.
destruct (ge_of rho i); try contradiction.
subst s.
simpl; auto.
Qed.

Lemma gvar_align_compatible:
  forall  {cs: compspecs} i s rho t,
    gvar_denote i s rho ->
    align_compatible t s.
Proof.
intros.
hnf in H. destruct (Map.get (ve_of rho) i) as [[? ? ] | ]; try contradiction.
destruct (ge_of rho i); try contradiction.
subst s.
simpl; auto.
exists 0. reflexivity.
Qed.

Lemma sgvar_size_compatible:
  forall {cs: compspecs} i s rho t,
    sgvar_denote i s rho ->
    sizeof t <= Int.modulus ->
    size_compatible t s.
Proof.
intros.
hnf in H.
destruct (ge_of rho i); try contradiction.
subst s.
simpl; auto.
Qed.

Lemma sgvar_align_compatible:
  forall  {cs: compspecs} i s rho t,
    sgvar_denote i s rho ->
    align_compatible t s.
Proof.
intros.
hnf in H.
destruct (ge_of rho i); try contradiction.
subst s.
simpl; auto.
exists 0. reflexivity.
Qed.

Lemma finish_compute_le:  Lt = Gt -> False.
Proof. congruence. Qed.

Lemma lower_one_gvar:
 forall t {cs: compspecs} rho Delta P i v Q R S,
  (glob_types Delta) ! i = Some t ->
  sizeof t <= Int.modulus  ->
  (isptr v -> gvar_denote i v rho ->
     size_compatible t v -> align_compatible t v ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (gvar i v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *. unfold_lift.
normalize.
rewrite prop_true_andp in H1 by auto.
apply H1; auto.
hnf in H3; destruct (Map.get (ve_of rho) i) as [[? ?] |  ]; try contradiction.
destruct (ge_of rho i); try contradiction.
subst. apply I.
eapply gvar_size_compatible; eauto.
eapply gvar_align_compatible; eauto.
Qed.

Lemma lower_one_sgvar:
 forall t {cs: compspecs}  rho Delta P i v Q R S,
  (glob_types Delta) ! i = Some t ->
  sizeof t <= Int.modulus  ->
  (isptr v -> sgvar_denote i v rho ->
     size_compatible t v -> align_compatible t v ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (sgvar i v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *. unfold_lift.
normalize.
rewrite prop_true_andp in H1 by auto.
apply H1; auto.
hnf in H3.
destruct (ge_of rho i); try contradiction.
subst. apply I.
eapply sgvar_size_compatible; eauto.
eapply sgvar_align_compatible; eauto.
Qed.

Lemma lower_one_prop:
 forall  rho Delta P (P1: Prop) Q R S,
  (P1 ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (localprop P1 :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *.
normalize.
rewrite prop_true_andp in H by auto.
hnf in H1.
apply H; auto.
Qed.

Lemma finish_lower:
  forall rho D R S,
  fold_right_sepcon R |-- S ->
  (local D && PROP() LOCAL() (SEPx R)) rho |-- S.
Proof.
intros.
simpl.
apply andp_left2.
unfold_for_go_lower; simpl. normalize.
Qed.

Lemma lower_one_temp_Vint':
 forall sz sg rho Delta P i v Q R S,
  (temp_types Delta) ! i = Some (Tint sz sg noattr, true) ->
  ((exists j, v = Vint j /\ tc_val (Tint sz sg noattr) (Vint j) /\ eval_id i rho = (Vint j)) ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (temp i v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
eapply lower_one_temp; eauto.
intros.
apply H0; auto.
generalize H1; intro.
hnf in H3. destruct v; try contradiction.
exists i0. split3; auto.
Qed.

Ltac lower_one_temp_Vint' :=
 match goal with
 | a : name ?i |- (local _ && PROPx _ (LOCALx (temp ?i ?v :: _) _)) _ |-- _ =>
     simple eapply lower_one_temp_Vint';
     [ reflexivity | ];
     let tc := fresh "TC" in
     clear a; intros [a [? [tc ?EVAL]]]; unfold tc_val in tc; try subst v;
     revert tc; fancy_intro true
 | |- (local _ && PROPx _ (LOCALx (temp _ ?v :: _) _)) _ |-- _ =>
    is_var v;
     simple eapply lower_one_temp_Vint';
     [ reflexivity | ];
    let v' := fresh "v" in rename v into v';
     let tc := fresh "TC" in
     intros [v [? [tc ?EVAL]]]; unfold tc_val in tc; subst v';
     revert tc; fancy_intro true
 end.

Lemma eq_True:
   forall (A: Prop), A -> (A=True).
Proof.
intros.
apply prop_ext; intuition.
Qed.

Ltac fold_types :=
 fold noattr tuint tint tschar tuchar;
 repeat match goal with
 | |- context [Tpointer ?t noattr] =>
      change (Tpointer t noattr) with (tptr t)
 | |- context [Tarray ?t ?n noattr] =>
      change (Tarray t n noattr) with (tarray t n)
 end.

Ltac fold_types1 :=
  match goal with |- _ -> ?A =>
  let a := fresh "H" in set (a:=A); fold_types; subst a
  end.

Ltac fold_types4 :=
  match goal with |- _ -> _ -> _ -> _ -> ?A =>
  let a := fresh "H" in set (a:=A); fold_types; subst a
  end.

Lemma derives_extract_PROP :
  forall (P1: Prop) A P QR S,
     (P1 -> A && PROPx P QR |-- S) ->
     A && PROPx (P1::P) QR |-- S.
Proof.
unfold PROPx in *.
intros.
rewrite fold_right_cons.
normalize.
eapply derives_trans; [ | apply H; auto].
normalize.
Qed.

Lemma ENTAIL_normal_ret_assert:
  forall Delta P Q ek vl,
 (ek = EK_normal -> vl = None -> ENTAIL Delta, P |-- Q) ->
 ENTAIL Delta, normal_ret_assert P ek vl |-- normal_ret_assert Q ek vl.
Proof.
intros.
unfold normal_ret_assert. normalize.
Qed.

(*
Lemma toss_rho: forall rho Delta Q R S,
 fold_right_sepcon R |-- S rho ->
 (local (tc_environ Delta) && PROPx nil (LOCALx Q (SEPx R))) rho |-- S rho.
Proof.
intros.
simpl.
apply andp_left2.
unfold PROPx, LOCALx, SEPx.
simpl.
apply andp_left2.
apply andp_left2.
auto.
Qed.
*)

Lemma lower_one_temp_trivial:
 forall t rho Delta P i v Q R S,
  (temp_types Delta) ! i = Some (t,true) ->
  (tc_val t v ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (temp i v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *. unfold_lift.
normalize.
rewrite prop_true_andp in H0 by auto.
apply H0; auto.
apply tc_eval_id_i with Delta; auto.
Qed.

Lemma quick_finish_lower:
  forall LHS,
  emp |-- !! True ->
  LHS |-- !! True.
Proof.
intros.
apply prop_right; auto.
Qed.

Definition rho_marker := tt.

Ltac go_lower :=
clear_Delta_specs;
intros;
match goal with
 | |- ENTAIL ?D, normal_ret_assert _ _ _ |-- _ =>
       apply ENTAIL_normal_ret_assert; fancy_intros true
 | |- local _ && _ |-- _ => idtac
 | |- ENTAIL _, _ |-- _ => idtac
 | _ => fail 10 "go_lower requires a proof goal in the form of (ENTAIL _ , _ |-- _)"
end;
repeat (simple apply derives_extract_PROP; fancy_intro true);
let rho := fresh "rho" in
intro rho;
try match goal with
| |- ?LHS |--  ?S rho =>
       unify (S rho) (S any_environ);
       let u := fresh "u" in pose (u := rho_marker);
   let x := fresh "x" in set (x:=LHS);
   unfold_for_go_lower; simpl; subst x;
   rewrite ?(prop_true_andp True) by auto
end;
first [simple apply quick_finish_lower
| repeat first
 [ match goal with u:=rho_marker |- _ => idtac end;
   simple eapply lower_one_temp_trivial;
     [reflexivity | unfold tc_val at 1; fancy_intro true ]
 | simple eapply lower_one_temp_Vint;
     [try reflexivity; eauto | unfold tc_val at 1; fancy_intro true; intros ?EVAL ]
 | lower_one_temp_Vint'
 | simple eapply lower_one_temp;
     [try reflexivity; eauto | unfold tc_val at 1; fancy_intro true; intros ?EVAL]
 | simple apply lower_one_lvar;
     fold_types1; fancy_intro true; intros ?LV
 | simple eapply lower_one_gvar;
     [try reflexivity; eauto  | compute; apply finish_compute_le
     | fold_types4; fancy_intro true; intros ?GV ?SC ?AC]
 | simple eapply lower_one_sgvar;
     [try reflexivity; eauto  | compute; apply finish_compute_le
     | fold_types4; fancy_intro true; intros ?GV ?SC ?AC]
 ];
 (simple apply finish_lower ||
 match goal with
 | |- (_ && PROPx nil _) _ |-- _ => fail 1 "LOCAL part of precondition is not a concrete list (or maybe Delta is not concrete)"
 | |- _ => fail 1 "PROP part of precondition is not a concrete list"
 end);
unfold_for_go_lower;
simpl; rewrite ?sepcon_emp;
repeat match goal with
| H: eval_id ?i rho = ?v |- _ =>
 first [rewrite ?H in *; clear H; match goal with
               | H:context[eval_id i rho]|-_ => fail 2
               | |- _ => idtac
               end
        |  let x := fresh "x" in
             set (x := eval_id i rho) in *; clearbody x; subst x
        ]
end;
repeat match goal with
 | H: lvar_denote ?i ?t ?v rho |- context [lvar_denote ?i ?t' ?v' rho] =>
     rewrite (eq_True (lvar_denote i t' v' rho) H)
 | H: gvar_denote ?i ?v rho |- context [gvar_denote ?i ?v' rho] =>
     rewrite (eq_True (gvar_denote i v' rho) H)
 | H: sgvar_denote ?i ?v rho |- context [sgvar_denote ?i ?v' rho] =>
     rewrite (eq_True (sgvar_denote i v' rho) H)
end
];
try match goal with u := rho_marker |- _ => clear u end;
clear_Delta;
try clear dependent rho.

Lemma raise_sepcon:
 forall A B : environ -> mpred ,
    (fun rho: environ => A rho * B rho) = (A * B).
Proof. reflexivity. Qed.
Hint Rewrite raise_sepcon : norm1.


Lemma lift1_lift1_retval {A}: forall i (P: val -> A),
lift1 (lift1 P retval) (get_result1 i) = lift1 P (eval_id i).
Proof. intros.  extensionality rho.
  unfold lift1.  f_equal; normalize.
Qed.

Lemma lift_lift_retval:
  forall (i: ident) P,
   @liftx (Tarrow environ (LiftEnviron mpred))
     (@liftx (Tarrow val (LiftEnviron mpred)) P retval) (get_result1 i) = `P (eval_id i).
Proof.
 reflexivity.
Qed.
Hint Rewrite lift_lift_retval: norm2.


Lemma lift_lift_x:  (* generalizes lift_lift_val *)
  forall t t' P (v: t),
  (@liftx (Tarrow t (LiftEnviron t')) P (@liftx (LiftEnviron t) v)) =
  (@liftx (LiftEnviron t') (P v)).
Proof. reflexivity. Qed.
Hint Rewrite lift_lift_x : norm2.

Lemma lift0_exp {A}{NA: NatDed A}:
  forall (B: Type) (f: B -> A), lift0 (exp f) = EX x:B, lift0 (f x).
Proof. intros; extensionality rho; unfold lift0. simpl.
f_equal; extensionality b; auto.
Qed.

Lemma lift0C_exp {A}{NA: NatDed A}:
  forall (B: Type) (f: B -> A), `(exp f) = EX x:B, `(f x).
Proof.
intros. unfold_lift. simpl. extensionality rho. f_equal; extensionality x; auto.
Qed.
Hint Rewrite @lift0_exp : norm2.
Hint Rewrite @lift0C_exp : norm2.

Lemma lift0_andp {A}{NA: NatDed A}:
 forall P Q,
   lift0 (@andp A NA P Q) = andp (lift0 P) (lift0 Q).
Proof.
intros. extensionality rho. reflexivity.
Qed.

Lemma lift0C_andp {A}{NA: NatDed A}:
 forall P Q: A,
  `(@andp A NA P Q) =
  andp (`P) (`Q).
Proof.
intros. extensionality rho. reflexivity.
Qed.

Lemma lift0_prop {A}{NA: NatDed A}:
 forall P, lift0 (!! P) = !!P.
Proof. intros. extensionality rho; reflexivity. Qed.

Lemma lift0C_prop {A}{NA: NatDed A}:
 forall P, @liftx (LiftEnviron A) (@prop A NA P) =
                  @prop (environ -> A) _ P.
Proof. reflexivity. Qed.

Lemma lift0_sepcon {A}{NA: NatDed A}{SA: SepLog A}:
 forall P Q,
  lift0 (@sepcon A NA SA P Q) = sepcon (lift0 P) (lift0 Q).
Proof.
intros. extensionality rho. reflexivity.
Qed.

Lemma lift0C_sepcon {A}{NA: NatDed A}{SA: SepLog A}:
 forall P Q N2 S2,
  (@liftx (LiftEnviron A) (@sepcon A N2 S2 P Q)) =
  (@sepcon (environ->A) _ _
     (@liftx (LiftEnviron A) P)
     (@liftx (LiftEnviron A) Q)).
Proof. reflexivity. Qed.

Lemma lift0_later {A}{NA: NatDed A}{IA: Indir A}:
  forall P:A,
   lift0 (@later A NA IA P) = later  (lift0 P).
Proof. intros. reflexivity. Qed.

Lemma lift0C_later {A}{NA: NatDed A}{IA: Indir A}:
  forall P:A,
   `(@later A NA IA P) = @later (environ->A) _ _ (`P).
Proof. intros. reflexivity. Qed.

Hint Rewrite (@lift0C_sepcon mpred _ _) : norm.
Hint Rewrite (@lift0C_andp mpred _) : norm.
Hint Rewrite (@lift0C_exp mpred _) : norm.
Hint Rewrite (@lift0C_later mpred _ _) : norm.
Hint Rewrite (@lift0C_prop mpred _) : norm.

Hint Rewrite
    @lift1_lift1_retval
    @lift0_exp
    @lift0_sepcon
    @lift0_prop
    @lift0_later
    : norm2.

Lemma fst_unfold: forall {A B} (x: A) (y: B), fst (x,y) = x.
Proof. reflexivity. Qed.
Lemma snd_unfold: forall {A B} (x: A) (y: B), snd (x,y) = y.
Proof. reflexivity. Qed.
Hint Rewrite @fst_unfold @snd_unfold : norm.

Lemma local_andp_prop:  forall P Q, local P && prop Q = prop Q && local P.
Proof. intros. apply andp_comm. Qed.
Lemma local_andp_prop1: forall P Q R, local P && (prop Q && R) = prop Q && (local P && R).
Proof. intros. rewrite andp_comm. rewrite andp_assoc. f_equal. apply andp_comm. Qed.
Hint Rewrite local_andp_prop local_andp_prop1 : norm2.

Lemma local_sepcon_assoc1:
   forall P Q R, (local P && Q) * R = local P && (Q * R).
Proof.
intros.
extensionality rho; unfold local, lift1; simpl.
apply pred_ext; normalize.
Qed.
Lemma local_sepcon_assoc2:
   forall P Q R, R * (local P && Q) = local P && (R * Q).
Proof.
intros.
extensionality rho; unfold local, lift1; simpl.
apply pred_ext; normalize.
Qed.
Hint Rewrite local_sepcon_assoc1 local_sepcon_assoc2 : norm2.

Definition do_canon (x y : environ->mpred) := (sepcon x y).

Ltac strip1_later P :=
 match P with
 | do_canon ?L ?R => let L' := strip1_later L in let R' := strip1_later R in constr:(do_canon L' R')
 | PROPx ?P ?QR => let QR' := strip1_later QR in constr:(PROPx P QR')
 | LOCALx ?Q ?R => let R' := strip1_later R in constr:(LOCALx Q R')
 | SEPx ?R => let R' := strip1_later R in constr:(SEPx R')
 | ?L::?R => let L' := strip1_later L in let R' := strip1_later R in constr:(L'::R')
 | nil => constr:(nil)
 | ?L && ?R => let L' := strip1_later L in let R' := strip1_later R in constr:(L' && R')
 | ?L * ?R => let L' := strip1_later L in let R' := strip1_later R in constr:(L'*R')
 | |> ?L => constr:(L)
 | ?L => constr:(L)
end.

Lemma andp_later_derives {A} {NA: NatDed A}{IA: Indir A}:
  forall P Q P' Q': A, P |-- |> P' -> Q |-- |> Q' -> P && Q |-- |> (P' && Q').
Proof.
intros. rewrite later_andp. apply andp_derives; auto. Qed.

Lemma sepcon_later_derives {A} {NA: NatDed A}{SL: SepLog A}{IA: Indir A}{SI: SepIndir A}:
  forall P Q P' Q': A, P |-- |> P' -> Q |-- |> Q' -> P * Q |-- |> (P' * Q').
Proof.
intros. rewrite later_sepcon. apply sepcon_derives; auto. Qed.

Hint Resolve @andp_later_derives @sepcon_later_derives @sepcon_derives
              @andp_derives @imp_derives @now_later @derives_refl: derives.

Notation "'DECLARE' x s" := (x: ident, s: funspec)
   (at level 160, x at level 0, s at level 150, only parsing).

Notation " a 'OF' ta " := (a%type,ta%type) (at level 100, only parsing): formals.
Delimit Scope formals with formals.

Definition NDsemax_external {Hspec: OracleKind} (ids: list ident) (ef: external_function)
  (A: Type) (P Q: A -> environ -> mpred): Prop :=
  @semax_external Hspec ids ef (rmaps.ConstType A) (fun _ => P) (fun _ => Q).

Notation "'WITH' x : tx 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default tx (fun x => P%assert) (fun x => Q%assert))
            (at level 200, x at level 0, P at level 100, Q at level 100).

Notation "'WITH' x : tx 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default tx (fun x => P%assert) (fun x => Q%assert))
            (at level 200, x at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2)
           (fun x => match x with (x1,x2) => P%assert end)
           (fun x => match x with (x1,x2) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2)
           (fun x => match x with (x1,x2) => P%assert end)
           (fun x => match x with (x1,x2) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3)
           (fun x => match x with (x1,x2,x3) => P%assert end)
           (fun x => match x with (x1,x2,x3) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3)
           (fun x => match x with (x1,x2,x3) => P%assert end)
           (fun x => match x with (x1,x2,x3) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100).


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4)
           (fun x => match x with (x1,x2,x3,x4) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4)
           (fun x => match x with (x1,x2,x3,x4) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5)
           (fun x => match x with (x1,x2,x3,x4,x5) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5)
           (fun x => match x with (x1,x2,x3,x4,x5) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100).

Lemma exp_derives {A}{NA: NatDed A}{B}:
   forall F G: B -> A, (forall x, F x |-- G x) -> exp F |-- exp G.
Proof.
intros.
apply exp_left; intro x. apply exp_right with x; auto.
Qed.

Lemma prop_true_andp1 {A}{NA: NatDed A} :
  forall (P1 P2: Prop) Q ,
    P1 -> (!! (P1 /\ P2) && Q = !!P2 && Q).
Proof.
intros. f_equal; auto.  f_equal.  apply prop_ext; intuition.
Qed.
Hint Rewrite prop_true_andp1 using solve [auto 3 with typeclass_instances]: norm1.
Hint Rewrite prop_true_andp1 using assumption : norm.

Lemma and_assoc': forall A B C: Prop,
  ((A /\ B) /\ C) = (A /\ (B /\ C)).
Proof.
intros. apply prop_ext; apply and_assoc.
Qed.

Lemma and_assoc'' {T}{NT: NatDed T}: forall A B C: Prop,
  !! ((A /\ B) /\ C) = !! (A /\ (B /\ C)).
Proof.
intros. rewrite and_assoc'; auto.
Qed.

Hint Rewrite @and_assoc'' using solve [auto with typeclass_instances] : norm1.
Hint Rewrite @and_assoc'' using solve [auto with typeclass_instances] : gather_prop.

Ltac hoist_later_left :=
   match goal with
  | |- (?P |-- _) =>
        let P' := strip1_later P in
        apply derives_trans with (|>P');
         [ solve [ auto 50 with derives ] | ]
  end.

Lemma semax_later_trivial: forall Espec  {cs: compspecs} Delta P c Q,
  @semax cs Espec Delta (|> P) c Q ->
  @semax cs Espec Delta P c Q.
Proof.
 intros until Q.
 apply semax_pre0.
  apply now_later.
Qed.

Ltac hoist_later_in_pre :=
     match goal with |- semax _ ?P _ _ =>
       match P with
       | context[@later] =>
            let P' := strip1_later P in apply semax_pre0 with (|> P'); [solve [auto 50 with derives] | ]
       | _ => apply semax_later_trivial
       end
     end.

Ltac type_of_field_tac :=
 simpl;
  repeat first [rewrite if_true by auto
                    | rewrite if_false by (let H:=fresh in intro H; inversion H)
                    | simpl; reflexivity].


Ltac simpl_tc_expr :=
    match goal with |- context [tc_expr ?A ?B] =>
        change (tc_expr A B) with (denote_tc_assert (typecheck_expr A B));
        simpl typecheck_expr; simpl denote_tc_assert
    end.


Lemma prop_and1 {A}{NA: NatDed A}:
  forall P Q : Prop, P -> !!(P /\ Q) = !!Q.
Proof. intros. f_equal; apply prop_ext; intuition.
Qed.
Hint Rewrite prop_and1 using solve [auto 3 with typeclass_instances] : norm2.


Lemma subst_make_args':
  forall  {cs: compspecs}  id v (P: environ->mpred) fsig tl el,
  length tl = length el ->
  length (fst fsig) = length el ->
  subst id v (`P (make_args' fsig (eval_exprlist tl el))) =
           (`P (make_args' fsig (subst id v (eval_exprlist tl el)))).
Proof.
intros. unfold_lift. extensionality rho; unfold subst.
f_equal. unfold make_args'.
revert tl el H H0; induction (fst fsig); destruct tl,el; simpl; intros; inv H; inv H0.
reflexivity.
specialize (IHl _ _ H2 H1).
unfold_lift; rewrite IHl. auto.
Qed.
Hint Rewrite @subst_make_args' using (solve[reflexivity]) : subst.

Lemma subst_andp {A}{NA: NatDed A}:
  forall id v (P Q: environ-> A), subst id v (P && Q) = subst id v P && subst id v Q.
Proof.
intros.
extensionality rho; unfold subst; simpl.
auto.
Qed.

Lemma subst_prop {A}{NA: NatDed A}: forall i v P,
    subst i v (prop P) = prop P.
Proof.
intros; reflexivity.
Qed.
Hint Rewrite @subst_andp subst_prop : subst.

Lemma map_cons: forall {A B} (f: A -> B) x y,
   map f (x::y) = f x :: map f y.
Proof. reflexivity. Qed.

Hint Rewrite @map_cons : norm.
Hint Rewrite @map_cons : subst.

Lemma map_nil: forall {A B} (f: A -> B), map f nil = nil.
Proof. reflexivity. Qed.

Hint Rewrite @map_nil : norm.
Hint Rewrite @map_nil : subst.

Lemma subst_sepcon: forall i v (P Q: environ->mpred),
  subst i v (P * Q) = (subst i v P * subst i v Q).
Proof. reflexivity. Qed.
Hint Rewrite subst_sepcon : subst.

Fixpoint remove_localdef (i: ident) (l: list localdef) : list localdef :=
  match l with
  | nil => nil
  | d :: l0 =>
     match d with
     | temp j v =>
       if ident_eq i j
       then remove_localdef i l0
       else d :: remove_localdef i l0
     | _ => d :: remove_localdef i l0
     end
  end.

Lemma subst_stackframe_of:
  forall {cs: compspecs} i v f, subst i v (stackframe_of f) = stackframe_of f.
Proof.
unfold stackframe_of; simpl; intros.
unfold subst.
extensionality rho.
induction (fn_vars f). reflexivity.
simpl map. repeat rewrite fold_right_cons.
f_equal.
apply IHl.
Qed.
Hint Rewrite @subst_stackframe_of : subst.

Lemma remove_localdef_PROP: forall (i: ident) P Q R,
  EX old: val, subst i `old (PROPx P (LOCALx Q (SEPx R))) |--
  PROPx P (LOCALx (remove_localdef i Q) (SEPx R)).
Proof.
  intros.
  apply exp_left; intro old.
  unfold PROPx.
  autorewrite with subst norm.
  apply andp_derives; auto.
  unfold LOCALx.
  autorewrite with subst norm.
  apply andp_derives; auto.
  induction Q; simpl fold_right.
  + autorewrite with subst norm; auto.
  + destruct a; [if_tac | ..];
    autorewrite with subst norm.
    - eapply derives_trans; [| exact IHQ].
      rewrite local_lift2_and.
      apply andp_left2; auto.
    - rewrite !local_lift2_and.
      apply andp_derives; [| exact IHQ].
      unfold locald_denote.
      autorewrite with subst norm.
      unfold local, lift1; unfold_lift; intros ?.
      apply prop_derives; simpl.
      unfold subst; simpl; intros.
      rewrite eval_id_other in H0 by auto; auto.
    - rewrite !local_lift2_and.
      apply andp_derives; [| exact IHQ].
      unfold local, lift1; unfold_lift; intros rho.
      unfold subst; simpl.
      auto.
    - rewrite !local_lift2_and.
      apply andp_derives; [| exact IHQ].
      unfold local, lift1; unfold_lift; intros rho.
      unfold subst; simpl.
      auto.
    - rewrite !local_lift2_and.
      apply andp_derives; [| exact IHQ].
      unfold local, lift1; unfold_lift; intros rho.
      unfold subst; simpl.
      auto.
    - rewrite !local_lift2_and.
      apply andp_derives; [| exact IHQ].
      unfold local, lift1; unfold_lift; intros rho.
      unfold subst; simpl.
      auto.
Qed.

Fixpoint iota_formals (i: ident) (tl: typelist) :=
 match tl with
 | Tcons t tl' => (i,t) :: iota_formals (i+1)%positive tl'
 | Tnil => nil
 end.

Ltac make_sequential :=
  match goal with
  | |- @semax _ _ _ _ _ (normal_ret_assert _) => idtac
  | |- _ => apply sequential
  end.

Lemma isptr_force_ptr'' : forall p Q,
    (isptr p -> Q) ->
    (isptr (force_ptr p) -> Q).
Proof.
intros.
apply X.
destruct p; inv H; apply Coq.Init.Logic.I.
Qed.

Lemma isptr_offset_val'': forall i p Q,
    (isptr p -> Q) ->
    (isptr (offset_val i p) -> Q).
Proof.
intros.
apply X.
destruct p; inv H; apply Coq.Init.Logic.I.
Qed.

Lemma ptr_eq_e': forall v1 v2 B,
   (v1=v2 -> B) ->
   (ptr_eq v1 v2 -> B).
Proof.
intuition. apply X. apply ptr_eq_e; auto.
Qed.

Lemma typed_false_of_bool':
 forall x (P: Prop),
    ((x=false) -> P) ->
    (typed_false tint (Val.of_bool x) -> P).
Proof.
intuition.
apply H, typed_false_of_bool; auto.
Qed.

Lemma typed_true_of_bool':
 forall x (P: Prop),
    ((x=true) -> P) ->
    (typed_true tint (Val.of_bool x) -> P).
Proof.
intuition.
apply H, typed_true_of_bool; auto.
Qed.

Ltac intro_if_new :=
 repeat match goal with
  | |- ?A -> _ => ((assert A by auto; fail 1) || fail 1) || intros _
  | |- (_ <-> _) -> _ =>
         intro
  | |- (?A /\ ?B) -> ?C =>
         apply (@and_ind A B C)
  | |- isptr (force_ptr ?P) -> ?Q =>
         apply (isptr_force_ptr'' P Q)
  | |- isptr (offset_val ?i ?P) -> ?Q =>
         apply (isptr_offset_val'' i P Q)
  | H: is_pointer_or_null ?P |- isptr ?P -> _ =>
         clear H
  | |- ?x = ?y -> _ =>
          let H := fresh in intro H;
                     first [subst x | subst y
                             | is_var x; rewrite H
                             | is_var y; rewrite <- H
                             | solve [discriminate H]
                             | idtac]
  | |- isptr ?x -> _ =>
          let H := fresh "P" x in intro H
  | |- is_pointer_or_null ?x =>
          let H := fresh "PN" x in intro H
  | |- typed_false _ (Val.of_bool _) -> _ =>
          simple apply typed_false_of_bool'
  | |- typed_true _ (Val.of_bool _) -> _ =>
          simple apply typed_true_of_bool'
  | |- ptr_eq _ _ -> _ =>
          apply ptr_eq_e'
  | |- _ -> _ =>
          intro
  end.

Lemma saturate_aux20:
 forall (P Q: mpred) P' Q' ,
    P |-- !! P' ->
    Q |-- !! Q' ->
    P * Q |-- !! (P' /\ Q').
Proof.
intros.
eapply derives_trans; [apply sepcon_derives; eassumption | ].
rewrite sepcon_prop_prop.
auto.
Qed.

Lemma saturate_aux21:  (* obsolete? *)
  forall (P Q: mpred) S (S': Prop),
   P |-- S ->
   S = !!S' ->
   !! S' && P |-- Q -> P |-- Q.
Proof.
intros. subst.
eapply derives_trans; [ | eassumption].
apply andp_right; auto.
Qed.

Lemma saturate_aux21x:
  forall (P Q S: mpred),
   P |-- S ->
   S && P |-- Q -> P |-- Q.
Proof.
intros. subst.
eapply derives_trans; [ | eassumption].
apply andp_right; auto.
Qed.


Lemma prop_True_right {A}{NA: NatDed A}: forall P:A, P |-- !! True.
Proof. intros; apply prop_right; auto.
Qed.

Ltac already_saturated :=
(match goal with |- ?P |-- ?Q =>
    let H := fresh in
     assert (H: P |-- Q) by auto with nocore saturate_local;
     cbv beta in H;
     match type of H with _ |-- !! ?Q' =>
     assert (Q') by (repeat simple apply conj; auto);
     fail 3
     end
end || auto with nocore saturate_local)
 || simple apply prop_True_right.


Ltac saturate_local :=
simple eapply saturate_aux21x;
 [repeat simple apply saturate_aux20;
   (* use already_saturated if want to be fancy,
         otherwise the next lines *)
    auto with nocore saturate_local;
    simple apply prop_True_right
(* | cbv beta; reflexivity    this line only for use with saturate_aux21 *)
 | simple apply derives_extract_prop;
   match goal with |- _ -> ?A =>
       let P := fresh "P" in set (P := A);
       fancy_intros true;
       subst P
      end
 ].

(* old version:
Ltac saturate_local :=
simple eapply saturate_aux21x;
 [repeat simple apply saturate_aux20;
   (* use already_saturated if want to be fancy,
         otherwise the next lines *)
    auto with nocore saturate_local;
    simple apply prop_True_right
(* | cbv beta; reflexivity    this line only for use with saturate_aux21 *)
 | simple apply derives_extract_prop;
   match goal with |- _ -> ?A =>
       let P := fresh "P" in set (P := A); autorewrite with norm;
              rewrite -> ?and_assoc; fancy_intros true;  subst P
      end
 ].
*)

(*********************************************************)

Lemma prop_right_emp {A} {NA: NatDed A}:
 forall P: Prop, P -> emp |-- !! P.
Proof. intros. normalize.
Qed.

Ltac prop_right_cautious :=
 try solve [simple apply prop_right; auto].

(**********************************************************)
(* testing
Parameter f: nat -> Prop.
Parameter g h : mpred.

Goal ( !! f 1 && ((h && !! f 2) && h ) && (!! f 3 && (g && (!!f 4 && !! f 5) && !! f 6)) |-- FF).

*)

(*****************************************************************)

Ltac subst_any :=
 repeat match goal with
  | H: ?x = ?y |- _ => first [ subst x | subst y ]
 end.

Lemma prop_and_right {A}{NA: NatDed A}:
 forall (U: A) (X Y: Prop),
    X ->
    U |-- !! Y ->
    U |-- !! (X /\ Y).
Proof. intros. apply derives_trans with (!!Y); auto.
apply prop_derives; auto.
Qed.

Lemma subst_ewand: forall i v (P Q: environ->mpred),
  subst i v (ewand P Q) = ewand (subst i v P) (subst i v Q).
Proof. reflexivity. Qed.
Hint Rewrite subst_ewand : subst.

Lemma fold_right_sepcon_subst:
 forall i e R, fold_right sepcon emp (map (subst i e) R) = subst i e (fold_right sepcon emp R).
Proof.
 intros. induction R; auto.
 autorewrite with subst. f_equal; auto.
Qed.

Lemma resubst: forall {A} i (v: val) (e: environ -> A), subst i (`v) (subst i `v e) = subst i `v e.
Proof.
 intros. extensionality rho. unfold subst.
 f_equal.
 unfold env_set.
 f_equal.
 apply Map.ext. intro j.
 destruct (eq_dec i j). subst. repeat rewrite Map.gss. f_equal.
 simpl.
 repeat rewrite Map.gso by auto. auto.
Qed.

Hint Rewrite @resubst : subst.

Lemma unsigned_eq_eq: forall i j, Int.unsigned i = Int.unsigned j -> i = j.
Proof.
  intros.
  rewrite <- (Int.repr_unsigned i), <- (Int.repr_unsigned j).
  rewrite H.
  reflexivity.
Qed.

Ltac solve_mod_eq :=
  unfold Int.add, Int.mul;
  repeat rewrite Int.unsigned_repr_eq;
  repeat
  (repeat rewrite Zmod_mod;
  repeat rewrite Zmult_mod_idemp_l;
  repeat rewrite Zmult_mod_idemp_r;
  repeat rewrite Zplus_mod_idemp_l;
  repeat rewrite Zplus_mod_idemp_r).


Lemma prop_false_andp {A}{NA :NatDed A}:
 forall P Q, ~P -> !! P && Q = FF.
Proof.
intros.
apply pred_ext; normalize.
Qed.

Lemma orp_FF {A}{NA: NatDed A}:
 forall Q, Q || FF = Q.
Proof.
intros. apply pred_ext. apply orp_left; normalize. apply orp_right1; auto.
Qed.

Lemma FF_orp {A}{NA: NatDed A}:
 forall Q, FF || Q = Q.
Proof.
intros. apply pred_ext. apply orp_left; normalize. apply orp_right2; auto.
Qed.

Lemma wand_join {A}{NA: NatDed A}{SA: SepLog A}:
  forall x1 x2 y1 y2: A,
    (x1 -* y1) * (x2 -* y2) |-- ((x1 * x2) -* (y1 * y2)).
Proof.
intros.
rewrite <- wand_sepcon_adjoint.
rewrite sepcon_assoc.
rewrite <- (sepcon_assoc _ x1).
rewrite <- (sepcon_comm x1).
rewrite (sepcon_assoc x1).
rewrite <- (sepcon_assoc _ x1).
rewrite <- (sepcon_comm x1).
rewrite <- (sepcon_comm x2).
apply sepcon_derives.
apply modus_ponens_wand.
apply modus_ponens_wand.
Qed.

Lemma wand_sepcon:
 forall {A} {NA: NatDed A}{SA: SepLog A} P Q,
   (P -* Q * P) * P = Q * P.
Proof.
intros.
apply pred_ext.
*
rewrite sepcon_comm.
apply modus_ponens_wand.
*
apply sepcon_derives; auto.
apply -> wand_sepcon_adjoint; auto.
Qed.

Lemma wand_sepcon':
 forall {A} {NA: NatDed A}{SA: SepLog A} P Q,
   P * (P -* Q * P) = P * Q.
Proof.
intros. rewrite (sepcon_comm P Q).
rewrite sepcon_comm; apply wand_sepcon.
Qed.


Hint Rewrite wand_sepcon wand_sepcon' : norm.



Lemma extract_nth_exists_in_SEP:
  forall n P Q (R: list mpred)
              {A} (S: A -> mpred),
   nth n R emp = (exp S) ->
   PROPx P (LOCALx Q (SEPx R)) =
   exp (fun x => PROPx P (LOCALx Q (SEPx (replace_nth n R (S x))))).
Proof.
intros.
transitivity (PROPx P (LOCALx Q (EX x:A, SEPx (replace_nth n R (S x))))).
*
f_equal. f_equal.
unfold SEPx.
simpl. extensionality rho.
revert R H; induction n; destruct R; intros.
unfold replace_nth, fold_right.
simpl.
unfold nth in H. rewrite H; clear H.
apply pred_ext.
apply exp_left; intro x. apply exp_right with x.
apply exp_right with x.
auto.
apply exp_left; intro x. auto.
unfold replace_nth, nth in *. subst m.
unfold fold_right_sepcon.
fold (fold_right_sepcon R).
normalize.
unfold nth in H. unfold replace_nth.
simpl.
rewrite H.
simpl.
apply pred_ext.
apply exp_left; intro x. apply exp_right with x.
apply exp_right with x.
auto.
apply exp_left; intro x. auto.
unfold nth in H.
fold (nth n R) in H.
simpl.
rewrite (IHn _ H). clear.
normalize.
*
unfold PROPx, LOCALx.
normalize.
Qed.

Ltac extract_exists_in_SEP' PQR :=
 match PQR with
 | PROPx ?P (LOCALx ?Q (SEPx (?R))) =>
   match R with context [(@exp _ _ ?A ?S) :: ?R'] =>
      let n := constr:((length R - Datatypes.S (length R'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      rewrite (@extract_nth_exists_in_SEP n' P Q R A S (eq_refl _));
      unfold replace_nth at 1;
      rewrite ?exp_andp2
   end
 end.

Ltac extract_exists_from_SEP :=
match goal with
  | |- semax _ ?Pre _ _ =>
    extract_exists_in_SEP' Pre; apply extract_exists_pre
  | |- _ && ?Pre |-- ?Post =>
     let P := fresh "POST" in set (P := Post);
    extract_exists_in_SEP' Pre; subst P; apply exp_left
  | |- ?Pre |-- ?Post => (* this case is obsolete, should probably be deleted *)
     let P := fresh "POST" in set (P := Post);
    extract_exists_in_SEP' Pre; subst P; apply exp_left
end.

Ltac move_from_SEP' PQR :=
 match PQR with
 | PROPx ?P (LOCALx ?Q (SEPx (?R))) =>
   match R with context [(prop ?P1 && ?S) :: ?R'] =>
      let n := constr:((length R - Datatypes.S (length R'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      rewrite(@extract_prop_in_SEP n' P1 S P Q R (eq_refl _));
      unfold replace_nth at 1
   end
 end.

Lemma derives_extract_PROP' :
  forall (P1: Prop) P QR S,
     (P1 -> PROPx P QR |-- S) ->
     PROPx (P1::P) QR |-- S.
Proof.
unfold PROPx in *.
intros.
rewrite fold_right_cons.
normalize.
eapply derives_trans; [ | apply H; auto].
normalize.
Qed.


Ltac Intro_prop :=
autorewrite with gather_prop;
match goal with
 | |- semax _ ?PQR _ _ =>
     first [ is_evar PQR; fail 1
            | simple apply semax_extract_PROP; fancy_intros false
            | move_from_SEP' PQR;
              simple apply semax_extract_PROP; fancy_intros false
            | flatten_in_SEP PQR
            ]
 | |- _ && ?PQR |-- _ =>
     first [ is_evar PQR; fail 1
            | simple apply derives_extract_prop; fancy_intros false
            | simple apply derives_extract_PROP; fancy_intros false
            | move_from_SEP' PQR;
               simple apply derives_extract_PROP; fancy_intros false
            | flatten_in_SEP PQR
             ]
 | |- ?PQR |-- _ =>  (* this case is obsolete, should probably be deleted *)
     first [ is_evar PQR; fail 1
            | simple apply derives_extract_prop; fancy_intros false
            | simple apply derives_extract_PROP; fancy_intros false
            | move_from_SEP' PQR;
               simple apply derives_extract_PROP; fancy_intros false
            | flatten_in_SEP PQR
             ]
end.

Ltac Intro'' a :=
  first [ simple apply extract_exists_pre; intro a
         | simple apply exp_left; intro a
         | rewrite exp_andp1; Intro'' a
         | rewrite exp_andp2; Intro'' a
         | rewrite exp_sepcon1; Intro'' a
         | rewrite exp_sepcon2; Intro'' a
         | extract_exists_from_SEP; intro a
         ].

Ltac Intro a :=
  repeat Intro_prop;
  match goal with
  | |- ?A |-- ?B =>
     let z := fresh "z" in pose (z:=B); change (A|--z); Intro'' a; subst z
  | |- semax _ _ _ _ =>
     Intro'' a
  end.

(* Tactic Notation "Intros" := repeat (let x := fresh "x" in Intro x). *)

Tactic Notation "Intros" := repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0) :=
 Intro x0; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) :=
 Intro x0; Intro x1; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2) :=
 Intro x0; Intro x1; Intro x2; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) :=
 Intro x0; Intro x1; Intro x2; Intro x3; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9;
 Intro x10; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10)
 simple_intropattern(x11) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9;
 Intro x10; Intro x11; repeat Intro_prop.


Ltac extract_exists_from_SEP_right :=
match goal with
  | |- ?Pre |-- ?Post =>
     let P := fresh "PRE" in set (P := Pre);
    extract_exists_in_SEP' Post; subst P
end.

Ltac Exists'' a :=
  first [apply exp_right with a
         | rewrite exp_andp1; Exists'' a
         | rewrite exp_andp2; Exists'' a
         | rewrite exp_sepcon1; Exists'' a
         | rewrite exp_sepcon2; Exists'' a
         | extract_exists_from_SEP_right; apply exp_right with a
         ].

Ltac Exists' a :=
  match goal with |- ?A |-- ?B =>
     let z := fresh "z" in pose (z:=A); change (z|--B); Exists'' a; subst z
  end.

Tactic Notation "Exists" constr(x0) :=
 Exists' x0.

Tactic Notation "Exists" constr(x0) constr(x1) :=
 Exists' x0; Exists x1.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) :=
 Exists' x0; Exists' x1; Exists' x2.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) constr(x11) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10; Exists' x11.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) constr(x11) constr(x12) :=
 Exists' x0; Exists' x1; Exists x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10; Exists' x11; Exists' x12.
