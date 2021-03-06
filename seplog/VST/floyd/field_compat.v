Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.type_induction.
Require Import floyd.nested_pred_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.reptype_lemmas.
Require floyd.aggregate_pred. Import floyd.aggregate_pred.aggregate_pred.
Require Import floyd.data_at_rec_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import floyd.sublist.
Require Import floyd.field_at.

Lemma field_compatible_offset_zero:
  forall {cs: compspecs} t gfs p,
    field_compatible t gfs p <-> field_compatible t gfs (offset_val 0 p).
Proof.
  intros.
  unfold field_compatible.
  destruct p; simpl; try tauto.
  rewrite !int_add_repr_0_r.
  tauto.
Qed.

Lemma field_address0_offset:
  forall {cs: compspecs} t gfs p,
    field_compatible0 t gfs p ->
    field_address0 t gfs p = offset_val (nested_field_offset t gfs) p.
Proof. intros. unfold field_address0; rewrite if_true by auto; reflexivity.
Qed.

(* TODO: This has already been proved in nested_field_lemmas, where it's named field_compatible_field_address. *)
Lemma field_address_offset:
  forall {cs: compspecs} t gfs p,
    field_compatible t gfs p ->
    field_address t gfs p = offset_val (nested_field_offset t gfs) p.
Proof. intros. unfold field_address; rewrite if_true by auto; reflexivity.
Qed.

Hint Extern 2 (field_compatible0 _ (ArraySubsc _ :: _) _) =>
   (eapply field_compatible0_cons_Tarray; [reflexivity | | omega])
  : field_compatible.

Hint Extern 2 (field_compatible _ (ArraySubsc _ :: _) _) =>
   (eapply field_compatible_cons_Tarray; [reflexivity | | omega])
  : field_compatible.

Lemma field_compatible_array_smaller0:
  forall {cs: compspecs} t n n' d,
  field_compatible (Tarray t n' noattr) nil d ->
  0 <= n <= n' ->
  field_compatible (Tarray t n noattr) nil d.
Proof.
intros until 1. pose proof I. intros.
hnf in H|-*.
destruct H as [? [? [? [? [? [? [? ?]]]]]]].
unfold sizeof in *; fold (sizeof t) in *.
rewrite Z.max_r in * by omega.
assert (sizeof t * n <= sizeof t * n')
  by (pose proof (sizeof_pos t); apply Z.mul_le_mono_nonneg_l; omega).
repeat split; auto.
*
unfold legal_alignas_type in *.
rewrite nested_pred_eq in H2|-*.
rewrite andb_true_iff in *; destruct H2; split; auto.
unfold local_legal_alignas_type in H2|-*.
rewrite andb_true_iff in *; destruct H2; split; auto.
rewrite andb_true_iff in *; destruct H11; split; auto.
apply Z.leb_le. tauto.
*
omega.
*
hnf in H6|-*.
destruct d; auto.
unfold sizeof in *; fold (sizeof t) in *.
rewrite Z.max_r in * by omega.
omega.
Qed.


Lemma field_compatible0_array_smaller0:
  forall {cs: compspecs} t n n' d,
  field_compatible0 (Tarray t n' noattr) nil d ->
  0 <= n <= n' ->
  field_compatible0 (Tarray t n noattr) nil d.
Proof.
intros until 1. pose proof I. intros.
hnf in H|-*.
destruct H as [? [? [? [? [? [? [? ?]]]]]]].
unfold sizeof in *; fold (sizeof t) in *.
rewrite Z.max_r in * by omega.
assert (sizeof t * n <= sizeof t * n')
  by (pose proof (sizeof_pos t); apply Z.mul_le_mono_nonneg_l; omega).
repeat split; auto.
*
unfold legal_alignas_type in *.
rewrite nested_pred_eq in H2|-*.
rewrite andb_true_iff in *; destruct H2; split; auto.
unfold local_legal_alignas_type in H2|-*.
rewrite andb_true_iff in *; destruct H2; split; auto.
rewrite andb_true_iff in *; destruct H11; split; auto.
apply Z.leb_le. omega.
*
omega.
*
hnf in H6|-*.
destruct d; auto.
unfold sizeof in *; fold (sizeof t) in *.
rewrite Z.max_r in * by omega.
omega.
Qed.


Hint Extern 2 (field_compatible (Tarray _ _ _) nil _) =>
   (eapply field_compatible_array_smaller0; [eassumption | omega]) : field_compatible.

Hint Extern 2 (field_compatible (tarray _ _) nil _) =>
   (eapply field_compatible_array_smaller0; [eassumption | omega]) : field_compatible.

Hint Extern 2 (field_compatible0 (Tarray _ _ _) nil _) =>
   (eapply field_compatible0_array_smaller0; [eassumption | omega]) : field_compatible.

Hint Extern 2 (field_compatible0 (tarray _ _) nil _) =>
   (eapply field_compatible0_array_smaller0; [eassumption | omega]) : field_compatible.

Lemma field_compatible0_array_smaller1:
  forall  {cs: compspecs} t i j n1 n2 p,
    field_compatible0 (Tarray t n1 noattr) (ArraySubsc j::nil) p ->
    0 <= i <= n2 ->
    n2 <= n1 ->
    field_compatible0 (Tarray t n2 noattr) (ArraySubsc i::nil) p.
Proof.
intros until p. intros H0 H' H.
move H0 after H.
hnf in H0|-*.
 assert (SS: sizeof t * n2 <= sizeof t * n1).
  apply Zmult_le_compat_l; auto.
  pose proof (sizeof_pos t); omega.
intuition.
 *
  unfold legal_alignas_type in H0|-*; simpl in H0|-*.
  rewrite nested_pred_eq in H0.
  rewrite nested_pred_eq.
  rewrite andb_true_iff in *. destruct H0; split; auto.
  clear - H1 H2 H0.
  unfold local_legal_alignas_type in *.
  rewrite andb_true_iff in *. destruct H0; split; auto.
  rewrite andb_true_iff in *. destruct H0; split; auto.
  eapply Zle_is_le_bool. omega.
 *
  unfold sizeof in H6|-*; fold (sizeof t) in *.
  rewrite Z.max_r in * by omega.
  eapply Z.le_lt_trans; eassumption.
 *
  destruct p; try contradiction; red in H7|-*.
  unfold sizeof in H7|-*; fold (sizeof t) in *.
  rewrite Z.max_r in * by omega.
  omega.
 *
  destruct H10; split; auto.
  simpl in H10|-*. omega.
Qed.

Hint Extern 2 (field_compatible0 (Tarray _ _ _) (ArraySubsc _ :: nil) _) =>
   (eapply field_compatible0_array_smaller1; [eassumption | omega | omega]) : field_compatible.

Hint Extern 2 (field_compatible0 (tarray _ _) (ArraySubsc _ :: nil) _) =>
   (eapply field_compatible0_array_smaller1; [eassumption | omega | omega]) : field_compatible.

Arguments nested_field_array_type {cs} t gfs lo hi / .

Hint Resolve field_compatible_field_compatible0 : field_compatible.

Lemma field_compatible0_ArraySubsc0:
 forall {cs: compspecs} t gfs p,
    field_compatible0 t gfs p ->
    legal_nested_field0 t (gfs SUB 0) ->
    field_compatible0 t (gfs SUB 0) p.
Proof.
intros. hnf in H|-*.
intuition.
Qed.

Lemma field_compatible_Tarray_split:
  forall {cs: compspecs} t i n d,
  0 <= i <= n ->
  (field_compatible (tarray t n) nil d <->
   field_compatible (tarray t i) nil d /\
   field_compatible (tarray t (n-i)) nil
       (field_address0 (tarray t n) (ArraySubsc i::nil) d)).
Proof.
intros.
unfold tarray in *.
split; intros.
assert (SP := sizeof_pos t).
assert (SL: sizeof t * i <= sizeof t * n)
  by (apply Zmult_le_compat_l; omega).
assert (SL': sizeof t * (n-i) <= sizeof t * n)
  by (apply Zmult_le_compat_l; omega).
assert (ST: 0*0 <= sizeof t * i).
apply Zmult_le_compat; omega.
change (0*0)%Z with 0 in ST.
assert (field_compatible (Tarray t i noattr) nil d /\
           field_compatible (Tarray t (n - i) noattr) nil
               (offset_val (sizeof t * i) d) /\
           field_compatible0 (Tarray t n noattr) (ArraySubsc i::nil) d). {
  unfold field_compatible, field_compatible0 in *.
decompose [and] H0; clear H0.
destruct d; try contradiction.
intuition.
*
unfold legal_alignas_type in H3|-*.
rewrite nested_pred_eq, andb_true_iff in H3|-*.
destruct H3; split; auto.
unfold local_legal_alignas_type in H|-*.
rewrite andb_true_iff in H|-*; destruct H.
rewrite andb_true_iff in H10 |-*; destruct H10.
split; auto.
split; auto.
apply Z.leb_le; auto.
*
unfold sizeof in H5|-*. fold sizeof in H5|-*.
rewrite Z.max_r in H5|-* by omega.
omega.
*
unfold size_compatible in H6|-*.
unfold sizeof in H6|-*. fold sizeof in H6 |-*.
rewrite Z.max_r in H6|-* by omega.
omega.
*
unfold legal_alignas_type in H3|-*.
rewrite nested_pred_eq, andb_true_iff in H3|-*.
destruct H3; split; auto.
unfold local_legal_alignas_type in H|-*.
rewrite andb_true_iff in H|-*; destruct H; split; auto.
rewrite andb_true_iff in H10|-*; destruct H10; split; auto.
apply Z.leb_le; omega.
*
unfold sizeof in H5|-*. fold sizeof in H5|-*.
rewrite Z.max_r in H5|-* by omega.
omega.
*
unfold size_compatible in H6|-*.
unfold offset_val.
rewrite <- (Int.repr_unsigned i0).
rewrite add_repr.
unfold sizeof in H6|-*. fold sizeof in H6 |-*.
rewrite Z.max_r in H6|-* by omega.
pose proof (Int.unsigned_range i0).
destruct (zeq (Int.unsigned i0 + sizeof t * i) Int.modulus).
rewrite e.
change (Int.unsigned (Int.repr Int.modulus)) with 0.
rewrite Z.add_0_l.
omega.
rewrite Int.unsigned_repr.
assert (sizeof t * i + sizeof t * (n - i)  =  sizeof t * n)%Z.
rewrite <- Z.mul_add_distr_l.
f_equal. omega.
omega.
change Int.max_unsigned with (Int.modulus-1).
omega.
*
unfold align_compatible in H7|-*.
unfold offset_val.
rewrite <- (Int.repr_unsigned i0).
rewrite add_repr.
destruct (zeq (Int.unsigned i0 + sizeof t * i) Int.modulus).
rewrite e.
change (Int.unsigned (Int.repr Int.modulus)) with 0.
apply Z.divide_0_r.
rewrite Int.unsigned_repr.
apply Z.divide_add_r; auto.
unfold alignof. fold alignof.
unfold attr_of_type, noattr, align_attr, attr_alignas.
apply Z.divide_mul_l; auto.
clear - H3.
apply (legal_alignas_type_Tarray _ _ _ H3).
unfold legal_alignas_type in H3.
rewrite nested_pred_eq in H3.
unfold legal_alignas_type.
rewrite andb_true_iff in H3; destruct H3; auto.
pose proof (Int.unsigned_range i0).
split; try omega.
unfold size_compatible in H6.
unfold sizeof in H6. fold sizeof in H6.
rewrite Z.max_r in H6 by omega.
change Int.max_unsigned with (Int.modulus-1).
omega.
*
split; auto.
split; auto.
}
destruct H1 as [? [? ?]].
rewrite field_address0_offset.
split; auto.
auto.
destruct H0.
unfold field_address0 in H1.
if_tac in H1; [ | destruct H1; contradiction].
clear H1.
hnf in H0,H2|-*.
intuition.
Qed.

Hint Resolve field_compatible0_ArraySubsc0 : field_compatible.

Hint Extern 2 (legal_nested_field0 _ _) =>
  (apply compute_legal_nested_field0_spec'; repeat constructor; omega) : field_compatible.
Hint Extern 2 (field_compatible0 _ _ (offset_val _ _)) =>
  (apply field_compatible0_nested_field_array; auto with field_compatible).

Lemma split2_data_at_Tarray_unfold {cs: compspecs}
     sh t n n1 v (v': list (reptype t)) v1 v2 p:
   0 <= n1 <= n ->
  JMeq v v' ->
  JMeq v1 (sublist 0 n1 v') ->
  JMeq v2 (sublist n1 n v') ->
  data_at sh (Tarray t n noattr) v p |--
  data_at sh (Tarray t n1 noattr) v1 p *
  data_at sh (Tarray t (n - n1) noattr) v2
    (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p).
Proof.
  intros.
  assert_PROP (Zlength v' = n). {
    eapply derives_trans; [apply data_at_local_facts | apply prop_derives].
    intros [? ?]. destruct H4 as [? _]. rewrite Z.max_r in H4 by omega.
    rewrite <- H4. f_equal. apply JMeq_eq. eapply JMeq_trans; [apply @JMeq_sym; exact H0 |].
    apply @JMeq_sym. apply (unfold_reptype_JMeq _ v).
  }
  assert_PROP (field_compatible0 (Tarray t n noattr) (ArraySubsc n1::nil) p). {
     eapply derives_trans; [apply data_at_local_facts | apply prop_derives].
     intros [? _]; auto with field_compatible.
  }
  rewrite field_address0_offset by auto.
  rewrite !nested_field_offset_ind by (repeat split; auto; omega).
  rewrite nested_field_type_ind. unfold gfield_offset.
  rewrite Z.add_0_l.
  rewrite data_at_isptr at 1.
  unfold data_at at 1. intros; simpl; normalize.
  erewrite (field_at_Tarray sh  (Tarray t n noattr) _ t); try reflexivity; trivial.
  2: omega. 2: eauto.
  rewrite (split2_array_at sh (Tarray t n noattr) nil 0 n1).
  2: auto. 2: rewrite Z.sub_0_r; auto.
  do 2 rewrite array_at_data_at by tauto.
  rewrite Zminus_0_r.
  unfold at_offset.
  erewrite (data_at_type_changable sh
            (nested_field_array_type (Tarray t n noattr) nil 0 n1)
            (Tarray t n1 noattr) _ v1).
  2: unfold nested_field_array_type; simpl; rewrite Zminus_0_r; trivial.
  2: eapply JMeq_trans; [| apply @JMeq_sym, H1]; apply @fold_reptype_JMeq.
  erewrite (data_at_type_changable sh
            (nested_field_array_type (Tarray t n noattr) nil n1 n)
            (Tarray t (n - n1) noattr) _  v2).
  2: unfold nested_field_array_type; simpl; trivial.
  2: eapply JMeq_trans; [| apply @JMeq_sym, H2]; subst n; apply @fold_reptype_JMeq.
  rewrite !nested_field_offset_ind by (repeat split; auto; omega).
  rewrite !nested_field_type_ind.
  unfold gfield_offset.
  rewrite !Z.add_0_l. rewrite Z.mul_0_r.
  rewrite isptr_offset_val_zero; trivial.
  normalize.
Qed.

Lemma split2_data_at_Tarray_fold {cs: compspecs} sh t n n1 v (v': list (reptype t)) v1 v2 p:
   0 <= n1 <= n ->
   JMeq v (sublist 0 n v') ->
   JMeq v1 (sublist 0 n1 v') ->
   JMeq v2 (sublist n1 n v') ->
   data_at sh (Tarray t n1 noattr) v1 p *
   data_at sh (Tarray t (n - n1) noattr) v2
        (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p)
   |--
   data_at sh (Tarray t n noattr) v p.
Proof.
  intros.
  unfold field_address0.
  if_tac; [ |
  eapply derives_trans; [apply sepcon_derives;
           apply prop_and_same_derives; apply data_at_local_facts
    | normalize ];
  destruct H6; contradiction].
  assert_PROP (field_compatible (Tarray t n noattr) nil p). {
    eapply derives_trans.
    apply sepcon_derives; apply prop_and_same_derives; apply data_at_local_facts .
    normalize. apply prop_right.
   clear - H3 H4 H.
   hnf in H3,H4|-*; intuition.
  } clear H3; rename H4 into H3.
  assert_PROP (n1 <= Zlength v'). {
    eapply derives_trans.
    apply sepcon_derives; apply prop_and_same_derives; apply data_at_local_facts .
    normalize. apply prop_right.
    destruct H5 as [? _], H7 as [? _].
    rewrite Z.max_r in * by omega.
    clear - H7 H5 H2 H1 H0 H H6.
    assert (Zlength (sublist 0 n1 v') = n1).
       rewrite <- H5 at 2. f_equal. apply JMeq_eq. eapply JMeq_trans; [apply @JMeq_sym; apply H1 |].
       apply @JMeq_sym, (unfold_reptype_JMeq _ v1).
    clear - H H3. unfold sublist in *.
   rewrite Zlength_correct in *.
   rewrite firstn_length in *. rewrite skipn_length in H3.
   change (Z.to_nat 0) with 0%nat in H3.
    rewrite !Z.sub_0_r in H3. rewrite NPeano.Nat.sub_0_r in H3.
   rewrite Nat2Z.inj_min in H3. rewrite Z2Nat.id in H3 by omega.
   rewrite Z.min_l_iff in  H3. auto.
  }
  rewrite data_at_isptr at 1. unfold at_offset. intros; normalize.
  unfold data_at at 3.  erewrite field_at_Tarray; try reflexivity; eauto; try omega.
  rewrite (split2_array_at sh (Tarray t n noattr) nil 0 n1); trivial.
  change (@reptype cs
            (@nested_field_type cs (Tarray t n noattr) (ArraySubsc 0 ::nil)))
   with (@reptype cs t).
  assert (Zlength (sublist 0 n v') = Z.min n (Zlength v')). {
     clear - H. unfold sublist. rewrite Z.sub_0_r. change (skipn (Z.to_nat 0) v') with v'.
  rewrite Zlength_firstn. rewrite Z.max_r by omega. auto.
  }
  rewrite H5. rewrite Z.sub_0_r.
  autorewrite with sublist.
  rewrite sublist_sublist; try omega.
  2:  destruct (Z.min_spec n (Zlength v')) as [[? ?]|[? ?]]; rewrite H7; omega.
  2:  destruct (Z.min_spec n (Zlength v')) as [[? ?]|[? ?]]; rewrite H7; omega.
  rewrite !Z.add_0_r.
  unfold data_at at 1; erewrite field_at_Tarray; try reflexivity; eauto; try omega.
  unfold data_at at 1; erewrite field_at_Tarray; try reflexivity; eauto; try omega.
  apply sepcon_derives.
  unfold array_at.
  simpl. apply andp_derives; auto.
  apply prop_derives. intuition.
  assert (sublist n1 (Z.min n (Zlength v')) v' = sublist n1 n v').
     admit.  (* true, but tedious *)
  rewrite H6. clear H6.
  clear - H H3.
  rewrite array_at_data_at by omega. normalize.
  rewrite array_at_data_at by omega.
  rewrite !prop_true_andp by auto with field_compatible.
  unfold at_offset.
  apply derives_refl'.
  rewrite offset_offset_val.
  rewrite !nested_field_offset_ind by (repeat split; auto; omega).
  rewrite !nested_field_type_ind. unfold gfield_offset.
  rewrite !Z.add_0_l. rewrite Z.mul_0_r, Z.add_0_r.
  apply equal_f.
  apply data_at_type_changable.
  unfold nested_field_array_type.
  rewrite !nested_field_type_ind.  unfold gfield_type. simpl. f_equal; omega.
  unfold nested_field_array_type. simpl.
  eapply JMeq_trans; [apply fold_reptype_JMeq |].
  eapply JMeq_trans; [| eapply @JMeq_sym; apply fold_reptype_JMeq].
  apply JMeq_refl.
  admit.
Admitted.

Lemma split2_data_at_Tarray {cs: compspecs} sh t n n1 v (v': list (reptype t)) v1 v2 p:
   0 <= n1 <= n ->
   JMeq v (sublist 0 n v') ->
   JMeq v1 (sublist 0 n1 v') ->
   JMeq v2 (sublist n1 n v') ->
   data_at sh (Tarray t n noattr) v p =
    data_at sh (Tarray t n1 noattr) v1 p *
    data_at sh (Tarray t (n - n1) noattr) v2 (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p).
Proof. intros.
 apply pred_ext.
 eapply split2_data_at_Tarray_unfold; try eassumption.
  autorewrite with sublist; auto.
  autorewrite with sublist; auto.
 eapply split2_data_at_Tarray_fold; try eassumption.
Qed.

Lemma field_compatible0_Tarray_offset:
 forall {cs: compspecs} t n i n' i' p p',
  field_compatible0 (Tarray t n' noattr) (ArraySubsc i' :: nil) p ->
  naturally_aligned t ->
  0 <= n <= n' ->
  0 <= i <= n ->
  n-i <= n'-i' ->
  i <= i' ->
  p' = offset_val (sizeof t * (i'-i)) p ->
  field_compatible0 (Tarray t n noattr) (ArraySubsc i :: nil) p'.
Proof.
intros until 1. intros NA ?H ?H Hni Hii Hp. subst p'.
  assert (SP := sizeof_pos t).
  assert (SS: sizeof t * n <= sizeof t * n').
  apply Zmult_le_compat_l. omega. omega.
  assert (SS': (sizeof t * n + sizeof t * (n'-n) = sizeof t * n')%Z).
  rewrite <- Z.mul_add_distr_l. f_equal. omega.
  hnf in H|-*.
  intuition.
  *
  unfold legal_alignas_type in H1|-*; simpl in H1|-*.
  rewrite nested_pred_eq in H1.
  rewrite nested_pred_eq.
  rewrite andb_true_iff in *. destruct H1; split; auto.
  unfold local_legal_alignas_type in *.
  rewrite andb_true_iff in *. destruct H1; split; auto.
  rewrite andb_true_iff in *. destruct H12; split; auto.
  eapply Zle_is_le_bool. omega.
  *
  unfold sizeof in H7|-*; fold (sizeof t) in *.
  rewrite Z.max_r in * by omega. omega.
  *
  destruct p; try contradiction.
  clear - SP SS SS' H H4 H0 H5 H7 H8 Hni Hii.
  red in H8|-*.
  simpl in H7,H8|-*. rewrite Z.max_r in H7,H8|-* by omega.
  rename i0 into j.
   pose proof (Int.unsigned_range j).
   assert (0 <= sizeof t * (i'-i) <= sizeof t * n').
   split. apply Z.mul_nonneg_nonneg; omega.
   apply Zmult_le_compat_l. omega. omega.
  assert (sizeof t * (i'-i+n) <= sizeof t * n').
   apply Zmult_le_compat_l. omega. omega.
  unfold Int.add.
  rewrite (Int.unsigned_repr (_ * _))
    by (change Int.max_unsigned with (Int.modulus -1); omega).
   rewrite Int.unsigned_repr_eq.
  apply Z.le_trans with
    ((Int.unsigned j + sizeof t * (i' - i))+ sizeof t * n ).
   apply Zplus_le_compat_r.
   apply Zmod_le. computable.
   omega.
  rewrite <- Z.add_assoc. rewrite <- Z.mul_add_distr_l. omega.
 *
  destruct p; try contradiction.
  clear H1 H3 H6 H7 H11.
  simpl in H8,H9|-*. rewrite Z.max_r in * by omega.
    unfold align_attr, noattr in *. simpl in *.
  apply (sizeof_alignof_compat cenv_cs) in NA.
  unfold Int.add.
   rewrite !Int.unsigned_repr_eq.
  assert (Int.modulus <> 0) by computable.
  rewrite Z.add_mod by auto.
  rewrite Z.mod_mod by auto.
  rewrite <- Z.add_mod by auto.
  apply arith_aux04.
  rename i0 into j.
   pose proof (Int.unsigned_range j).
   assert (0 <= sizeof t * (i'-i) <= sizeof t * n').
   split. apply Z.mul_nonneg_nonneg; omega.
   apply Zmult_le_compat_l. omega. omega.
   omega.
  apply Z.divide_add_r; auto.
  apply Z.divide_mul_l; auto.
Qed.

(*
Hint Extern 2 (field_compatible0 (Tarray _ _ _) (ArraySubsc _ :: nil) _) =>
    (eapply field_compatible0_Tarray_offset; [eassumption | omega | omega]) : field_compatible.

Hint Extern 2 (field_compatible0 (tarray _ _) (ArraySubsc _ :: nil) _) =>
    (eapply field_compatible0_Tarray_offset; [eassumption | omega | omega]) : field_compatible.
*)

Lemma split3_data_at_Tarray {cs: compspecs} sh t n n1 n2 v (v': list (reptype t)) v1 v2 v3 p:
   naturally_aligned t ->
   0 <= n1 <= n2 ->
   n2 <= n ->
   JMeq v (sublist 0 n v') ->
   JMeq v1 (sublist 0 n1 v') ->
   JMeq v2 (sublist n1 n2 v') ->
   JMeq v3 (sublist n2 n v') ->
   data_at sh (Tarray t n noattr) v p =
    data_at sh (Tarray t n1 noattr) v1 p *
    data_at sh (Tarray t (n2 - n1) noattr) v2 (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p) *
    data_at sh (Tarray t (n - n2) noattr) v3 (field_address0 (Tarray t n noattr) (ArraySubsc n2::nil) p).
Proof. intros until 1. rename H into NA; intros.
  destruct (field_compatible0_dec (tarray t n) (ArraySubsc n2::nil) p).
  erewrite (split2_data_at_Tarray sh t n n1); try eassumption; try omega.
  instantiate (1:= @fold_reptype cs (Tarray t (n - n1) noattr) (sublist n1 n v')).
  2: apply @fold_reptype_JMeq.
  erewrite (split2_data_at_Tarray sh t (n-n1) (n2-n1)); try eassumption; try omega.
  2: instantiate (1:= sublist n1 n v'); autorewrite with sublist;
     apply @fold_reptype_JMeq.
  2: autorewrite with sublist;
     instantiate (1:= @fold_reptype cs (Tarray t (n2-n1) noattr) (sublist n1 n2 v'));
     apply @fold_reptype_JMeq.
  2: autorewrite with sublist;
     instantiate (1:= @fold_reptype cs (Tarray t (n-n1-(n2-n1)) noattr) (sublist n2 n v'));
     apply @fold_reptype_JMeq.
  rewrite sepcon_assoc.
  f_equal. f_equal. f_equal. apply JMeq_eq.
  eapply JMeq_trans; [apply fold_reptype_JMeq | apply @JMeq_sym, H3].
  replace  (field_address0 (Tarray t (n - n1) noattr) (SUB (n2 - n1))
     (field_address0 (Tarray t n noattr) (SUB n1) p))
   with (field_address0 (Tarray t n noattr) (SUB n2) p).
  apply equal_f.
  apply data_at_type_changable.
  f_equal. omega.
  eapply JMeq_trans; [apply @fold_reptype_JMeq |]; apply JMeq_sym; auto.
  rewrite field_address0_offset by auto with field_compatible.
  rewrite (field_address0_offset (Tarray t n noattr) ) by auto with field_compatible.
  rewrite field_address0_offset.
  rewrite offset_offset_val. f_equal.
  rewrite !nested_field_offset_ind by auto with field_compatible.
  rewrite !nested_field_type_ind;   unfold gfield_offset.
  rewrite Z.mul_sub_distr_l.
  omega.
  rewrite !nested_field_offset_ind by auto with field_compatible.
  rewrite !nested_field_type_ind;   unfold gfield_offset.
  rewrite Z.add_0_l.
  eapply field_compatible0_Tarray_offset; try eassumption; try omega.
  f_equal. f_equal. f_equal. omega.
  apply pred_ext.
  eapply derives_trans. apply data_at_local_facts. normalize.
  contradiction n0. auto with field_compatible.
  unfold field_address0 at 2.
  if_tac.
  contradiction n0. auto with field_compatible.
  eapply derives_trans. apply sepcon_derives; [apply derives_refl | ].
  apply prop_and_same_derives; apply data_at_local_facts .
  normalize. destruct H6 as [H6 _]; contradiction H6.
Qed.

Lemma split2_data_at_Tarray_tuchar {cs: compspecs} sh n n1 v p:
   0 <= n1 <= n ->
   Zlength v = n ->
   data_at sh (Tarray tuchar n noattr) v p =
    data_at sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
    data_at sh (Tarray tuchar (n - n1) noattr) (sublist n1 n v) (field_address0 (Tarray tuchar n noattr) (ArraySubsc n1::nil) p).
Proof. intros.
 eapply split2_data_at_Tarray; auto.
 symmetry in H0.
 rewrite sublist_same; try omega; auto.
Qed.

Lemma split3_data_at_Tarray_tuchar {cs: compspecs} sh n n1 n2 v p:
   0 <= n1 <= n2 ->
   n2 <= n ->
   Zlength v = n ->
   data_at sh (Tarray tuchar n noattr) v p =
    data_at sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
    data_at sh (Tarray tuchar (n2 - n1) noattr) (sublist n1 n2 v) (field_address0 (Tarray tuchar n noattr) (ArraySubsc n1::nil) p) *
    data_at sh (Tarray tuchar (n - n2) noattr) (sublist n2 n v) (field_address0 (Tarray tuchar n noattr) (ArraySubsc n2::nil) p).
Proof. intros.
 eapply split3_data_at_Tarray; auto.
  split; simpl; auto.
 rewrite sublist_same; try omega; auto.
Qed.

Lemma sizeof_tarray_tuchar {cs} n (N:0<=n): @sizeof cs (tarray tuchar n) = n.
Proof. simpl. rewrite Z.max_r. destruct n; trivial. omega. Qed. 

Opaque sizeof.
Import ListNotations.

Lemma memory_block_field_compatible_tarraytuchar_ent {cs} sh n p (N:0<=n < Int.modulus):
memory_block sh n p |-- !! @field_compatible cs (tarray tuchar n) nil p.
Proof. Transparent memory_block. unfold memory_block. Opaque memory_block.
   destruct p; try solve [apply FF_left]. normalize.
   apply prop_right. red.
   destruct (Int.unsigned_range i). simpl.
   repeat split; try rewrite sizeof_tarray_tuchar; trivial; try omega.
    unfold legal_alignas_type, nested_pred, local_legal_alignas_type; simpl.
      rewrite Zle_imp_le_bool; trivial; omega.
    unfold align_attr; simpl. apply Z.divide_1_l.
Qed.

Lemma memory_block_field_compatible_tarraytuchar {cs} sh n p (N:0<=n < Int.modulus):
memory_block sh n p = !!(@field_compatible cs (tarray tuchar n) nil p) && memory_block sh n p.
Proof. apply pred_ext. apply andp_right; trivial. apply memory_block_field_compatible_tarraytuchar_ent; trivial.
normalize.
Qed. 

Lemma memory_block_data_at__tarray_tuchar {cs} sh p n (N: 0<=n < Int.modulus):
  memory_block sh n p |-- @data_at_ cs sh (tarray tuchar n) p.
Proof. 
  rewrite memory_block_field_compatible_tarraytuchar, memory_block_isptr; trivial. 
  normalize. destruct p; try solve [inv Pp].
  unfold data_at_, data_at.
  rewrite field_at__memory_block. 
  unfold field_address. rewrite if_true; trivial.
  unfold nested_field_offset, nested_field_type; simpl.
  rewrite Int.add_zero, sizeof_tarray_tuchar; trivial; omega.
Qed.

Lemma memory_block_data_at__tarray_tuchar_eq {cs} sh p n (N: 0<=n < Int.modulus):
  memory_block sh n p = @data_at_ cs sh (tarray tuchar n) p.
Proof.
  apply pred_ext. apply memory_block_data_at__tarray_tuchar; trivial.
  rewrite data_at__memory_block; simpl. normalize. rewrite sizeof_tarray_tuchar; trivial; omega. 
Qed.

Lemma isptr_field_compatible_tarray_tuchar0 {cs} p: isptr p -> 
      @field_compatible cs (tarray tuchar 0) nil p.
Proof. intros; red. destruct p; try contradiction.
  repeat split; simpl; try rewrite sizeof_tarray_tuchar; trivial; try omega.
  destruct (Int.unsigned_range i); omega.
  apply Z.divide_1_l. 
Qed. 

Lemma data_at_tuchar_singleton_array {cs} sh v p:
  @data_at cs sh tuchar v p |-- @data_at cs sh (tarray tuchar 1) [v] p.  
Proof. 
  rewrite data_at_isptr. normalize.
  assert_PROP (field_compatible (tarray tuchar 1) [] p).
  { eapply derives_trans. eapply data_at_local_facts. normalize. }
  unfold data_at at 2.
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: apply JMeq_refl. 2: simpl; trivial. 
  erewrite array_at_len_1. 2: apply JMeq_refl.
  rewrite field_at_data_at; simpl. 
  rewrite field_address_offset; trivial.
    simpl. rewrite isptr_offset_val_zero; trivial.
  eapply field_compatible_cons_Tarray. reflexivity. trivial. omega.
Qed.
 
Lemma data_at_tuchar_singleton_array_inv {cs} sh v p:
  @data_at cs sh (tarray tuchar 1) [v] p |-- @data_at cs sh tuchar v p.  
Proof. 
  rewrite data_at_isptr. normalize.
  assert_PROP (field_compatible (tarray tuchar 1) [] p).
  { eapply derives_trans. eapply data_at_local_facts. normalize. }
  unfold data_at at 1.
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: apply JMeq_refl. 2: simpl; trivial. 
  erewrite array_at_len_1. 2: apply JMeq_refl.
  rewrite field_at_data_at; simpl. 
  rewrite field_address_offset; trivial.
    simpl. rewrite isptr_offset_val_zero; trivial.
  eapply field_compatible_cons_Tarray. reflexivity. trivial. omega.
Qed.
 
Lemma data_at_tuchar_singleton_array_eq {cs} sh v p:
  @data_at cs sh (tarray tuchar 1) [v] p = @data_at cs sh tuchar v p.  
Proof. apply pred_ext.
  apply data_at_tuchar_singleton_array_inv.
  apply data_at_tuchar_singleton_array. 
Qed. 

Lemma data_at_tuchar_zero_array {cs} sh p: isptr p ->
  emp |-- @data_at cs sh (tarray tuchar 0) [] p.  
Proof. intros.
  unfold data_at. 
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: apply JMeq_refl. 2: simpl; trivial. 
  rewrite array_at_len_0. apply andp_right; trivial.
  apply prop_right. apply isptr_field_compatible_tarray_tuchar0 in H.
  unfold field_compatible in H.  
  unfold field_compatible0; simpl in *. intuition.
Qed.

Lemma data_at_tuchar_zero_array_inv {cs} sh p:
  @data_at cs sh (tarray tuchar 0) [] p |-- emp.  
Proof. intros.
  unfold data_at. 
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: apply JMeq_refl. 2: simpl; trivial. 
  rewrite array_at_len_0. normalize. 
Qed.

Lemma data_at_tuchar_zero_array_eq {cs} sh p:
  isptr p ->
  @data_at cs sh (tarray tuchar 0) [] p = emp.  
Proof. intros.
  apply pred_ext.
  apply data_at_tuchar_zero_array_inv.
  apply data_at_tuchar_zero_array; trivial.
Qed. 

Lemma data_at__tuchar_zero_array {cs} sh p (H: isptr p):
  emp |-- @data_at_ cs sh (tarray tuchar 0) p.  
Proof. unfold data_at_, field_at_. apply data_at_tuchar_zero_array; trivial. Qed.

Lemma data_at__tuchar_zero_array_inv {cs} sh p:
  @data_at_ cs sh (tarray tuchar 0) p |-- emp.  
Proof. unfold data_at_, field_at_. apply data_at_tuchar_zero_array_inv. Qed.

Lemma data_at__tuchar_zero_array_eq {cs} sh p (H: isptr p):
  @data_at_ cs sh (tarray tuchar 0) p = emp.  
Proof. intros.
  apply pred_ext.
  apply data_at__tuchar_zero_array_inv.
  apply data_at__tuchar_zero_array; trivial.
Qed. 

Lemma split2_data_at__Tarray_tuchar
     : forall {cs} (sh : Share.t)  (n n1 : Z) (p : val),
       0 <= n1 <= n -> isptr p ->field_compatible (Tarray tuchar n noattr) [] p ->
       @data_at_ cs sh (Tarray tuchar n noattr) p =
       @data_at_ cs sh (Tarray tuchar n1 noattr) p *
       @data_at_ cs sh (Tarray tuchar (n - n1) noattr)
         (field_address0 (Tarray tuchar n noattr) [ArraySubsc n1] p).
Proof. intros. unfold data_at_ at 1; unfold field_at_.
rewrite field_at_data_at.
erewrite (@split2_data_at_Tarray cs sh tuchar n n1).
instantiate (1:= list_repeat (Z.to_nat (n-n1)) Vundef).
instantiate (1:= list_repeat (Z.to_nat n1) Vundef).
unfold field_address. simpl. 
rewrite if_true; trivial. rewrite isptr_offset_val_zero; trivial.
trivial.
simpl.
instantiate (1:=list_repeat (Z.to_nat n) Vundef).
unfold default_val. simpl. autorewrite with sublist. apply JMeq_refl. 
unfold default_val. simpl. autorewrite with sublist. apply JMeq_refl. 
unfold default_val. simpl. autorewrite with sublist. apply JMeq_refl.
Qed. 
