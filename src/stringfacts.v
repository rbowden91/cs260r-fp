Require Import String.
Require Import Ascii.
Require Import Bool.
Require Import Arith.
Require Import Omega.
Require Import Program.Tactics.

(*
 * I should polish this up and get merged upstream.
 * coq's string library is a disgrace.
 *)

Section MissingListBits.

   (* XXX why isn't this in the library? or is it and I can't find it? *)
   Function take {T} (n: nat) (xs: list T) :=
      match n, xs with
      | S n, (x :: more)%list => (x :: take n more)%list
      | _, _ => nil
      end.

   Lemma take_length:
      forall T (xs : list T) n,
      List.length (take n xs) <= List.length xs.
   Proof.
      intros. revert n.
      induction xs; intros.
      - destruct n; rewrite take_equation; auto.
      - destruct n; rewrite take_equation; simpl; try omega.
        apply le_n_S. apply IHxs.
   Qed.

   Lemma take_length_strict:
      forall T (xs : list T) n,
      n <= List.length xs -> List.length (take n xs) = n.
   Proof.
      intros. revert H. revert n.
      induction xs; intros.
      - simpl in H. assert (n = 0) by omega. subst. simpl. reflexivity.
      - destruct n; rewrite take_equation; simpl in *; try apply eq_S; try apply IHxs; omega.
   Qed.

   Lemma take_correctness:
      forall T n (xs : list T) k x,
         k < n -> List.nth k (take n xs) x = List.nth k xs x.
   Proof.
      intros T n xs. revert n.
      induction xs; intros;
         rewrite take_equation;
         destruct n; destruct k;
         simpl; try discriminate;
         try apply IHxs; try omega;
         auto.
   Qed.

   Lemma take_correctness_2:
      forall T n (xs : list T) k x,
         k >= n -> List.nth k (take n xs) x = x.
   Proof.
      intros T n xs. revert n.
      induction xs; intros;
         rewrite take_equation;
         destruct n; destruct k;
         simpl; try apply IHxs; try omega; auto.
   Qed.

   (* and I'd expect to find this too... *)
   Function natlist_sum (ns : list nat): nat :=
      match ns with
      | nil => 0
      | (n :: more)%list => n + (natlist_sum more)
      end.

   Lemma natlist_sum_ge:
      forall n ns,
      List.In n ns -> natlist_sum ns >= n.
   Proof.
      intros.
      revert H. revert n.
      induction ns; intros.
      - unfold List.In in H. contradiction.
      - rewrite natlist_sum_equation.
        apply List.in_inv in H.
        destruct H; subst; try apply IHns in H; try omega.
   Qed.

   (* not sure what else to prove about natlist_sum *)

End MissingListBits.

Section CharacterFacts.
   (*
    * These bits are from pset3regex
    *)

  (* `ascii_eq` is an executable equality test for characters. *)
  Definition ascii_eq (a b:ascii) : bool :=
    match (a, b) with
    | (Ascii a1 a2 a3 a4 a5 a6 a7 a8,
       Ascii b1 b2 b3 b4 b5 b6 b7 b8) =>
      eqb a1 b1 && eqb a2 b2 && eqb a3 b3 && eqb a4 b4 &&
          eqb a5 b5 && eqb a6 b6 && eqb a7 b7 && eqb a8 b8
    end.

  Lemma ascii_eq_refl (a:ascii):
    ascii_eq a a = true.
  Proof.
    destruct a; unfold ascii_eq; repeat rewrite eqb_reflx; simpl; auto.
  Qed.

  (* `ascii_eq` is equivalent to character equality. *)
  Lemma ascii_eq_iff a b:
    ascii_eq a b = true <-> a = b.
  Proof.
    split; intros.
    - unfold ascii_eq in H; destruct a; destruct b;
        repeat rewrite andb_true_iff in *; destruct_pairs;
          rewrite eqb_true_iff in *; congruence.
    - rewrite H; apply ascii_eq_refl.
  Qed.

  (*
   * These bits are mine
   *)

  (* we also need inequality *)
  Lemma ascii_neq_iff a b:
    ascii_eq a b = false <-> a <> b.
  Proof.
    split; intros.
    - unfold ascii_eq in H; destruct a; destruct b;
        repeat rewrite andb_false_iff in *.
        repeat rewrite eqb_false_iff in *.
        injection.
        (* destruct pairs doesn't work... *)
        repeat (destruct H; auto).
    - unfold ascii_eq; destruct a; destruct b.
      unfold eqb.
      (* there must be a better way to do this... *)
      destruct b; destruct b0; auto; destruct b1; destruct b8; auto; simpl;
      destruct b2; destruct b9; auto; destruct b3; destruct b10; auto; simpl;
      destruct b4; destruct b11; auto; destruct b5; destruct b12; auto; simpl;
      destruct b6; destruct b13; auto; destruct b7; destruct b14; auto; simpl;
      contradiction.
  Qed.

End CharacterFacts.

Section StringFacts.

  (*
   * These bits are from pset3regex
   *)

  Lemma append_nil_l s:
    ("" ++ s)%string = s.
  Proof.
    simpl; auto.
  Qed.

  Lemma append_nil_r s:
    (s ++ "")%string = s.
  Proof.
    induction s; simpl; try rewrite IHs; auto.
  Qed.

  Lemma append_assoc s1 s2 s3:
    (s1 ++ s2 ++ s3)%string = ((s1 ++ s2) ++ s3)%string.
  Proof.
    induction s1; simpl; try rewrite IHs1; auto.
  Qed.

  Lemma append_comm_cons a s1 s2:
    (String a s1 ++ s2)%string = String a (s1 ++ s2)%string.
  Proof.
    induction s1; simpl; auto.
  Qed.


  Definition strlen := String.length.

  Lemma append_strlen_l s1 s2:
    strlen s1 <= strlen (s1 ++ s2).
  Proof.
    induction s1; simpl; try rewrite IHs1; omega.
  Qed.

  Lemma append_strlen_r s1 s2:
    strlen s1 <= strlen (s1 ++ s2).
  Proof.
    induction s1; simpl; try rewrite IHs1; omega.
  Qed.

  (*
   * These bits are mine.
   *)
  Lemma length_zero_empty:
     forall s,
     strlen s = 0 -> s = EmptyString.
  Proof.
     intros.
     induction s.
     - auto.
     - simpl in H. discriminate.
  Qed.

  Lemma length_cons:
     forall c s,
     strlen (String c s) = S (strlen s).
  Proof.
     intros; simpl; auto.
  Qed.

  Lemma length_append:
     forall s1 s2,
     String.length (s1 ++ s2)%string = String.length s1 + String.length s2.
  Proof.
     intros.
     induction s1.
     - simpl; auto.
     - rewrite append_comm_cons.
       repeat rewrite length_cons.
       rewrite plus_Sn_m.
       apply eq_S.
       auto.
  Qed.

  Lemma cons_substring:
     forall n c s,
     String.substring 0 (S n) (String c s) = String c (String.substring 0 n s).
  Proof.
     intros.
     simpl.
     auto.
  Qed.

  Lemma cons_eq_cons:
     forall c s1 s2,
        String c s1 = String c s2 <-> s1 = s2.
  Proof.
     intros.
     split.
     - congruence.
     - intro. rewrite H. auto.
  Qed.

  Lemma cons_neq_cons:
     forall c s1 s2,
        String c s1 <> String c s2 <-> s1 <> s2.
  Proof.
     split; intros; congruence.
  Qed.

  (* XXX this needs a better name *)
  Lemma cons_neq_cons_2:
     forall c1 c2 s,
        String c1 s <> String c2 s <-> c1 <> c2.
  Proof.
     split; intros; congruence.
  Qed.

  (* XXX this too *)
  Lemma cons_neq_cons_3:
     forall c1 c2 s1 s2,
        String c1 s1 <> String c2 s2 <-> c1 <> c2 \/ s1 <> s2.
  Proof.
     split; intros.
     - destruct (ascii_dec c1 c2); subst.
       * rewrite cons_neq_cons in H. auto.
       * auto.
     - destruct H; congruence.
  Qed.

  Lemma cons_not_itself:
     forall c s,
        String c s = s -> False.
  Proof.
     intros.
     induction s; try discriminate.
     inversion H; subst.
     auto.
  Qed.

  Lemma cons_is_prepend:
     forall c s,
        String c s = ((String c EmptyString) ++ s)%string.
  Proof.
     intros.
     induction s; simpl; auto.
  Qed.

  Lemma append_eq_append:
     forall s1 s2 s3,
        (s1 ++ s3)%string = (s2 ++ s3)%string -> s1 = s2.
  Proof.
  (* There must be a less messy way to do this. *)
  intros.
  revert H. revert s1 s2.
  induction s3; intros.
  - repeat rewrite append_nil_r in H. auto.
  - rewrite cons_is_prepend in H.
    repeat rewrite append_assoc in H.
    apply IHs3 with
       (s1 := (s1 ++ String a "")%string) (s2 := (s2 ++ String a "")%string) in H.
    revert H; revert s2; induction s1; intros.
    * destruct s2; auto.
      simpl in H.
      destruct (ascii_dec a a0); subst.
      + assert (EmptyString = (s2 ++ String a0 EmptyString)%string) by congruence.
        destruct s2.
        -- rewrite append_nil_l in H0. discriminate.
        -- simpl in H0. discriminate.
      + congruence.
    * destruct s2; simpl in H.
      + destruct (ascii_dec a a0); subst.
        -- assert ((s1 ++ String a0 EmptyString)%string = EmptyString) by congruence.
           destruct s1.
           ** rewrite append_nil_l in H0. discriminate.
           ** simpl in H0. discriminate.
        -- congruence.
      + destruct (ascii_dec a0 a1); subst.
        -- assert ((s1 ++ String a "")%string = (s2 ++ String a "")%string) by congruence.
           apply IHs1 in H0.
           rewrite H0; auto.
        -- congruence.
  Qed.

  Lemma prepend_eq_prepend:
     forall s1 s2 s3,
        (s1 ++ s2)%string = (s1 ++ s3)%string -> s2 = s3.
  Proof.
     intros.
     induction s1.
     - repeat rewrite append_nil_l in H; auto.
     - simpl in H.
       apply cons_eq_cons in H.
       auto.
  Qed.

  Lemma null_substring:
     forall s,
     String.substring 0 0 s = EmptyString.
  Proof.
     intros.
     (* just compute doesn't work *)
     induction s; compute; auto.
  Qed.

  Lemma entire_substring:
     forall s,
     String.substring 0 (String.length s) s = s.
  Proof.
     intros.
     remember (String.length s) as n.
     revert Heqn. revert n.
     induction s; intros.
     - simpl in Heqn.
       rewrite Heqn.
       compute.
       auto.
     - assert (exists m, n = S m) as M by
         (induction n; [simpl in Heqn; omega | exists n; auto]).
       destruct M as [m M].
       rewrite M.
       rewrite cons_substring.
       rewrite cons_eq_cons.
       apply IHs.
       simpl in Heqn.
       omega.
  Qed.

  Lemma substring_cons_head:
     forall c s n,
     String.substring 0 (S n) (String c s) = String c (String.substring 0 n s).
  Proof.
     intros; simpl; auto.
  Qed.

  Lemma substring_cons_tail:
     forall c s m n,
     String.substring (S m) n (String c s) = String.substring m n s.
  Proof.
     intros; simpl; auto.
  Qed.

  (* substring of s1 ++ s2 that falls entirely within s1 *)
  Lemma substring_append_first:
     forall s1 s2 m n,
     m + n <= String.length s1 ->
     String.substring m n (s1 ++ s2)%string = String.substring m n s1.
  Proof.
     intro. (* s1 only *)
     induction s1; intros.
     - simpl in H.
       assert (m = 0) by omega.
       assert (n = 0) by omega.
       subst.
       simpl.
       rewrite null_substring.
       auto.
     - destruct (Nat.eq_dec m 0).
       * subst.
         rewrite Nat.add_0_l in H.
         destruct (Nat.eq_dec n 0).
         + subst. repeat rewrite null_substring. auto.
         + assert (exists k, n = S k) as kEq by
              (exists (Nat.pred n); rewrite Nat.succ_pred; auto).
           destruct kEq as [k kEq].
           rewrite kEq.
           rewrite append_comm_cons.
           repeat rewrite substring_cons_head.
           rewrite cons_eq_cons.
           apply IHs1.
           simpl in H.
           omega.
       * assert (exists k, m = S k) as kEq by
           (exists (Nat.pred m); rewrite Nat.succ_pred; auto).
           destruct kEq as [k kEq].
           rewrite kEq.
           rewrite append_comm_cons.
           repeat rewrite substring_cons_tail.
           apply IHs1.
           simpl in H.
           omega.
  Qed.

  (* substring of s1 ++ s2 that includes parts of both s1 and s2 *)
  Lemma substring_append_both:
     forall s1 s2 m n,
     m <= String.length s1 -> m + n >= String.length s1 ->
     String.substring m n (s1 ++ s2)%string =
        (String.substring m (String.length s1 - m) s1 ++
         String.substring 0 ((m + n) - String.length s1) s2)%string.
  Proof.
     intro; (* s1 only *)
     induction s1; intros.
     - simpl in H. assert (m = 0) by omega; subst. simpl.
       rewrite Nat.sub_0_r. auto.
     - rewrite length_cons.
       destruct m; simpl in H; simpl in H0.
       * 
         assert (exists k, n = S k) as kEq by
            (exists (Nat.pred n); rewrite Nat.succ_pred; omega).
         destruct kEq as [k kEq].
         rewrite kEq.
         specialize IHs1 with (s2 := s2) (m := 0) (n := k).
         rewrite Nat.sub_0_r in *.
         rewrite Nat.add_0_l in *.
         rewrite append_comm_cons.
         repeat rewrite substring_cons_head.
         rewrite append_comm_cons.
         rewrite cons_eq_cons.
         rewrite Nat.sub_succ.
         apply IHs1; omega.
       * rewrite plus_Sn_m.
         repeat rewrite Nat.sub_succ.
         apply IHs1; omega.
  Qed.

  (* substring of s1 ++ s2 that falls entirely within s2 *)
  Lemma substring_append_second:
     forall s1 s2 m n,
     m >= String.length s1 ->
     String.substring m n (s1 ++ s2)%string = String.substring (m - String.length s1) n s2.
  Proof.
     intro. (* s1 only *)
     induction s1; intros.
     - simpl. rewrite Nat.sub_0_r. auto.
     - rewrite append_comm_cons.
       simpl in H.
       assert (exists k, m = S k) as kEq by
          (exists (Nat.pred m); rewrite Nat.succ_pred; omega).
       destruct kEq as [k kEq].
       rewrite kEq.
       simpl.
       apply IHs1.
       omega.
  Qed.

  (* General statement of substring_append. *)
  Lemma substring_append:
     forall s1 s2 m n,
     exists m1 n1 m2 n2,
     String.substring m n (s1 ++ s2)%string =
        (String.substring m1 n1 s1 ++ String.substring m2 n2 s2)%string.
  Proof.
     intros.
     destruct (le_gt_dec m (String.length s1)).
     1: destruct (le_gt_dec (m + n) (String.length s1)).
     - (* substring_append_first *)
       exists m; exists n.
       exists 0; exists 0.
       rewrite null_substring.
       rewrite append_nil_r.
       apply substring_append_first.
       auto.
     - (* substring_append_both *)
       exists m; exists (String.length s1 - m).
       exists 0; exists ((m + n) - String.length s1).
       apply substring_append_both; omega.
     - (* substring_append_second *)
       exists 0; exists 0.
       exists (m - String.length s1); exists n.
       rewrite null_substring.
       rewrite append_nil_l.
       apply substring_append_second.
       omega.
  Qed.

  (* Specialization of substring_append_first for m = 0 *)
  Lemma substring_append_head_shorter:
     forall s1 s2 n,
     n <= String.length s1 ->
     String.substring 0 n (s1 ++ s2)%string = String.substring 0 n s1.
  Proof.
     intros.
     apply substring_append_first.
     omega.
  Qed.

  (* Specialization of substring_append_both for m = 0 *)
  Lemma substring_append_head_longer:
     forall s1 s2 n,
     n >= String.length s1 ->
     String.substring 0 n (s1 ++ s2)%string =
        (s1 ++ String.substring 0 (n - String.length s1) s2)%string.
  Proof.
     intros.
     assert (String.substring 0 n (s1 ++ s2)%string =
             (String.substring 0 (String.length s1 - 0) s1 ++
              String.substring 0 ((0 + n) - String.length s1) s2)%string) by
        (rewrite substring_append_both; try omega; auto).
     rewrite H0.
     rewrite Nat.sub_0_r.
     rewrite entire_substring.
     simpl.
     reflexivity.
  Qed.

  (* Specialization of substring_append_both for n = strlen s - m *)
  Lemma substring_append_tail_longer:
     forall s1 s2 m,
     m <= String.length s1 ->
     String.substring m (String.length (s1 ++ s2)%string - m) (s1 ++ s2)%string =
        (String.substring m (String.length s1 - m) s1 ++ s2)%string.
  Proof.
     intros.

     assert (m <= String.length (s1 ++ s2)%string) by
        (rewrite length_append; omega).
     assert (String.length (s1 ++ s2)%string >= String.length s1) by
        (rewrite length_append; omega).

     assert(String.substring m (String.length (s1 ++ s2)%string - m) (s1 ++ s2)%string =
            (String.substring m (String.length s1 - m) s1 ++
             String.substring 0 ((m + (String.length (s1 ++ s2)%string - m)) -
                                  String.length s1) s2)%string) by
        (rewrite substring_append_both; try omega; try rewrite <- le_plus_minus; auto).
     rewrite H2.

     rewrite <- le_plus_minus; auto.
     rewrite length_append.
     rewrite minus_plus.
     rewrite entire_substring.
     reflexivity.
  Qed.

  (* Specialization of substring_append_second for n = strlen s - m *)
  Lemma substring_append_tail_shorter:
     forall s1 s2 m,
     m >= String.length s1 ->
     String.substring m (String.length (s1 ++ s2)%string - m) (s1 ++ s2)%string =
        String.substring (m - String.length s1) (String.length s2 - (m - String.length s1)) s2.
  Proof.
     intros.
     rewrite substring_append_second; auto.
     rewrite length_append.
     (* ! *)
     assert (forall a b c, b >= c -> a - (b - c) = c + a - b) as Ha by (intros; omega).
     rewrite Ha; auto.
  Qed.

  Lemma split_once:
     forall s n,
     n <= String.length s ->
     ((String.substring 0 n s) ++ (String.substring n (String.length s - n) s))%string = s.
  Proof.
     intros. revert H. revert n.
     induction s; intros.
     - simpl in H. assert (n = 0) by omega. subst. simpl. auto.
     - destruct (Nat.eq_dec n 0).
       * subst. simpl. rewrite entire_substring. auto.
       * assert (n > 0) by omega.
         assert (exists m, n = S m) as mEq by
            (exists (Nat.pred n); rewrite Nat.succ_pred; auto).
         destruct mEq as [m mEq].
         rewrite mEq.
         rewrite substring_cons_head.
         rewrite substring_cons_tail.
         simpl.
         rewrite cons_eq_cons.
         apply IHs.
         simpl in H.
         omega.
  Qed.

  Function concat (xs : list string): string :=
     match xs with
     | nil => ""%string
     | (s :: more)%list => (s ++ concat more)%string
     end.

  Lemma concat_substring:
     forall k xs,
     k < List.length xs ->
     String.substring
        (natlist_sum (take k (List.map String.length xs)))
        (String.length (List.nth k xs EmptyString))
        (concat xs) =
       List.nth k xs EmptyString.
  Proof.
     intros k xs. revert k.
     induction xs; intros.
     - simpl in H. omega.
     - rewrite List.map_cons.
       rewrite concat_equation.
       destruct k.
       * rewrite take_equation.
         rewrite natlist_sum_equation.
         simpl.
         rewrite substring_append_head_shorter; try omega.
         rewrite entire_substring.
         auto.
       * rewrite take_equation.
         rewrite natlist_sum_equation.
         simpl.
         rewrite substring_append_second; try omega.
         rewrite minus_plus.
         apply IHxs.
         simpl in H.
         omega.
  Qed.

  Lemma concat_length:
     forall xs,
     length (concat xs) = natlist_sum (List.map length xs).
  Proof.
     intros.
     induction xs.
     - simpl. auto.
     - rewrite List.map_cons.
       rewrite concat_equation.
       rewrite natlist_sum_equation.
       rewrite length_append.
       rewrite IHxs.
       auto.
  Qed.

  Lemma concat_in:
     forall x xs,
     List.In x xs ->
     exists m, String.substring m (String.length x) (concat xs) = x.
  Proof.
     intros. revert H. revert x.
     induction xs; intros.
     - simpl in H. contradiction.
     - apply List.in_inv in H.
       destruct H.
       * rewrite H.
         rewrite concat_equation.
         exists 0.
         rewrite substring_append_head_shorter; try omega.
         rewrite entire_substring.
         auto.
       * apply IHxs in H.
         destruct H as [m H].
         rewrite concat_equation.
         exists (length a + m).
         rewrite substring_append_second; try omega.
         rewrite minus_plus.
         auto.
  Qed.

  Function reverse s: string :=
     match s with
     | EmptyString => EmptyString
     | String c s' => ((reverse s') ++ String c EmptyString)%string
     end.

  Lemma length_reverse:
     forall s, String.length (reverse s) = String.length s.
  Proof.
     intro.
     induction s; simpl.
     - auto.
     - rewrite length_append.
       simpl.
       rewrite Nat.add_1_r.
       apply eq_S.
       auto.
  Qed.

  Lemma reverse_cons:
     forall c s,
     reverse (String c s) = (reverse s ++ String c EmptyString)%string.
  Proof.
     intros.
     rewrite reverse_equation.
     auto.
  Qed.

  Lemma cons_reverse:
     forall c s,
     String c (reverse s) = reverse (s ++ String c EmptyString)%string.
  Proof.
     intros.
     induction s.
     - rewrite append_nil_l. simpl. auto.
     - simpl. rewrite <- IHs. rewrite append_comm_cons. auto.
  Qed.

  Lemma reverse_reverse:
     forall s,
     reverse (reverse s) = s.
  Proof.
     intro.
     induction s; simpl.
     - auto.
     - rewrite <- cons_reverse. rewrite cons_eq_cons. auto.
  Qed.

  Function StringMap f s: string :=
     match s with
     | EmptyString => EmptyString
     | String c s' => String (f c) (StringMap f s')
     end.

  Lemma map_identity:
     forall s, StringMap (fun c => c) s = s.
  Proof.
     intro.
     induction s; simpl.
     - auto.
     - rewrite cons_eq_cons. auto.
  Qed.

  Lemma map_length:
     forall s f, String.length (StringMap f s) = String.length s.
  Proof.
     intros; induction s; simpl; try rewrite IHs; auto.
  Qed.

  Lemma map_cons:
     forall c s f, StringMap f (String c s) = String (f c) (StringMap f s).
  Proof.
     intros; destruct s; simpl; auto.
  Qed.

  Lemma map_append:
     forall s1 s2 f,
     StringMap f (s1 ++ s2)%string = (StringMap f s1 ++ StringMap f s2)%string.
  Proof.
     intros.
     induction s1; simpl.
     - auto.
     - rewrite cons_eq_cons. auto.
  Qed.

  Lemma map_reverse:
     forall s f, StringMap f (reverse s) = reverse (StringMap f s).
  Proof.
     intros.
     induction s; simpl.
     - auto.
     - rewrite map_append. rewrite map_cons. rewrite IHs. simpl. auto.
  Qed.

  Inductive StringIn: ascii -> string -> Prop :=
  | string_in_cons_eq: forall c s, StringIn c (String c s)
  | string_in_cons_neq: forall c1 c2 s, StringIn c1 s -> StringIn c1 (String c2 s)
  .

  Inductive StringNotIn: ascii -> string -> Prop :=
  | string_notin_nil: forall c, StringNotIn c EmptyString
  | string_notin_cons: forall c1 c2 s,
       c1 <> c2 -> StringNotIn c1 s -> StringNotIn c1 (String c2 s)
  .

  (* this is redundant XXX *)
  Lemma StringInCons:
     forall c1 c2 s,
     StringIn c1 s -> StringIn c1 (String c2 s).
  Proof.
     intros; inversion H; subst; apply string_in_cons_neq; auto.
  Qed.

  Lemma StringInInv:
     forall c1 c2 s,
     StringIn c1 (String c2 s) -> c1 = c2 \/ StringIn c1 s.
  Proof.
     intros.
     destruct (ascii_dec c1 c2).
     - left; auto.
     - right. inversion H; subst; try contradiction; auto.
  Qed.

  Function StringNth n s def: ascii :=
     match n, s with
     | _, EmptyString => def
     | 0, String c _ => c
     | S n', String _ s' => StringNth n' s' def
     end.

  Lemma StringNthCons:
     forall n s def c,
     StringNth n s def = StringNth (S n) (String c s) def.
  Proof.
     intros. revert n; induction s; intros; destruct n; simpl; auto.
  Qed.

  Lemma StringNthOverflow:
     forall s n def, String.length s <= n -> StringNth n s def = def.
  Proof.
     intro. (* s only *)
     induction s; intros.
     - rewrite StringNth_equation. destruct n; auto.
     - destruct n; try rewrite StringNth_equation; try apply IHs; simpl in H; omega.
  Qed.

  Lemma StringNthIndep:
     forall s n def def', n < String.length s -> StringNth n s def = StringNth n s def'.
  Proof.
     intro. (* s only *)
     induction s; intros.
     - simpl in H. omega.
     - destruct n; rewrite StringNth_equation.
       * rewrite StringNth_equation; auto.
       * simpl. apply IHs. simpl in H. omega.
  Qed.

  Lemma StringNthSCons:
     forall n s def c,
     StringIn (StringNth n s def) s ->
        StringIn (StringNth (S n) (String c s) def) (String c s).
  Proof. 
     intros.
     rewrite <- StringNthCons.
     apply StringInCons.
     auto.
  Qed.

  Lemma StringNthIn:
     forall n s def, n < String.length s -> StringIn (StringNth n s def) s.
  Proof.
     intros n s. revert n.
     induction s; intros.
     - simpl in H. omega.
     - destruct n; simpl.
       * apply string_in_cons_eq.
       * apply StringInCons. apply IHs. simpl in H. omega.
  Qed.

  Lemma StringInNth:
     forall s c def,
     StringIn c s -> exists n, n < String.length s /\ StringNth n s def = c.
  Proof.
     intro. (* s only *)
     induction s; intros.
     - inversion H.
     - apply StringInInv in H.
       destruct H.
       * rewrite H. exists 0; split; simpl; try omega; auto.
       * apply IHs with (def := def) in H.
         destruct H as [n H].
         exists (S n).
         simpl.
         rewrite <- Nat.succ_lt_mono.
         auto.
  Qed.

  Lemma StringNthInOrDefault:
     forall n s def, {StringIn (StringNth n s def) s} + {StringNth n s def = def}.
  Proof.
     intros.
     destruct (le_gt_dec (String.length s) n).
     - right; apply StringNthOverflow; auto.
     - left. apply StringNthIn. omega.
  Qed.

  Lemma StringAppNth_l:
     forall s1 s2 def n,
     n < String.length s1 -> StringNth n (s1 ++ s2)%string def = StringNth n s1 def.
  Proof.
     intro. (* s1 only *)
     induction s1; intros; simpl in H.
     - omega.
     - rewrite append_comm_cons.
       destruct n; simpl.
       * auto.
       * apply IHs1. omega.
  Qed.

  Lemma StringAppNth_r:
     forall s1 s2 def n,
     n >= String.length s1 ->
        StringNth n (s1 ++ s2)%string def = StringNth (n - String.length s1) s2 def.
  Proof.
     intro. (* s1 only *)
     induction s1; intros; simpl in H.
     - simpl. rewrite Nat.sub_0_r. auto.
     - rewrite append_comm_cons.
       destruct n; simpl; try apply IHs1; omega.
  Qed.

  Lemma StringNthSplit:
     forall n s def,
     n < String.length s ->
        exists s1 s2,
        s = (s1 ++ String (StringNth n s def) s2)%string /\ String.length s1 = n.
  Proof.
     intros n s. revert n.
     induction s; intros.
     - simpl in H. omega.
     - destruct n.
       * exists EmptyString, s.
         rewrite append_nil_l.
         simpl.
         split; auto.
       * simpl.
         specialize IHs with (n := n) (def := def).
         simpl in H.
         apply lt_S_n in H.
         apply IHs in H.
         destruct H as [s1 [s2 [H1 H2]]].
         exists (String a s1), s2.
         rewrite append_comm_cons.
         rewrite cons_eq_cons.
         simpl.
         rewrite H2.
         split; auto.
  Qed.

  Lemma StringRevNth:
     forall s def n,
     n < String.length s ->
        StringNth n (reverse s) def = StringNth (String.length s - S n) s def.
  Proof.
     intro. (* s only *)
     induction s; intros; simpl in H.
     - omega.
     - simpl.
       destruct (Nat.eq_dec n (String.length s)).
       * subst.
         rewrite StringAppNth_r; rewrite length_reverse; try omega.
         rewrite Nat.sub_diag.
         simpl.
         auto.
       * simpl in H.
         assert (n < length s) by omega.
         rewrite StringAppNth_l; try rewrite length_reverse; auto.
         apply IHs with (def := def) in H0.
         rewrite H0.
         assert (S (length s - S n) = length s - n) by omega.
         rewrite <- H1.
         rewrite <- StringNthCons.
         auto.
  Qed.

  Lemma StringMapNth:
     forall f s def n,
     StringNth n (StringMap f s) (f def) = f (StringNth n s def).
  Proof.
     intros f s. revert f.
     induction s; intros; destruct n; simpl; auto.
  Qed.

  Lemma string_dec:
     forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.
  Proof.
     intro.
     induction s1; intros; destruct s2.
     - left. auto.
     - right. congruence.
     - right. congruence.
     - destruct (ascii_dec a a0); destruct IHs1 with (s2 := s2); subst.
       * left; auto.
       * right; congruence.
       * right; congruence.
       * right; congruence.
  Qed.

  (*
   * string_eq is an executable equality test for strings
   *)
  Function string_eq (s1 s2 : string): bool :=
     match s1, s2 with
     | EmptyString, EmptyString => true
     | String c1 s1', String c2 s2' => ascii_eq c1 c2 && string_eq s1' s2'
     | _, _ => false
     end.

  (* string equality is reflexive *)
  Lemma string_eq_refl:
     forall s, string_eq s s = true.
  Proof.
     intros.
     induction s; simpl; auto.
     rewrite andb_true_iff.
     rewrite ascii_eq_iff.
     auto.
  Qed.

  (* show that string_eq is equivalent to structural equality *)
  Lemma string_eq_iff:
     forall s1 s2, string_eq s1 s2 = true <-> s1 = s2.
  Proof.
     split; revert s2; induction s1; intros; destruct s2; try discriminate; auto.
     - simpl in H.
       rewrite andb_true_iff in H.
       destruct H as [H1 H2].
       apply IHs1 in H2.
       rewrite ascii_eq_iff in H1.
       subst; auto.
     - simpl.
       rewrite andb_true_iff.
       split.
       * rewrite ascii_eq_iff; congruence.
       * rewrite IHs1; auto; congruence.
  Qed.

  (* also nonequality *)
  Lemma string_neq_iff:
     forall s1 s2, string_eq s1 s2 = false <-> s1 <> s2.
  Proof.
     split; revert s2; induction s1; intros; destruct s2;
        try discriminate; try contradiction; auto.
     - simpl in H.
       rewrite andb_false_iff in H.
       destruct H.
       * rewrite ascii_neq_iff in H. congruence.
       * apply IHs1 in H. congruence.
     - simpl.
       rewrite andb_false_iff.
       apply cons_neq_cons_3 in H.
       destruct H.
       * left. rewrite ascii_neq_iff. auto.
       * right. apply IHs1. auto.
  Qed.

End StringFacts.
