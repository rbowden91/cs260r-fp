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
