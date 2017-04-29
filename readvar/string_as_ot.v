Require Import Ascii.
Require Import String.
Require Import OrderedType OrderedTypeEx.
Require Import Compare_dec.

(*
 * Ffs. I have to write this?
 *)
Definition bool_lt a b: Prop := a = false /\ b = true.
Lemma bool_lt_trans: forall a b c, bool_lt a b -> bool_lt b c -> bool_lt a c.
Proof.
   intros.
   unfold bool_lt in *.
   destruct H; destruct H0; auto.
Qed.
Lemma bool_lt_not_eq: forall a b, bool_lt a b -> a <> b.
Proof.
   intros.
   unfold bool_lt in *.
   destruct H. subst. auto.
Qed.

Inductive ascii_lt: ascii -> ascii -> Prop :=
| ascii_lt_at_7:
    forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7,
    bool_lt a7 b7 ->
    ascii_lt (Ascii a0 a1 a2 a3 a4 a5 a6 a7) (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
| ascii_lt_at_6:
    forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7,
    a7 = b7 -> bool_lt a6 b6 ->
    ascii_lt (Ascii a0 a1 a2 a3 a4 a5 a6 a7) (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
| ascii_lt_at_5:
    forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7,
    a7 = b7 -> a6 = b6 -> bool_lt a5 b5 ->
    ascii_lt (Ascii a0 a1 a2 a3 a4 a5 a6 a7) (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
| ascii_lt_at_4:
    forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7,
    a7 = b7 -> a6 = b6 -> a5 = b5 -> bool_lt a4 b4 ->
    ascii_lt (Ascii a0 a1 a2 a3 a4 a5 a6 a7) (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
| ascii_lt_at_3:
    forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7,
    a7 = b7 -> a6 = b6 -> a5 = b5 -> a4 = b4 -> bool_lt a3 b3 ->
    ascii_lt (Ascii a0 a1 a2 a3 a4 a5 a6 a7) (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
| ascii_lt_at_2:
    forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7,
    a7 = b7 -> a6 = b6 -> a5 = b5 -> a4 = b4 -> a3 = b3 -> bool_lt a2 b2 ->
    ascii_lt (Ascii a0 a1 a2 a3 a4 a5 a6 a7) (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
| ascii_lt_at_1:
    forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7,
    a7 = b7 -> a6 = b6 -> a5 = b5 -> a4 = b4 -> a3 = b3 -> a2 = b2 -> bool_lt a1 b1 ->
    ascii_lt (Ascii a0 a1 a2 a3 a4 a5 a6 a7) (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
| ascii_lt_at_0:
    forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7,
    a7 = b7 -> a6 = b6 -> a5 = b5 -> a4 = b4 -> a3 = b3 -> a2 = b2 -> a1 = b1 ->
    bool_lt a0 b0 ->
    ascii_lt (Ascii a0 a1 a2 a3 a4 a5 a6 a7) (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
.

Lemma ascii_lt_ok_by_example:
   ascii_lt "a" "b" /\ ~(ascii_lt "a" "a") /\ ~(ascii_lt "b" "a").
Proof.
   split; try split.
   1: apply ascii_lt_at_1; unfold bool_lt; auto.
   all: intro; inversion H; unfold bool_lt in *.
   all: match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        end.
   all: discriminate.
Qed.

Lemma ascii_lt_trans: forall x y z, ascii_lt x y -> ascii_lt y z -> ascii_lt x z.
Proof.
Admitted.

Lemma ascii_lt_not_eq: forall x y, ascii_lt x y -> ~(x = y).
Proof.
   intros.
   inversion H; subst.

   1: contradict H0.
   2: contradict H1.
   3: contradict H2.
   4: contradict H3.
   5: contradict H4.
   6: contradict H5.
   7: contradict H6.
   8: contradict H7.

   (* this is really slow *)
   1: assert (a7 = b7) by congruence.
   2: assert (a6 = b6) by congruence.
   3: assert (a5 = b5) by congruence.
   4: assert (a4 = b4) by congruence.
   5: assert (a3 = b3) by congruence.
   6: assert (a2 = b2) by congruence.
   7: assert (a1 = b1) by congruence.
   8: assert (a0 = b0) by congruence.

   all: unfold bool_lt.

   1: contradict H1; destruct H1.
   2-8: contradict H0; destruct H0.
   all: subst; auto.
Qed.

Lemma ascii_lt_not_gt: forall x y, ascii_lt x y -> ascii_lt y x -> False.
Proof.
Admitted.

Lemma ascii_lt_dec: forall x y, {ascii_lt x y} + {~(ascii_lt x y)}.
Proof.
Admitted.

Function ascii_compare a b: comparison :=
   if ascii_dec a b then Eq
   else if ascii_lt_dec a b then Lt
   else Gt
.

Lemma ascii_compare_eq: forall a b, ascii_compare a b = Eq -> a = b.
Proof.
Admitted.

Lemma ascii_compare_lt: forall a b, ascii_compare a b = Lt -> ascii_lt a b.
Proof.
Admitted.

Lemma ascii_compare_gt: forall a b, ascii_compare a b = Gt -> ascii_lt b a.
Proof.
Admitted.

Module Ascii_as_OT <: UsualOrderedType.
   Definition t := ascii.
   Definition eq := @eq t.
   Definition lt := ascii_lt.

   Definition eq_refl := @eq_refl t.
   Definition eq_sym := @eq_sym t.
   Definition eq_trans := @eq_trans t.
   Definition lt_trans := ascii_lt_trans.
   Definition lt_not_eq := ascii_lt_not_eq.

   Definition compare a b : Compare lt eq a b.
   Proof.
      case_eq (ascii_compare a b); intro.
      - apply EQ. apply ascii_compare_eq. auto.
      - apply LT. apply ascii_compare_lt. auto.
      - apply GT. apply ascii_compare_gt. auto.
   Qed.
   Definition eq_dec := ascii_dec.
End Ascii_as_OT.

Inductive string_lt: string -> string -> Prop :=
| string_lt_empty: forall a c, string_lt EmptyString (String a c)
| string_lt_head: forall a b c d, ascii_lt a b ->
     string_lt (String a c) (String b d)
| string_lt_tail: forall a c d, string_lt c d ->
     string_lt (String a c) (String a d)
.

Lemma string_lt_not_eq: forall s t, string_lt s t -> s <> t.
Proof.
   intro.
   induction s; intros.
   - inversion H; subst; try discriminate.
   - destruct t; inversion H; subst; try discriminate.
     * apply ascii_lt_not_eq in H1. congruence.
     * assert (s <> t -> String a0 s <> String a0 t) as Q by congruence.
       apply Q.
       apply IHs.
       auto.
Qed.

(*
Lemma string_lt_not_gt:
   forall s t,
   string_lt s t -> string_lt t s -> False.
Proof.
   intros.
   induction s; induction t.
   - apply string_lt_not_eq in H.
     contradiction.
   - apply IHt; inversion H0.
   - apply IHs; inversion H.
   - admit.
Admitted.

Lemma string_lt_not_symm:
   forall s t,
   string_lt s t -> ~(string_lt t s).
Proof.
   unfold not.
   intros.
   apply string_lt_not_gt in H; auto.
Qed.
*)

Lemma string_lt_trans:
   forall s t u,
      string_lt s t -> string_lt t u ->
      string_lt s u.
Proof.
   intro. (*s*)
   induction s; intros.
   - destruct u.
     * inversion H0.
     * apply string_lt_empty.
   - destruct t.
     * inversion H.
     * inversion H0; subst.
       + inversion H; subst.
         -- apply ascii_lt_trans with (x := a) (y := a0) (z := b) in H2; auto.
            apply string_lt_head; auto.
         -- inversion H0; subst.
            ** apply string_lt_head; auto.
            ** apply string_lt_tail. apply IHs with (t := t); auto.
       + inversion H; subst.
         -- apply string_lt_head; auto.
         -- apply string_lt_tail. apply IHs with (t := t); auto.
Qed.

Lemma string_compare_dec:
   forall s t, {string_lt s t} + {s = t} + {string_lt t s}.
Proof.
   intro.
   induction s; intros.
   - destruct t.
     * auto.
     * left. left. apply string_lt_empty.
   - destruct t.
     * right. apply string_lt_empty.
     * remember (ascii_compare a a0) as k; symmetry in Heqk.
       destruct k.
       + apply ascii_compare_eq in Heqk; subst.
         destruct IHs with (t := t) as [IHss | IHss ];
            [ destruct IHss as [IHss | IHss] | ];
            [ left; left | left; right | right ].
         -- apply string_lt_tail; auto.
         -- subst; auto.
         -- apply string_lt_tail; auto.
       + apply ascii_compare_lt in Heqk.
         left; left.
         apply string_lt_head.
         auto.
       + apply ascii_compare_gt in Heqk.
         right.
         apply string_lt_head.
         auto.
Qed.

Module String_as_OT <: UsualOrderedType.
   Definition t := string.
   Definition eq := @eq t.
   Definition lt := string_lt.

   Definition eq_refl := @eq_refl t.
   Definition eq_sym := @eq_sym t.
   Definition eq_trans := @eq_trans t.
   Definition lt_trans := string_lt_trans.
   Definition lt_not_eq := string_lt_not_eq.

   Definition compare : forall x y : t, Compare string_lt eq x y.
   Proof.
      intros.
      destruct (string_compare_dec x y) as [H | H]; [destruct H as [ H | H ] | ];
        [ apply LT | apply EQ | apply GT ]; auto.
   Qed.

   Definition eq_dec := string_dec.
End String_as_OT.
