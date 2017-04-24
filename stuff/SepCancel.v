(* Fundamentally untouched, minus the Frap import and renamings *)

(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * An entailment procedure for separation logic's assertion language
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Setoid Classes.Morphisms.
Require Import List.
Import ListNotations.
Set Implicit Arguments.

Module Type SEP.
  Parameter s_prop : Type.
  Parameter lift : Prop -> s_prop.
  Parameter star : s_prop -> s_prop -> s_prop.
  Parameter exis : forall A, (A -> s_prop) -> s_prop.

  Notation "[| P |]" := (lift P).
  Infix "*" := star.
  Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)).

  Parameters s_imp s_eq : s_prop -> s_prop -> Prop.

  Infix "===" := s_eq (no associativity, at level 70).
  Infix "===>" := s_imp (no associativity, at level 70).

  Axiom s_imp_s_eq : forall p q, p === q
                               <-> (p ===> q /\ q ===> p).
  Axiom s_imp_refl : forall p, p ===> p.
  Axiom s_imp_trans : forall p q r, p ===> q -> q ===> r -> p ===> r.

  Axiom lift_left : forall p (Q : Prop) r,
    (Q -> p ===> r)
    -> p * [| Q |] ===> r.
  Axiom lift_right : forall p q (R : Prop),
    p ===> q
    -> R
    -> p ===> q * [| R |].
  Axiom extra_lift : forall (P : Prop) p,
    P
    -> p === [| P |] * p.

  Axiom star_comm : forall p q, p * q === q * p.
  Axiom star_assoc : forall p q r, p * (q * r) === (p * q) * r.
  Axiom star_cancel : forall p1 p2 q1 q2, p1 ===> p2
    -> q1 ===> q2
    -> p1 * q1 ===> p2 * q2.

  Axiom exis_gulp : forall A p (q : A -> _),
    p * exis q === exis (fun x => p * q x).
  Axiom exis_left : forall A (p : A -> _) q,
    (forall x, p x ===> q)
    -> exis p ===> q.
  Axiom exis_right : forall A p (q : A -> _) x,
    p ===> q x
    -> p ===> exis q.
End SEP.

Module Make(Import S : SEP).
  Add Parametric Relation : s_prop s_imp
    reflexivity proved by s_imp_refl
    transitivity proved by s_imp_trans
    as s_imp_rel.

  Lemma s_eq_refl : forall p, p === p.
  Proof.
    intros; apply s_imp_s_eq; intuition (apply s_imp_refl).
  Qed.

  Lemma s_eq_sym : forall p q, p === q -> q === p.
  Proof.
    intros; apply s_imp_s_eq; apply s_imp_s_eq in H; intuition.
  Qed.

  Lemma s_eq_trans : forall p q r, p === q -> q === r -> p === r.
  Proof.
    intros; apply s_imp_s_eq; apply s_imp_s_eq in H; apply s_imp_s_eq in H0;
    intuition (eauto using s_imp_trans).
  Qed.

  Add Parametric Relation : s_prop s_eq
    reflexivity proved by s_eq_refl
    symmetry proved by s_eq_sym
    transitivity proved by s_eq_trans
    as s_eq_rel.

  Instance s_imp_s_eq_mor : Proper (s_eq ==> s_eq ==> iff) s_imp.
  Proof.
    hnf; intros; hnf; intros.
    apply s_imp_s_eq in H; apply s_imp_s_eq in H0.
    intuition eauto using s_imp_trans.
  Qed.

  Add Parametric Morphism : star
  with signature s_eq ==> s_eq ==> s_eq
  as star_sor.
  Proof.
    intros; apply s_imp_s_eq; apply s_imp_s_eq in H; apply s_imp_s_eq in H0;
    intuition (auto using star_cancel).
  Qed.

  Add Parametric Morphism : star
  with signature s_imp ==> s_imp ==> s_imp
  as star_mor'.
  Proof.
    auto using star_cancel.
  Qed.

  Instance exis_iff_morphism (A : Type) :
    Proper (pointwise_relation A s_eq ==> s_eq) (@exis A).
  Proof.
    hnf; intros; apply s_imp_s_eq; intuition.
    hnf in H.
    apply exis_left; intro.
    eapply exis_right.
    assert (x x0 === y x0) by eauto.
    apply s_imp_s_eq in H0; intuition eauto.
    hnf in H.
    apply exis_left; intro.
    eapply exis_right.
    assert (x x0 === y x0) by eauto.
    apply s_imp_s_eq in H0; intuition eauto.
  Qed.

  Instance exis_imp_morphism (A : Type) :
    Proper (pointwise_relation A s_imp ==> s_imp) (@exis A).
  Proof.
    hnf; intros.
    apply exis_left; intro.
    eapply exis_right.
    unfold pointwise_relation in H.
    eauto.
  Qed.

  Lemma star_combine_lift1 : forall P Q, [| P |] * [| Q |] ===> [| P /\ Q |].
  Proof.
    intros.
    apply lift_left; intro.
    rewrite extra_lift with (P := True); auto.
    apply lift_left; intro.
    rewrite extra_lift with (P := True) (p := [| P /\ Q |]); auto.
    apply lift_right.
    reflexivity.
    tauto.
  Qed.

  Lemma star_combine_lift2 : forall P Q, [| P /\ Q |] ===> [| P |] * [| Q |].
  Proof.
    intros.
    rewrite extra_lift with (P := True); auto.
    apply lift_left; intro.
    apply lift_right; try tauto.
    rewrite extra_lift with (P := True) (p := [| P |]); auto.
    apply lift_right; try tauto.
    reflexivity.
  Qed.

  Lemma star_combine_lift : forall P Q, [| P |] * [| Q |] === [| P /\ Q |].
  Proof.
    intros.
    apply s_imp_s_eq; auto using star_combine_lift1, star_combine_lift2.
  Qed.

  Lemma star_comm_lift : forall P q, [| P |] * q === q * [| P |].
  Proof.
    intros; apply star_comm.
  Qed.

  Lemma star_assoc_lift : forall p Q r,
    (p * [| Q |]) * r === p * r * [| Q |].
  Proof.
    intros.
    rewrite <- star_assoc.
    rewrite (star_comm [| Q |]).
    apply star_assoc.
  Qed.

  Lemma star_comm_exis : forall A (p : A -> _) q, exis p * q === q * exis p.
  Proof.
    intros; apply star_comm.
  Qed.

  Ltac lift :=
    intros; apply s_imp_s_eq; split;
    repeat (apply lift_left; intro);
    repeat (apply lift_right; intuition).

  Lemma lift_combine : forall p Q R,
    p * [| Q |] * [| R |] === p * [| Q /\ R |].
  Proof.
    intros; apply s_imp_s_eq; split;
    repeat (apply lift_left; intro);
    repeat (apply lift_right; intuition).
  Qed.

  Lemma lift1_left : forall (P : Prop) q,
    (P -> [| True |] ===> q)
    -> [| P |] ===> q.
  Proof.
    intros.
    rewrite (@extra_lift True [| P |]); auto.
    apply lift_left; auto.
  Qed.

  Lemma lift1_right : forall p (Q : Prop),
    Q
    -> p ===> [| True |]
    -> p ===> [| Q |].
  Proof.
    intros.
    rewrite (@extra_lift True [| Q |]); auto.
    apply lift_right; auto.
  Qed.

  Ltac normalize0 :=
    match goal with
    | [ |- context[star ?p (exis ?q)] ] => rewrite (exis_gulp p q)
    | [ |- context[star (star ?p (lift ?q)) (lift ?r)] ] => rewrite (lift_combine p q r)
    | [ |- context[star ?p (star ?q ?r)] ] => rewrite (star_assoc p q r)
    | [ |- context[star (lift ?p) (lift ?q)] ] => rewrite (star_combine_lift p q)
    | [ |- context[star (lift ?p) ?q ] ] => rewrite (star_comm_lift p q)
    | [ |- context[star (star ?p (lift ?q)) ?r] ] => rewrite (star_assoc_lift p q r)
    | [ |- context[star (exis ?p) ?q] ] => rewrite (star_comm_exis p q)
    end.

  Ltac normalizeL :=
    (apply exis_left || apply lift_left; intro; try congruence)
    || match goal with
         | [ |- lift ?P ===> _ ] =>
           match P with
             | True => fail 1
             | _ => apply lift1_left; intro; try congruence
           end
       end.

  Ltac normalizeR :=
    match goal with
    | [ |- _ ===> exis _ ] => eapply exis_right
    | [ |- _ ===> _ * lift _ ] => apply lift_right
    | [ |- _ ===> lift ?Q ] =>
      match Q with
      | True => fail 1
      | _ => apply lift1_right
      end
    end.

  Ltac normalize1 := normalize0 || normalizeL || normalizeR.

  Lemma lift_uncombine : forall p P Q,
    p * [| P /\ Q |] === p * [| P |] * [| Q |].
  Proof.
    lift.
  Qed.
  
  Ltac normalize2 :=
    match goal with
    | [ |- context[star ?p lift (?P /\ ?Q)] ] => rewrite (lift_uncombine p P Q)
    | [ |- context[star ?p (star ?q ?r)] ] => rewrite (star_assoc p q r)
    end.

  Ltac normalizeLeft :=
    let s := fresh "s" in intro s;
    let rhs := fresh "rhs" in
    match goal with
      | [ |- _ ===> ?Q ] => set (rhs := Q)
    end;
    simpl; intros; repeat (normalize0 || normalizeL);
    repeat match goal with
             | [ H : ex _ |- _ ===> _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : _ = _ |- _ ] => rewrite H
           end; subst rhs.
                                                      
  Ltac normalize :=
    simpl; intros; repeat normalize1; repeat normalize2;
    repeat (match goal with
              | [ H : ex _ |- _ ===> _ ] => destruct H
            end; intuition idtac).

  Ltac forAllAtoms p k :=
    match p with
      | ?q * ?r => forAllAtoms q k || forAllAtoms r k
      | _ => k p
    end.

  Lemma stb1 : forall p q r,
    (q * p) * r === q * r * p.
  Proof.
    intros; rewrite <- star_assoc; rewrite (star_comm p r); apply star_assoc.
  Qed.

  Ltac sendToBack part := repeat (rewrite (stb1 part) || rewrite (star_comm part)).

  Theorem star_cancel' : forall p1 p2 q, p1 ===> p2
    -> p1 * q ===> p2 * q.
  Proof.
    intros; apply star_cancel; auto using s_imp_refl.
  Qed.

  Theorem star_cancel'' : forall p q, lift True ===> q
    -> p ===> p * q.
  Proof.
    intros.
    eapply s_imp_trans.
    rewrite extra_lift with (P := True); auto.
    instantiate (1 := p * q).
    rewrite star_comm.
    apply star_cancel; auto.
    reflexivity.
    reflexivity.
  Qed.

  Module Type TRY_ME_FIRST.
    Parameter try_me_first : s_prop -> Prop.

    Axiom try_me_first_easy : forall p, try_me_first p.
  End TRY_ME_FIRST.

  Module TMF : TRY_ME_FIRST.
    Definition try_me_first (_ : s_prop) := True.

    Theorem try_me_first_easy : forall p, try_me_first p.
    Proof.
      constructor.
    Qed.
  End TMF.

  Import TMF.
  Export TMF.

  Ltac cancel1 :=
    match goal with
      | [ |- ?p ===> ?q ] =>
        (is_var q; fail 2)
        || forAllAtoms p ltac:(fun p0 =>
          (let H := fresh in assert (H : try_me_first p0) by eauto; clear H);
                                 sendToBack p0;
          forAllAtoms q ltac:(fun q0 =>
            (let H := fresh in assert (H : try_me_first q0) by eauto; clear H);
            sendToBack q0;
            apply star_cancel'))
    end ||
    match goal with
      | [ |- _ ===> ?Q ] =>
        match Q with
        | _ => is_evar Q; fail 1
        | ?Q _ => is_evar Q; fail 1
        | _ => apply s_imp_refl
        end
      | [ |- ?p ===> ?q ] =>
        (is_var q; fail 2)
        || forAllAtoms p ltac:(fun p0 =>
          sendToBack p0;
          forAllAtoms q ltac:(fun q0 =>
            sendToBack q0;
            apply star_cancel'))
      | _ => progress autorewrite with core
    end.

  Ltac hide_evars :=
    repeat match goal with
           | [ |- ?P ===> _ ] => is_evar P; set P
           | [ |- _ ===> ?Q ] => is_evar Q; set Q
           | [ |- context[star ?P _] ] => is_evar P; set P
           | [ |- context[star _ ?Q] ] => is_evar Q; set Q
           | [ |- _ ===> exists v, _ * ?R v ] => is_evar R; set R
           end.

  Ltac restore_evars :=
    repeat match goal with
           | [ x := _ |- _ ] => subst x
           end.

  Fixpoint flattenAnds (Ps : list Prop) : Prop :=
    match Ps with
    | nil => True
    | [P] => P
    | P :: Ps => P /\ flattenAnds Ps
    end.

  Ltac allPuresFrom k :=
    match goal with
    | [ H : ?P |- _ ] =>
      match type of P with
      | Prop => generalize dependent H; allPuresFrom ltac:(fun Ps => k (P :: Ps))
      end
    | _ => intros; k (@nil Prop)
    end.

  Ltac whichToQuantify skip foundAlready k :=
    match goal with
    | [ x : ?T |- _ ] =>
      match type of T with
      | Prop => fail 1
      | _ =>
        match skip with
        | context[x] => fail 1
        | _ =>
          match foundAlready with
          | context[x] => fail 1
          | _ => (instantiate (1 := lift (x = x)); fail 2)
                 || (instantiate (1 := fun _ => lift (x = x)); fail 2)
                 || (whichToQuantify skip (x, foundAlready) k)
          end
        end
      end
    | _ => k foundAlready
    end.

  Ltac quantifyOverThem vars e k :=
    match vars with
    | tt => k e
    | (?x, ?vars') =>
      match e with
      | context[x] =>
        match eval pattern x in e with
        | ?f _ => quantifyOverThem vars' (exis f) k
        end
      | _ => quantifyOverThem vars' e k
      end
    end.

  Ltac addQuantifiers P k :=
    whichToQuantify tt tt ltac:(fun vars =>
        quantifyOverThem vars P k).

  Ltac addQuantifiersSkipping x P k :=
    whichToQuantify x tt ltac:(fun vars =>
        quantifyOverThem vars P k).

  Ltac basic_cancel :=
    normalize; repeat cancel1; repeat match goal with
                                      | [ H : _ /\ _ |- _ ] => destruct H
                                      | [ |- _ /\ _ ] => split
                                      end; eassumption || apply I.

  Ltac beautify := repeat match goal with
                          | [ H : True |- _ ] => clear H
                          | [ H : ?P, H' : ?P |- _ ] =>
                            match type of P with
                            | Prop => clear H'
                            end
                          | [ H : _ /\ _ |- _ ] => destruct H
                          end.

  Ltac cancel := hide_evars; normalize; repeat cancel1; restore_evars; beautify;
                 try match goal with
                     | [ |- _ ===> ?p * ?q ] =>
                       ((is_evar p; fail 1) || apply star_cancel'')
                       || ((is_evar q; fail 1) || (rewrite (star_comm p q); apply star_cancel''))
                     end;
                 try match goal with
                     | [ |- ?P ===> _ ] => sendToBack P;
                       match goal with
                       | [ |- ?P ===> ?Q * ?P ] => is_evar Q;
                         rewrite (star_comm Q P);
                         allPuresFrom ltac:(fun Ps =>
                                              match Ps with
                                              | nil => instantiate (1 := lift True)
                                              | _ =>
                                                let Ps' := eval s_impl in (flattenAnds Ps) in
                                                addQuantifiers (lift Ps') ltac:(fun e => instantiate (1 := e))
                                              end;
                                              basic_cancel)
                       end
                     | [ |- ?P ===> ?Q ] => is_evar Q;
                       allPuresFrom ltac:(fun Ps =>
                                            match Ps with
                                            | nil => reflexivity
                                            | _ =>
                                              let Ps' := eval s_impl in (flattenAnds Ps) in
                                              addQuantifiers (star P (lift Ps')) ltac:(fun e => instantiate (1 := e));
                                              basic_cancel
                                            end)
                     | [ |- ?P ===> ?Q ?x ] => is_evar Q;
                        allPuresFrom ltac:(fun Ps =>
                                             match Ps with
                                             | nil => reflexivity
                                             | _ =>
                                               let Ps' := eval s_impl in (flattenAnds Ps) in
                                               addQuantifiersSkipping x (star P (lift Ps'))
                                                 ltac:(fun e => match eval pattern x in e with
                                                                | ?f _ => instantiate (1 := f)
                                                                end);
                                               basic_cancel
                                             end)
                     | [ |- _ ===> _ ] => intuition (try congruence)
                     end; intuition idtac; beautify.
End Make.
