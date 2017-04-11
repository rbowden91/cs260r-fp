Require Import OrderedType OrderedTypeEx DecidableType.
Require Import Program.Tactics.
Require FMapList.
Require FMapFacts.

Module WXFacts_fun (E:DecidableType) (Import Map:FMapInterface.WSfun E).
Module MapF := FMapFacts.WFacts_fun E Map.
Module MapProperties := FMapFacts.WProperties_fun E Map.
Section XMapFacts.
  Notation eq_dec := E.eq_dec.
  Context {elt: Type}.
  Implicit Types m: t elt.
  Implicit Types x y z: key.
  Implicit Types e: elt.
  Notation Partition := MapProperties.Partition.
  Notation Disjoint := MapProperties.Disjoint.
  Notation update := MapProperties.update.


  Definition Submap m1 m2 :=
    forall k e, MapsTo k e m1 -> MapsTo k e m2.

  Lemma Submap_in:
    forall {m1 m2}, Submap m1 m2 ->
                    forall k, In k m1 -> In k m2.
  Proof.
    intros m1 m2 S k I.
    destruct I.
    exists x.
    now apply S.
  Qed.


  (* Pull in the library’s facts on Disjoint and Partition. *)
  Lemma Disjoint_alt:
    forall m m', Disjoint m m' <->
                 (forall k e e', MapsTo k e m ->
                                 MapsTo k e' m' ->
                                 False).
  Proof.
    apply MapProperties.Disjoint_alt.
  Qed.

  Lemma Disjoint_empty_r:
    forall {m}, Disjoint m (Map.empty elt).
  Proof.
    intros; rewrite Disjoint_alt; intros.
    now rewrite MapF.empty_mapsto_iff in H0.
  Qed.

  Lemma Disjoint_sym:
    forall {m1 m2}, Disjoint m1 m2 -> Disjoint m2 m1.
  Proof.
    apply MapProperties.Disjoint_sym.
  Qed.

  Lemma Disjoint_in_nin:
    forall {m1 m2}, Disjoint m1 m2 ->
                    forall k, In k m1 -> ~ In k m2.
  Proof.
    intros m1 m2 D k I1 I2; apply (D k); intuition.
  Qed.

  Lemma Disjoint_mapsto_nin:
    forall {m1 m2}, Disjoint m1 m2 ->
                    forall k e, MapsTo k e m1 -> ~ In k m2.
  Proof.
    intros m1 m2 D k e M1 I2; apply (D k); intuition; now exists e.
  Qed.

  Lemma Disjoint_submap_r:
    forall m1 m2 m3, Disjoint m1 m2 ->
                     Submap m3 m2 -> Disjoint m1 m3.
  Proof.
    intros m1 m2 m3 D S k I; destruct I as [I1 I2].
    apply (Submap_in S) in I2; now apply (D k).
  Qed.


  Lemma update_in_iff:
    forall m1 m2 k, In k (update m1 m2) <-> In k m1 \/ In k m2.
  Proof.
    apply MapProperties.update_in_iff.
  Qed.

  Lemma update_mapsto_iff:
    forall m1 m2 k e, MapsTo k e (update m1 m2) <->
                      (MapsTo k e m2 \/
                       (MapsTo k e m1 /\ ~ In k m2)).
  Proof.
    apply MapProperties.update_mapsto_iff.
  Qed.

  Lemma disjoint_update_mapsto_iff:
    forall {m1 m2}, Disjoint m1 m2 ->
                    forall k e, MapsTo k e (update m1 m2) <->
                                MapsTo k e m1 \/ MapsTo k e m2.
  Proof.
    intros m1 m2 D k e; rewrite update_mapsto_iff.
    generalize (Disjoint_mapsto_nin D k e); intros G; intuition.
  Qed.

  Lemma disjoint_update_comm:
    forall {m1 m2}, Disjoint m1 m2 ->
                    Map.Equal (update m1 m2) (update m2 m1).
  Proof.
    intros m1 m2 D; rewrite MapF.Equal_mapsto_iff; intros.
    rewrite (disjoint_update_mapsto_iff D).
    rewrite (disjoint_update_mapsto_iff (Disjoint_sym D)).
    intuition.
  Qed.

  Lemma update_submap_r:
    forall m1 m2, Submap m2 (update m1 m2).
  Proof.
    intros m1 m2 k e M; apply update_mapsto_iff; now left.
  Qed.

  Lemma disjoint_update_submap_l:
    forall {m1 m2}, Disjoint m1 m2 ->
                    Submap m1 (update m1 m2).
  Proof.
    intros m1 m2 D k e M; apply disjoint_update_mapsto_iff; intuition.
  Qed.


  Lemma Partition_disjoint:
    forall {m m1 m2}, Partition m m1 m2 -> Disjoint m1 m2.
  Proof.
    unfold Partition; intuition.
  Qed.

  Lemma Partition_mapsto_iff:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k e, MapsTo k e m <->
                                  MapsTo k e m1 \/ MapsTo k e m2.
  Proof.
    unfold Partition; intuition.
  Qed.

  Lemma Partition_mapsto_l:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k e, MapsTo k e m1 -> MapsTo k e m.
  Proof.
    intros; rewrite (Partition_mapsto_iff H); intuition.
  Qed.

  Lemma Partition_mapsto_r:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k e, MapsTo k e m2 -> MapsTo k e m.
  Proof.
    intros; rewrite (Partition_mapsto_iff H); intuition.
  Qed.

  Lemma Partition_submap_l:
    forall {m m1 m2}, Partition m m1 m2 -> Submap m1 m.
  Proof.
    intros m m1 m2 P k e M; rewrite (Partition_mapsto_iff P); intuition.
  Qed.

  Lemma Partition_submap_r:
    forall {m m1 m2}, Partition m m1 m2 -> Submap m2 m.
  Proof.
    intros m m1 m2 P k e M; rewrite (Partition_mapsto_iff P); intuition.
  Qed.

  Lemma Partition_in_iff:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k, In k m <-> In k m1 \/ In k m2.
  Proof.
    intros; generalize (Partition_mapsto_iff H); split; intros.
    - destruct H1; rewrite H0 in H1; destruct or H1;
        [ left | right ]; now exists x.
    - destruct or H1; destruct H1; exists x; rewrite H0; intuition.
  Qed.

  Lemma Partition_in_l:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k, In k m1 -> In k m.
  Proof.
    intros; rewrite (Partition_in_iff H); intuition.
  Qed.

  Lemma Partition_in_r:
    forall {m m1 m2}, Partition m m1 m2 ->
                      forall k, In k m2 -> In k m.
  Proof.
    intros; rewrite (Partition_in_iff H); intuition.
  Qed.


  Lemma Partition_refl:
    forall m, Partition m m (Map.empty elt).
  Proof.
    intros; unfold Partition; split.
    - apply Disjoint_empty_r.
    - intros; rewrite MapF.empty_mapsto_iff; intuition.
  Qed.

  Lemma Partition_sym:
    forall m m1 m2, Partition m m1 m2 -> Partition m m2 m1.
  Proof.
    apply MapProperties.Partition_sym.
  Qed.

  Lemma Partition_empty_r:
    forall m m', Partition m m' (Map.empty elt) ->
                 Map.Equal m m'.
  Proof.
    intros; apply MapF.Equal_mapsto_iff; intros.
    unfold Partition in *; destruct_conjs.
    generalize (H0 k e); rewrite MapF.empty_mapsto_iff; intuition.
  Qed.

  Lemma Partition_update:
    forall m m1 m2, Partition m m1 m2 ->
                    Map.Equal m (update m1 m2).
  Proof.
    intros; unfold MapProperties.Partition in *; destruct_conjs.
    apply MapF.Equal_mapsto_iff; intros.
    rewrite H0.
    rewrite (disjoint_update_mapsto_iff H).
    intuition.
  Qed.

  Lemma disjoint_update_partition:
    forall m1 m2, Disjoint m1 m2 ->
                  Partition (update m1 m2) m1 m2.
  Proof.
    intros; unfold Partition; split; auto; intros.
    rewrite (disjoint_update_mapsto_iff H); intuition.
  Qed.

  Lemma Partition_assoc:
    forall m m1 m2 m2a m2b,
      Partition m m1 m2 ->
      Partition m2 m2a m2b ->
      Partition m (update m1 m2a) m2b.
  Proof.
    intros; unfold Partition; split.
    - unfold Disjoint; intros k I; destruct I as [Ia Ib].
      apply update_in_iff in Ia; destruct or Ia.
      + apply (Partition_disjoint H k).
        now apply (Partition_in_r H0) in Ib.
      + now apply (Partition_disjoint H0 k).
    - intros; rewrite disjoint_update_mapsto_iff.
      rewrite (Partition_mapsto_iff H).
      rewrite (Partition_mapsto_iff H0).
      split; intuition.
      apply Disjoint_submap_r with (m2:=m2).
      apply (Partition_disjoint H).
      apply (Partition_submap_l H0).
  Qed.

  Lemma Partition_add_1:
    forall m m1 m2 k v v1,
      Partition m (Map.add k v1 m1) m2 ->
      Partition (Map.add k v m) (Map.add k v m1) m2.
  Proof.
    intros m m1 m2 k v v1 P.
    unfold Partition; split.
    - intros kk I; destruct I; apply (Partition_disjoint P kk).
      rewrite MapF.add_in_iff in *; intuition.
    - intros kk e.
      rewrite MapF.add_mapsto_iff.
      rewrite (Partition_mapsto_iff P).
      repeat rewrite MapF.add_mapsto_iff.
      intuition.
      right; split; intuition.
      apply (Partition_disjoint P kk).
      rewrite H in *; rewrite MapF.add_in_iff; intuition; now exists e.
  Qed.

End XMapFacts.
End WXFacts_fun.