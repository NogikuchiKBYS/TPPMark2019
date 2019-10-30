Require Import List Arith Lia.
Require Import TPPMark2019.Util.

Set Implicit Arguments.

Lemma nth_error_eq {A} : forall (xs ys : list A), (forall i, nth_error xs i = nth_error ys i) <-> xs = ys.
Proof.
  intros.
  split; intros; subst; auto.
  revert ys H.
  induction xs.
  - destruct ys; auto.
    intro H.
    specialize (H 0).
    inversion H.
  - destruct ys.
    + intro H.
      specialize (H 0).
      inversion H.
    + intro H.
      f_equal.
      * specialize (H 0).
        now inversion H.
      * apply IHxs.
        intro i.
        specialize (H (S i)).
        apply H.
Qed.

Module Tape.
  Class class (A : Type) (V : Type) :=
    {
      size: A -> nat;
      head : A -> nat;
      read : A -> V;
      write : V -> A -> A;
      move_right : A -> A;
      move_left : A -> A;

      to_list : A -> list V;
      to_list_size : forall t, size t = length (to_list t);
      head_spec : forall t, size t <> 0 -> head t < size t;
      read_spec : forall t, size t <> 0 -> List.nth_error (to_list t) (head t) = Some (read t);
      write_spec_head : forall v t, size t <> 0 -> List.nth_error (to_list (write v t)) (head t) = Some v;
      write_spec_other : forall i v t,
          size t <> 0 ->
          i <> head t ->
          List.nth_error (to_list (write v t)) i = List.nth_error (to_list t) i;
      write_head : forall v t, head (write v t) = head t;
      move_right_list : forall t, to_list (move_right t) = to_list t;
      move_right_head : forall t, size t <> 0 -> head (move_right t) = S (head t) mod size t;
      move_left_list : forall t, to_list (move_left t) = to_list t;
      move_left_head : forall t, size t <> 0 -> head (move_left t) =
                            match head t with
                            | 0 => size t - 1
                            | S h => h
                            end
    }.

  Lemma write_spec : forall A V `{class A V} (tape : A) v i,
      size tape <> 0 ->
      List.nth_error (to_list (write v tape)) i =
      if i =? head tape
      then (Some v)
      else List.nth_error (to_list tape) i.
  Proof.
    intros.
    destruct (Nat.eqb_spec i (head tape)); subst.
    - apply write_spec_head; auto.
    - apply write_spec_other; auto.
  Qed.
  
  Lemma write_size : forall A V `{class A V} (tape : A) (v : V),
      size tape <> 0 -> 
      size (write v tape) = size tape.
  Proof.
    intros until v.
    intro Hnz.
    enough (forall i, Nat.ltb i (size (write v tape)) = Nat.ltb i (size tape)) as Hltbeq.
    - revert Hltbeq.
      generalize (size (write v tape)) as n.
      generalize (size tape) as m.
      intros.
      apply Nat.le_antisymm.
      + specialize (Hltbeq m).
        rewrite Nat.ltb_irrefl in Hltbeq.
        now rewrite Nat.ltb_ge in Hltbeq.
      + specialize (Hltbeq n).
        rewrite Nat.ltb_irrefl in Hltbeq.
        symmetry in Hltbeq.
        now rewrite Nat.ltb_ge in Hltbeq.
    - intro i.
      destruct (List.nth_error (to_list (write v tape)) i) eqn: Heq.
      + replace (i <? size (write v tape)) with true; symmetry; rewrite Nat.ltb_lt.
        * destruct (Nat.eq_dec i (head tape)); subst; auto using head_spec.
          rewrite to_list_size, <- nth_error_Some.
          rewrite write_spec_other in Heq; congruence.
        * rewrite to_list_size, <- nth_error_Some.
          congruence.
      + replace (i <? size (write v tape)) with false; symmetry;
          rewrite Nat.ltb_ge, to_list_size, <- nth_error_None; auto.
        destruct (Nat.eq_dec i (head tape)).
        * subst. rewrite write_spec_head in Heq; congruence.
        * rewrite write_spec_other in Heq; congruence.
  Qed.

  
  Lemma move_left_size : forall A V `{class A V} (tape : A),
      size (move_left tape) = size tape.
  Proof.
    intros.
    now rewrite !to_list_size, move_left_list.
  Qed.

  Lemma move_right_size : forall A V `{class A V} (tape : A),
      size (move_right tape) = size tape.
  Proof.
    intros.
    now rewrite !to_list_size, move_right_list.
  Qed.

  Lemma read_write_id : forall A V `{class A V} (tape  : A) (v : V),
      size tape <> 0 ->
      v = read tape ->
      to_list (write v tape) = to_list tape.
  Proof.
    intros.
    apply nth_error_eq.
    intro i.
    rewrite write_spec; auto.
    destruct_cmpbs.
    pose proof (read_spec tape) as Hread.
    subst.
    intuition.
  Qed.

  Definition replace_at {A} i (xs ys : list A) (v : A) :=
    exists a l r, length l = i /\ xs = l ++ a :: r /\ ys = l ++ v :: r.

  Lemma skipn_Sn : forall {A} i (xs : list A) (x : A), nth_error xs i = Some x -> skipn i xs = x :: skipn (S i) xs.
  Proof.
    intros A i xs x.
    revert i.
    induction xs; simpl.
    - destruct i; inversion 1.
    - destruct i; simpl in *; try congruence.
      apply IHxs.
  Qed.

  Lemma skipn_nth_error :
    forall {A} s i (xs : list A), nth_error (skipn s xs) i = nth_error xs (s + i).
  Proof.
    induction s; intros.
    - reflexivity.
    - destruct xs; simpl; auto.
      destruct i; auto.
  Qed.

  Lemma firstn_nth_error :
    forall {A} s i (xs : list A),
      nth_error (firstn s xs) i =
      if i <? s
      then nth_error xs i
      else None.
  Proof.
    induction s; intros.
    - destruct (Nat.ltb_spec i 0); simpl; try lia.
      destruct i; auto.
    - destruct i.
      + destruct_cmpbs; try lia.
        destruct xs; auto.
      + destruct xs; simpl.
        * destruct Nat.ltb; auto.
        * rewrite IHs.
          destruct_cmpbs; auto with zarith; lia.
  Qed.
             
  
  Lemma write_replace_at : forall A V `{class A V} (tape : A) (v : V),
      size tape <> 0 ->
      replace_at (Tape.head tape) (Tape.to_list tape) (Tape.to_list (Tape.write v tape)) v.
  Proof.
    intros until v.
    intro Hsnz.
    exists (read tape).
    exists (List.firstn (head tape) (to_list tape)).
    exists (List.skipn (S (head tape)) (to_list tape)).
    pose proof (head_spec tape Hsnz) as Hhead.
    pose Hsnz as Hlennz.
    rewrite to_list_size in Hhead, Hlennz.
    split; [| split].
    - rewrite firstn_length_le; auto with zarith.
    - rewrite <- (firstn_skipn (head tape) (to_list tape)) at 1.
      rewrite <- skipn_Sn; auto.
      now apply read_spec.
    - rewrite <- (firstn_skipn (head tape) (to_list (write v tape))).
      replace (firstn (head tape) (to_list tape)) with (firstn (head tape) (to_list (write v tape))).
      + replace (skipn (S (head tape)) (to_list tape)) with (skipn (S (head tape)) (to_list (write v tape))).
        * rewrite <- skipn_Sn; auto.
          now apply write_spec_head.
        * apply nth_error_eq.
          intro i.
          rewrite !skipn_nth_error.
          apply write_spec_other; auto with zarith.
      + apply nth_error_eq.
        intro i.
        rewrite !firstn_nth_error.
        destruct_cmpb; auto.
        apply write_spec_other; auto with zarith.
  Qed.

  Lemma count_occ_app : forall {A} eq_dec xs ys (v : A),
      List.count_occ eq_dec (xs ++ ys) v = List.count_occ eq_dec xs v + List.count_occ eq_dec ys v.
  Proof.
    intros.
    induction xs; simpl; auto.
    destruct eq_dec; simpl; auto.
  Qed.

  Lemma write_count_occ_ge : forall A V `{class A V} (eq_dec : forall x y, {x = y} + {x <> y}) (tape : A) (v : V),
      size tape <> 0 ->
      List.count_occ eq_dec (to_list tape) v <=
      List.count_occ eq_dec (to_list (Tape.write v tape)) v.
  Proof.
    intros.
    cut (forall i (xs ys : list V),
            replace_at i xs ys v -> List.count_occ eq_dec xs v <= List.count_occ eq_dec ys v).
    - intro H'.
      apply (H'(head tape)); auto using write_replace_at.
    - intros i xs ys Hrep.
      destruct Hrep as (a & l & r & Hlen & Hl & Hr).
      subst.
      rewrite !count_occ_app.
      simpl.
      repeat destruct eq_dec; subst; try congruence; auto with arith.
  Qed.
    
  Lemma write_count_occ_gt : forall A V `{class A V} (eq_dec : forall x y, {x = y} + {x <> y}) (tape : A) (v : V),
      size tape <> 0 ->
      read tape <> v ->
      List.count_occ eq_dec (to_list tape) v <
      List.count_occ eq_dec (to_list (write v tape)) v.
  Proof.
    intros.
    cut (forall i (xs ys : list V),
            nth_error xs i <> Some v ->
            replace_at i xs ys v -> List.count_occ eq_dec xs v < List.count_occ eq_dec ys v).
    - intro H'.
      apply (H'(head tape)); auto using write_replace_at.
      pose proof (read_spec tape) as Hread.
      cut_hyp Hread; auto.
      congruence.
    - intros i xs ys Hne Hrep.
      destruct Hrep as (a & l & r & Hlen & Hl & Hr).
      subst.
      rewrite !count_occ_app.
      simpl.
      repeat destruct eq_dec; subst; try congruence; auto with arith.
      contradict Hne.
      rewrite nth_error_app2; auto.
      rewrite Nat.sub_diag.
      reflexivity.
  Qed.
End Tape.
