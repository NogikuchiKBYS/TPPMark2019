Require Import Arith Lia.
Require Import List.
Require Import FunInd.

Require Import TPPMark2019.Value.
Require Import TPPMark2019.Tape.
Require Import TPPMark2019.CTM.
Require Import TPPMark2019.Util.

Set Implicit Arguments.

Section Clear.
  Variable V : Type.
  Context `{Value.class V}.
  Variable T : Type.
  Context `{Tape.class T V}.

  Inductive State :=
    Init0 | Init1 | Clear | Back | Look | Skip | Finish.
  
  Instance State_Finite : Finite.class State :=
    {|
      Finite.card := 7;
      Finite.surj n :=
        match n with
        | 0 => Init0
        | 1 => Init1
        | 2 => Clear
        | 3 => Back
        | 4 => Look
        | 5 => Skip
        | _ => Finish
        end
    |}.
  Proof.
    intros.
    destruct x;
      [exists 0 | exists 1 | exists 2 | exists 3 | exists 4 | exists 5 | exists 6]; auto with arith.
  Defined.

  Definition State_eq_dec : forall (x y : State), {x = y} + {x <> y}.
    decide equality.
  Defined.

  Definition clearer_trans (s : State) (v : V) : (V * CTM.Move * option State) :=
    match s with
    | Init0 => (Value.one, CTM.MoveR, Some Init1)
    | Init1 => (Value.one, CTM.MoveR, Some Clear)
    | Clear =>
      if Value.eq_dec v Value.one
      then (Value.zero, CTM.MoveL, Some Back)
      else (Value.zero, CTM.MoveR, Some Clear)
    | Back =>
      if Value.eq_dec v Value.zero
      then (v, CTM.MoveL, Some Back)
      else (v, CTM.MoveL, Some Look)
    | Look =>
      if Value.eq_dec v Value.zero
      then (v, CTM.MoveR, Some Finish)
      else (v, CTM.MoveR, Some Skip)
    | Skip => (v, CTM.MoveR, Some Clear)
    | Finish =>
      (Value.zero, CTM.MoveR, None)
    end.
  Functional Scheme clearer_trans_ind := Induction for clearer_trans Sort Prop.
  
  Definition clearer : CTM.Machine V State :=
    {|
      CTM.init_state := Init0;
      CTM.transition := clearer_trans;
    |}.

  Definition zero_except_ix1 (l : list V) :=
    List.nth_error l 1 = Some Value.one /\
    forall i, i < List.length l -> i <> 1 -> List.nth_error l i = Some Value.zero.

  Definition measure (tms :CTM.TMState State T) : nat :=
    Tape.size (CTM.tape tms) - 
    List.count_occ Value.eq_dec (Tape.to_list (CTM.tape tms)) Value.zero.


  Definition PreCondition (tms : CTM.TMState State T) : Prop :=
    let state := CTM.state tms in
    let tape := CTM.tape tms in
    let l := Tape.to_list tape in
    match state with
    | Some Init0 => Tape.head tape = 0
    | Some Init1 =>
      Tape.head tape = 1 /\
      List.nth_error l 0 = Some Value.one
    | Some Clear =>
      Tape.head tape <> 1 /\
      List.nth_error l 0 = Some Value.one /\
      List.nth_error l 1 = Some Value.one /\
      if Tape.head tape =? 0
      then forall i, 2 <= i < Tape.size tape -> List.nth_error l i = Some Value.zero
      else forall i, 2 <= i < Tape.head tape -> List.nth_error l i = Some Value.zero
    | Some Back =>
      Tape.head tape <> 0 /\
      ((List.nth_error l 0 = Some Value.one /\ List.nth_error l 1 = Some Value.one /\
        forall i, 2 <= i <= Tape.head tape -> List.nth_error l i = Some Value.zero) \/
      zero_except_ix1 l)
    | Some Look =>
      Tape.head tape = 0 /\
      ((List.nth_error l 0 = Some Value.one /\ List.nth_error l 1 = Some Value.one) \/
       zero_except_ix1 l)
    | Some Skip =>
      Tape.head tape = 1 /\
      List.nth_error l 0 = Some Value.one /\
      List.nth_error l 1 = Some Value.one
    | Some Finish => 
      Tape.head tape = 1 /\
      zero_except_ix1 l
    | None => 
      forall v, In v l -> v = Value.zero
    end.

  Definition PostCondition (tms tms': CTM.TMState State T) : Prop :=
    match CTM.state tms with
    | Some Init0 => True
    | Some Init1 => True
    | Some Clear =>
      match CTM.state tms' with
      | Some Back => measure tms' < measure tms
      | _ => measure tms' <= measure tms
      end
    | Some Back =>
      measure tms' = measure tms
    | Some Look =>
      measure tms' = measure tms
    | Some Skip =>
      measure tms' = measure tms
    | Some Finish => True
    | None => True
    end.

  Definition Valid (tms : CTM.TMState State T) :=
    1 < Tape.size (CTM.tape tms) /\ PreCondition tms.

  
  Hint Rewrite
       Tape.read_spec Tape.write_head
       Tape.move_right_list Tape.move_right_head
       Tape.move_left_list Tape.move_left_head
       Tape.write_size Tape.move_left_size Tape.move_right_size
       Tape.write_spec
    : tape.

  Lemma start_Valid : forall tape,
      1 < Tape.size tape -> Tape.head tape = 0 -> Valid (CTM.start clearer tape).
  Proof.
    intros.
    unfold Valid, CTM.start.
    simpl.
    auto.
  Qed.

  Lemma mod0_large : forall n m, n <> 0 -> m <> 0 -> n mod m = 0 -> m <= n.
  Proof.
    intros n m Hn Hm Hmod.
    rewrite Nat.mod_divide in Hmod; auto.
    destruct Hmod as [k ->].
    assert (k <> 0); subst; nia.
  Qed.

  Lemma mod_S_inj : forall n m x, 1 < m -> S n mod m = S x -> n mod m = x.
  Proof.
    intros n m x Hne Heq.
    replace (S n) with (1 + n) in Heq; auto.
    rewrite Nat.add_mod in Heq; auto with zarith.
    rewrite Nat.mod_1_l in *; auto.
    rewrite Nat.mod_small in Heq; auto.
    pose proof (Nat.mod_upper_bound n m) as Hub.
    cut (1 + (n mod m) <> m); try lia.
    intro Heq'.
    rewrite Heq' in *.
    rewrite Nat.mod_same in *; lia.
  Qed.

  Lemma step_Valid : forall tms, Valid tms -> Valid (CTM.step clearer tms).
  Proof.
    intros [tape state] HV.
    unfold Valid in *.
    assert (Tape.size tape <> 0) as Hnonempty. {
      simpl in *.
      auto with zarith.
    }
    split.
    {
      rewrite CTM.step_tape_size; auto with zarith.
    } {
      destruct HV as [Hsz HPC].
      simpl in *.
      destruct state eqn: Hstate; [|simpl in *; auto].
      remember (Tape.read tape) as v.
      functional induction (clearer_trans s v); unfold PreCondition in *; simpl in *.
      - repeat autorewrite with tape; try lia.
        split.
        + rewrite HPC.
          rewrite Nat.mod_1_l; auto with arith.
        + destruct_cmpbs; auto.
          congruence.
      - repeat autorewrite with tape; try lia.
        destruct HPC as [-> HPC].
        split.
        + destruct (Nat.eq_dec (Tape.size tape) 2) as [-> |].
          * rewrite Nat.mod_same; auto.
          * rewrite Nat.mod_small; lia.
        + destruct_cmpbs; try congruence.
          * split; auto. split; auto.
            intros i (Hle & Hlt).
            autorewrite with tape; try lia.
            destruct_cmpbs; subst; auto.
            -- rewrite Nat.mod_small in *; lia.
            -- assert (Tape.size tape <= 2); try lia.
               apply mod0_large; auto.
          * split; auto. split; auto.
            intros i (Hle & Hlt).
            destruct (Nat.eq_dec (Tape.size tape) 2) as [Heq |].
            -- rewrite Heq in *; simpl in *; congruence.
            -- rewrite Nat.mod_small in *; lia.
      - repeat autorewrite with tape; try lia.
        destruct HPC as (Hh & Hi0 & Hi1 & Hr).
        split.
        + destruct (Tape.head tape); auto.
          lia.
        + destruct_cmpbs; try lia.
          right.
          unfold zero_except_ix1.
          rewrite <- Tape.to_list_size.
          repeat autorewrite with tape; try lia.
          destruct_cmpbs; try lia.
          split; auto.
          intro i.
          repeat autorewrite with tape; try lia.
          destruct_cmpbs; try lia.
          left.
          split; auto.
          split; auto.
          intro i.
          destruct (Tape.head tape) eqn: Heq; try congruence.
          intro Hrange.
          repeat autorewrite with tape; auto.
          destruct_cmpbs.
      - assert (Tape.head tape <> 0). {
          intro Hhead0.
          enough (Some (Tape.read tape) = Some Value.one); try congruence.
          rewrite <- Tape.read_spec; auto.
          now rewrite Hhead0.
        }
        repeat autorewrite with tape; try lia.
        destruct HPC as (Hh & Hi0 & Hi1 &  Hr).
        split.
        + intro Heq.
          apply mod_S_inj in Heq; try lia.
          apply mod0_large in Heq; auto.
          pose proof (Tape.head_spec tape).
          lia.
        + destruct_cmpbs; try congruence.
          * split; auto. split; auto.
            intros i Hrange.
            autorewrite with tape; auto.
            destruct_cmpbs; auto.
            apply Hr; split; try tauto.
            replace (Tape.head tape) with (Tape.size tape - 1) in *; try lia.
            assert (Tape.size tape <= S (Tape.head tape)); auto using mod0_large.
            pose proof (Tape.head_spec tape).
            lia.
          * split; auto. split; auto.
            intros i Hrange.
            autorewrite with tape; auto.
            destruct_cmpbs; auto.
            apply Hr; split; try tauto.
            rewrite Nat.mod_small in Hrange; try lia.
            pose proof (Tape.head_spec tape).
            enough (Tape.head tape <> Tape.size tape - 1); try lia.
            intro Heq.
            rewrite Heq in *.
            replace (S (Tape.size tape - 1)) with (Tape.size tape) in *; try lia.
            rewrite Nat.mod_same in *; congruence.
      - rewrite Tape.move_left_list.
        rewrite !Tape.read_write_id; auto.
        repeat autorewrite with tape; auto.
        split.
        + destruct (Tape.head tape) eqn: Heq; try lia.
          intro. subst.
          apply Value.zero_ne_one.
          pose proof (Tape.read_spec tape) as Hread.
          rewrite Heq in *.
          cut_hyp Hread; auto.
          unfold zero_except_ix1 in HPC.
          intuition; congruence.
        + destruct HPC as [Hhead [(Hi0 & Hi1 & Hi) | Hze]]; auto.
          left. split; auto. split; auto.
          intro i.
          destruct (Tape.head tape) eqn: Heq; intuition.
      - assert (Tape.head tape = 1) as Hhead. {
          cut (~ 2 <= Tape.head tape); try lia.
          intro Hge2.
          destruct HPC as [Hhead [(Hi0 & Hi1 & Hi) | Hze]]; auto.
          - specialize (Hi (Tape.head tape)).
            cut_hyp Hi; auto.
            pose proof (Tape.read_spec tape) as Hread.
            cut_hyp Hread; congruence.
          - unfold zero_except_ix1 in Hze.
            destruct Hze as [_ Hi].
            specialize (Hi (Tape.head tape)).
            cut_hyp Hi.
            + pose proof (Tape.read_spec tape) as Hread.
              cut_hyp Hi; try lia.
              cut_hyp Hread; congruence.
            + rewrite <- Tape.to_list_size.
              now apply Tape.head_spec.
        }
        assert (Tape.read tape = Value.one) as Hread. {
          pose proof (Tape.read_spec tape) as Hread.
          cut_hyp Hread; auto.
          rewrite Hhead in *.
          destruct HPC as [_ [(Hi0 & Hi1 & Hi) | [Hi1 _]]]; congruence.
        }
        rewrite Tape.move_left_list, Tape.read_write_id; auto.
        repeat autorewrite with tape; auto.
        rewrite Hhead.
        tauto.
      - rewrite Tape.move_right_list, Tape.read_write_id; auto.
        repeat autorewrite with tape; try lia.
        destruct HPC as [Heq [[Hcontra] | Hze]].
        + exfalso.
          apply Value.zero_ne_one.
          pose proof (Tape.read_spec tape) as Hread.
          rewrite Heq in *.
          rewrite Hread in Hcontra; auto.
          congruence.
        + rewrite Heq in *.
          split.
          * rewrite Nat.mod_1_l; auto with arith.
          * unfold zero_except_ix1 in *.
            destruct Hze as [Hi1 Hi].
            split; auto.
      - rewrite Tape.move_right_list, Tape.read_write_id; auto.
        repeat autorewrite with tape; try lia.
        destruct HPC as [Heq Hi].
        rewrite Heq in *.
        split.
        + rewrite Nat.mod_1_l; auto with arith.
        + destruct_cmpbs; try congruence.
          destruct Hi as [Hi | Hi]; try tauto.
          destruct Hi as [Hi1 Hi].
          specialize (Hi 0).
          cut_hyp Hi.
          * cut_hyp Hi; auto.
            contradict Hi.
            pose proof (Tape.read_spec tape) as Hread.
            rewrite Heq in *.
            rewrite Hread; congruence.
          * rewrite <- Tape.to_list_size. auto with zarith.
      - rewrite Tape.move_right_list, Tape.read_write_id; auto.
        repeat autorewrite with tape; try lia.
        destruct HPC as [-> HPC].
        split.
        + destruct (Nat.eq_dec (Tape.size tape) 2) as [->|]; simpl; auto.
          rewrite Nat.mod_small; lia.
        + destruct_cmpbs; try congruence.
          * split; try tauto. split; try tauto.
            intros i (Hle & Hlt).
            autorewrite with tape; try lia.
            destruct_cmpbs; subst; auto.
            rewrite Nat.mod_small in *; lia.
          * split; try tauto. split; try tauto.
            intros i (Hle & Hlt).
            rewrite Nat.mod_small in *; try lia.
            cut (Tape.size tape <> 2); try lia.
            intro Heq. rewrite Heq in *.
            simpl in *. lia.
      - intros v (i & Hi)%In_nth_error.
        autorewrite with tape in *; auto.
        destruct_cmpbs; subst; try congruence.
        destruct HPC as [Heq Hze].
        rewrite Heq in *.
        apply proj2 in Hze.
        specialize (Hze i).
        rewrite Hze in Hi; try congruence.
        rewrite <- nth_error_Some.
        congruence.
    }
  Qed.
  
  Lemma steps_Valid : forall n tms, Valid tms -> Valid (CTM.steps n clearer tms).
  Proof.
    induction n; intros; simpl; auto using step_Valid.
  Qed.

  Lemma sub_mono : forall x y z, y < z <= x -> x - z < x - y.
  Proof.
    intros.
    lia.
  Qed.

  Lemma count_occ_length : forall A dec (xs : list A) a, count_occ dec xs a <= length xs.
  Proof.
    intros.
    induction xs; simpl; auto.
    destruct dec; subst; auto.
    lia.
  Qed.

  Lemma step_PostCondition : forall tms, Valid tms -> PostCondition tms (CTM.step clearer tms).
  Proof.
    intros [tape state] HV.
    unfold Valid in *.
    assert (Tape.size tape <> 0) as Hnonempty. {
      simpl in *.
      auto with zarith.
    }

    destruct HV as [Hsz HPC].
    simpl in *.
    destruct state eqn: Hstate; [|simpl in *; auto]; try solve [intuition].
    remember (Tape.read tape) as v.
    functional induction (clearer_trans s v); unfold PostCondition in *; simpl in *; auto; unfold measure; simpl;
      try solve [repeat autorewrite with tape; auto; rewrite Tape.read_write_id; auto].
    - repeat autorewrite with tape; auto.
      pose proof (@Tape.write_count_occ_gt T V _ Value.eq_dec tape Value.zero) as Hgt.
      cut_hyp Hgt.
      + apply sub_mono.
        split.
        * apply Hgt.
          pose proof Value.zero_ne_one; congruence.
        * rewrite <- Tape.write_size with (v := Value.zero) (tape := tape); auto.
          rewrite Tape.to_list_size.
          apply count_occ_length.
      + pose proof Value.zero_ne_one.
        congruence.
    - repeat autorewrite with tape; auto.
      pose proof (Tape.write_count_occ_ge Value.eq_dec tape Value.zero).
      lia.
  Qed.

  Lemma look_unreachable_from_finish_halt :
    forall n tms,
      CTM.state (CTM.steps n clearer tms) = Some Look ->
      match CTM.state tms with
      | Some Finish | None => False
      | _ => True
      end.
  Proof.
    induction n.
    - simpl.
      now intros tms ->.
    - intros tms.
      simpl.
      intro Hstate.
      remember (CTM.step clearer tms) as tms' eqn: Heqtms'.
      destruct tms as [tape state].
      simpl in *.
      destruct state.
      + functional induction (clearer_trans s (Tape.read tape)); auto.
        specialize (IHn tms' Hstate).
        now subst.
      + specialize (IHn tms' Hstate).
        now subst.
  Qed.


  Definition Trans1 (s : State) (s' : option State) : Prop :=
    exists v,
      let '(_, _, s'') := clearer_trans s v in
      s' = s''.

  Ltac solve_trans1 :=
    pose proof Value.zero_ne_one;
    unfold Trans1; (exists Value.zero) + (exists Value.one); simpl; try destruct Value.eq_dec; congruence.
  
  Definition Trans1_dec : forall s s', {Trans1 s s'} + {~Trans1 s s'}.
    intros.
    destruct s' as [s' |].
    - destruct s, s';
        try solve [left; solve_trans1];
        try solve[
              right; unfold Trans1; intros [v Hv]; simpl in Hv; repeat destruct Value.eq_dec in Hv; congruence
            ].
    - destruct s;
        try solve [left; solve_trans1];
        try solve[
              right; unfold Trans1; intros [v Hv]; simpl in Hv; repeat destruct Value.eq_dec in Hv; congruence
            ].
  Defined.

  Ltac solve_trans v :=
    match goal with
    | |- exists _, Trans1 _ _ /\ Some (?x) = _ /\ _ <> _ =>
      exists (Some x); split;
      [solve_trans1|]; split; try congruence
                                              (*[unfold Trans1; exists v; auto|]; split; try congruence*)
    | |- exists _, Trans1 _ _ /\ None = _ /\ _ <> _ => exists None;
                                    split; [unfold Trans1; exists v; auto|]; split; try congruence
                                                                                          
    end.
  Lemma state_escape :
    forall tms,
      Valid tms ->
      match CTM.state tms with
      | Some s => exists n s', Trans1 s s' /\ CTM.state (CTM.steps n clearer tms) = s' /\ s' <> CTM.state tms
      | _ => True
      end.
  Proof.
    pose proof Value.zero_ne_one as Hzneo.
    intros tms HValid.
    destruct tms as [tape state].
    simpl in *.
    destruct state as [state | ]; auto.
    destruct state; try solve [ exists 1; simpl; solve_trans Value.zero].
    - remember (Tape.head tape) as h eqn: Heqh.
      remember (Tape.size tape) as sz eqn: Heqsz.
      revert tape HValid Heqh Heqsz.
      induction h as [h IH] using (well_founded_induction (Nat.gt_wf sz)).
      intros tape HValid Heqh Heqsz.
      remember {| CTM.tape := tape; CTM.state := Some Clear |} as tms eqn: Heqtms.
      remember (CTM.step clearer tms) as tms' eqn: Heqtms'def.
      pose proof Heqtms'def as Heqtms'.
      rewrite Heqtms in Heqtms'.
      simpl in Heqtms'.
      destruct Value.eq_dec in Heqtms'.
      + exists 1, (Some Back).
        rewrite CTM.steps_1, <- Heqtms'def, Heqtms'.
        simpl.
        repeat split; try congruence.
        solve_trans1.
      + pose proof (step_Valid HValid) as HValid'.
        unfold Valid, PreCondition in HValid; rewrite Heqtms in HValid; simpl in *.
        destruct HValid as (Hsize & Hhead & Hi).
        destruct (Nat.eq_dec h (sz - 1)).
        * specialize (IH 0).
          exists 2.
          simpl.
          rewrite <- Heqtms'def, Heqtms'.
          simpl.
          destruct Value.eq_dec; simpl; try discriminate.
          -- exists (Some Back).
             repeat split; try congruence.
             solve_trans1.
          -- exfalso.
             remember (Tape.move_right (Tape.write Value.zero tape)) as tape' eqn: Heqtape'.
             pose proof (Value.zero_ne_one); try congruence.
             pose proof (Tape.read_spec tape') as Hread.
             rewrite <- Heqtms'def, Heqtms' in HValid'.
             unfold Valid, PreCondition in HValid'; simpl in HValid'.
             destruct HValid' as (Hsize' & Hhead' & Hi').
             cut_hyp Hread; auto with zarith.
             assert (Tape.head tape' = 0) as Heq. {
               rewrite Heqtape'.
               repeat autorewrite with tape; auto with zarith.
               rewrite <- Heqh.
               subst.
               replace (S (Tape.head tape)) with (Tape.size tape); try rewrite Nat.mod_same; auto with zarith.
             }
             rewrite Heq in *.
             destruct Hi'; congruence.
        * assert (Tape.head (CTM.tape tms') = S h) as Hheadeq. {
            rewrite Heqtms'.
            simpl.
            repeat autorewrite with tape; auto with zarith.
            rewrite Nat.mod_small; auto.
            pose proof (Tape.head_spec tape).
            lia.
          }
          specialize (IH (S h)).
          cut_hyp IH.
          -- specialize (IH (CTM.tape tms')).
             destruct IH as [k IHk]; auto.
             ++ rewrite <- Heqtms'def in HValid'.
               clear Heqtms'def.
               subst.
               simpl in *.
               assumption.
             ++ subst.
               simpl.
               destruct Value.eq_dec; try congruence.
               simpl.
               repeat autorewrite with tape; auto with zarith.
             ++ exists (S k).
               simpl.
               rewrite <- Heqtms'def. clear Heqtms'def.
               subst.
               simpl in *.
               assumption.
          -- split; auto.
             rewrite <- Hheadeq, Heqtms'.
             simpl.
             subst.
             repeat autorewrite with tape; auto with zarith.
             apply Nat.lt_le_incl.
             auto with zarith.
    - remember (Tape.head tape) as h.
      revert tape HValid Heqh.
      induction h as [|h]; intros tape HValid Heqh.
      + unfold Valid, PreCondition in HValid; simpl in HValid.
        exists 1, (Some Look).
        lia.
      + remember {| CTM.tape := tape; CTM.state := Some Back |} as tms eqn: Htms.
        remember (CTM.step clearer tms) as tms'.
        specialize (IHh (CTM.tape tms')).
        destruct h.
        * exists 1.
          simpl.
          rewrite Htms.
          simpl.
          destruct Value.eq_dec; simpl; try congruence.
          -- exfalso.
          unfold Valid, PreCondition in HValid; rewrite Htms in *; simpl in HValid.
          rewrite <- Heqh in *.
          pose proof Value.zero_ne_one.
          pose proof (Tape.read_spec tape) as Hread.
          cut_hyp Hread; auto with zarith.
          cut (nth_error (Tape.to_list tape) 1 = Some Value.one); try congruence.
          unfold zero_except_ix1 in HValid.
          intuition.
          -- exists (Some Look).
             repeat split; try congruence || solve_trans1.
        * pose proof (step_Valid HValid) as HValid'.
          rewrite <- Heqtms' in HValid'.
          rewrite Htms in *.
          simpl in Heqtms'.
          destruct Value.eq_dec.
          -- destruct IHh as [n Hn].
             ++ subst.
               now simpl.
             ++ subst.
               simpl CTM.tape.
               rewrite Tape.move_left_head.
               ** rewrite Tape.write_head.
                  now rewrite <- Heqh.
               ** unfold Valid in HValid.
                  simpl in HValid.
                  rewrite Tape.write_size; auto with zarith.
             ++ exists (S n).
               rewrite <- Htms.
               simpl CTM.steps.
               rewrite Htms.
               simpl.
               destruct Value.eq_dec; try congruence.
               subst.
               assumption.
          -- unfold Valid, PreCondition in HValid; simpl in HValid.
             cut (Tape.read tape = Value.zero); try congruence.
             pose proof (Tape.read_spec tape) as Hread.
             cut_hyp Hread; auto with zarith.
             rewrite <- Heqh in *.
             destruct HValid as (Hlen & _ & [Hi | Hi]).
             ++ destruct Hi as (_ & _ & Hi).
               specialize (Hi (S (S h))).
               cut_hyp Hi; auto with arith.
               congruence.
             ++ destruct Hi as [_ Hi].
               specialize (Hi (S (S h))).
               cut_hyp Hi; auto with arith.
               ** cut_hyp Hi; auto. congruence.
               ** rewrite <- Tape.to_list_size.
                  pose proof (Tape.head_spec tape).
                  auto with zarith.
    - exists 1.
      simpl.
      destruct Value.eq_dec; simpl.
      + exists (Some Finish).
        repeat split; congruence || solve_trans1.
      + exists (Some Skip).
        repeat split; congruence || solve_trans1.
  Qed.

  Definition StateOrder (s' s : option State) :=
    match s with
    | None => False
    | Some s =>
      match s' with
      | Some Look => False
      | _ => Trans1 s s' /\ s' <> Some s
      end
    end.
  
  Lemma StateOrder_dec : forall s' s, {StateOrder s' s} + {~StateOrder s' s}.
  Proof.
    intros.
    destruct s as [s|]; auto.
    remember (Trans1_dec s s') as dec.
    destruct s' as [s' |].
    - unfold StateOrder.
      destruct s, s'.
      all: destruct dec; try congruence.
      all: try solve [right; destruct 1; auto; congruence].
      all: left; split; try congruence; tauto.
    - simpl.
      destruct s.
      all: destruct dec; try congruence.
      all: try solve [right; destruct 1; auto; congruence].
      all: left; split; try congruence; tauto.
  Defined.
  
  Ltac solve_SO_acc :=
    match goal with
    | |- Acc StateOrder ?s =>
      let y := fresh in
      constructor;
      intro y;
      remember (StateOrder_dec y s) as dec eqn:Heqdec;
      destruct y as [y|]; try tauto;
      destruct y; simpl in Heqdec; destruct dec; try congruence
    end.


  Lemma wf_StateOrder : well_founded StateOrder.
  Proof.
    unfold well_founded.
    intros s.
    assert (Acc StateOrder None). {
      constructor.
      simpl.
      tauto.
    }
    assert (Acc StateOrder (Some Finish)). {
      solve_SO_acc.
    }
    assert (Acc StateOrder (Some Back)). {
      solve_SO_acc.
    }
    assert (Acc StateOrder (Some Clear)). {
      solve_SO_acc.
    }
    assert (Acc StateOrder (Some Skip)). {
      solve_SO_acc.
    }
    assert (Acc StateOrder (Some Look)). {
      solve_SO_acc.
    }
    assert (Acc StateOrder (Some Init1)). {
      solve_SO_acc.
    }
    assert (Acc StateOrder (Some Init0)). {
      solve_SO_acc.
    }
    destruct s as [s|]; auto.
    destruct s; auto.
  Qed.

  Lemma look_or_halt :
    forall tms, Valid tms -> exists n,
        match CTM.state (CTM.steps (S n) clearer tms) with
        | None | Some Look => True
        | _ => False
        end.
  Proof.
    intro tms.
    remember (CTM.state tms) as state eqn: Heqstate.
    revert tms Heqstate.
    induction state as [state IH] using (well_founded_induction wf_StateOrder).
    intros tms Heqstate HValid.
    destruct tms as [tape state'] eqn: Htms_def. rewrite <- Htms_def in *.
    pose proof state_escape as He.
    specialize (He tms HValid). rewrite <- Heqstate in He.
    destruct state as [state|].
    {
      destruct He as (n & s' & HT & Heq & Hneq).
      destruct n as [| n].
      - simpl in Heq.
        congruence.
      - destruct s' as [s' |].
        + destruct (State_eq_dec s' Look).
          * exists n.
            rewrite Heq.
            now subst.
          * specialize (IH (Some s')).
            cut_hyp IH.
            -- specialize (IH (CTM.steps (S n) clearer tms)).
               cut_hyp IH; auto.
               cut_hyp IH; auto using steps_Valid.
               destruct IH as [m IH].
               rewrite CTM.steps_add in IH.
               simpl in IH.
               exists (m + S n).
               assumption.
            -- unfold StateOrder.
               destruct s'; auto.
        + exists n.
          now rewrite Heq.
    } {
      exists 0.
      subst. simpl in *.
      now subst.
    }
  Qed.
  
  Lemma measure_decrease :
    forall n tms tms',
      Valid tms ->
      tms' = CTM.steps (S n) clearer tms ->
      CTM.state tms' = Some Look ->
      match CTM.state tms with
      | Some Look | Some Skip | Some Clear => measure tms' < measure tms
      | Some Back => measure tms' <= measure tms
      | _ => True
      end.
  Proof.
    induction n; intros tms tms' HValid Htms' Hstate.
    {
      pose proof (step_PostCondition HValid) as HPost.
      simpl in *.
      rewrite <- Htms' in *.
      destruct tms as [tape state].
      simpl in *.
      remember (Tape.read tape) as v eqn: Heqnv.
      destruct state as [state|]; auto.
      functional induction (clearer_trans state v);
        rewrite Htms' in *; clear tms' Htms'; simpl in *; try discriminate; auto.
      apply Nat.eq_le_incl.
      auto.
    } {
      pose proof (step_PostCondition HValid) as HPost.
      simpl in Htms'.
      simpl in *.
      specialize (IHn (CTM.step clearer tms) tms').
      repeat (cut_hyp IHn; auto using step_Valid).
      remember (CTM.step clearer tms) as tms_next eqn: Hnext in *.
      destruct tms as [tape state].
      simpl in *.
      remember (Tape.read tape) as v eqn: Heqnv.
      destruct state as [state|]; auto.
      functional induction (clearer_trans state v); auto.
      all: rewrite Hnext in IHn; simpl in IHn.
      all: try rewrite <- Hnext in IHn.
      all: rewrite Hnext in HPost; unfold PostCondition in HPost; simpl in HPost.
      all: rewrite <- Hnext in HPost.
      all: auto with zarith.
      exfalso.
      pose proof (look_unreachable_from_finish_halt (S n) tms_next) as Hur.
      cut_hyp Hur; simpl.
      - now subst.
      - congruence.
    }
  Qed.

  Lemma look_halts : forall tms,
      Valid tms ->
      CTM.state tms = Some Look ->
      CTM.Halts clearer tms.
  Proof.
    induction tms as [tms IH] using (induction_ltof1 _ measure).
    intros HValid HLook.
    destruct (look_or_halt HValid) as [n Hn].
    remember (CTM.steps (S n) clearer tms) as tms' eqn: Hdeftms'.
    specialize (IH tms').
    destruct tms' as [tape' state'] eqn: Heqtms'. rewrite <- Heqtms' in *.
    rewrite Heqtms' in Hn.
    destruct state' as [state' |].
    - destruct state'; simpl in Hn; try tauto.
      cut_hyp IH.
      + rewrite CTM.Halts_steps in *.
        destruct IH as [m Hm].
        * rewrite Hdeftms'.
          apply steps_Valid.
          assumption.
        * now subst.
        * rewrite Hdeftms', CTM.steps_add in Hm.
          eauto.
      + pose proof (@measure_decrease n tms tms' HValid Hdeftms') as Hlt.
        cut_hyp Hlt.
        * now rewrite HLook in Hlt.
        * subst; auto.
    - rewrite CTM.Halts_steps.
      exists (S n).
      now rewrite <- Hdeftms', Heqtms'.
  Qed.

  Lemma valid_clearer_halt : forall tms,
      Valid tms ->
      CTM.Halts clearer tms.
  Proof.
    intros tms HValid.
    destruct (look_or_halt HValid) as [n Hn].
    destruct (CTM.state (CTM.steps (S n) clearer tms)) as [state|] eqn: Hstate.
    - destruct state; try tauto.
      pose proof (@look_halts (CTM.steps (S n) clearer tms)) as HHalt.
      cut_hyp HHalt; auto using steps_Valid.
      rewrite CTM.Halts_steps in *.
      destruct HHalt as [m Hm]; auto.
      rewrite CTM.steps_add in Hm.
      eauto.
    - rewrite CTM.Halts_steps.
      eauto.
  Qed.

  Theorem clear_and_halt :
    forall tape : T,
      1 < Tape.size tape -> Tape.head tape = 0 ->
      exists tape', CTM.HaltWith clearer tape tape' /\ (forall v, In v (Tape.to_list tape') -> v = Value.zero).
  Proof.
    intro tape.
    intros Hsize Hhead.
    pose proof (start_Valid _ Hsize Hhead) as HValid.
    pose proof (valid_clearer_halt HValid) as HHalt.
    rewrite <- CTM.HaltWith_Halts in HHalt.
    destruct HHalt as [tape' Htape'].
    exists tape'.
    split; auto.
    intros v Hv.
    unfold CTM.HaltWith in Htape'.
    destruct Htape' as [n Hn].
    pose proof (steps_Valid n HValid) as HValid'.
    rewrite Hn in HValid'.
    unfold Valid, PreCondition in HValid'; simpl in HValid'.
    intuition.
  Qed.
End Clear.