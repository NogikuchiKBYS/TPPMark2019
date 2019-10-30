Require Import FunInd.
Require Import Arith.
Require Import List.
Import ListNotations.

Require Import TPPMark2019.Value.
Require Import TPPMark2019.Tape.

Set Implicit Arguments.

Module CTM.
  Inductive Move := MoveL | MoveR.
  Section CTM.
    Variable V : Type.
    Context `{Value.class V}.
    Variable State : Type.
    Context `{Finite.class State}.
    Variable T : Type.
    Context `{Tape.class T V}.
    
    Record Machine :=
      {
        init_state : State;
        transition : State -> V -> (V * Move * option State);
        
      }.

    Record TMState :=
      {
        tape : T;
        state : option State;
      }.

    Definition start (machine : Machine) (tape : T) : TMState :=
      {|
        tape := tape;
        state := Some (init_state machine);
      |}.
    

    Definition step (machine : Machine) (tms : TMState) : TMState :=
      let '{|tape:=tape; state:=state|} := tms in
      match state with
      | None => tms
      | Some state =>
        let '(v, m, s) := transition machine state (Tape.read tape) in
        let tape := Tape.write v tape in
        let tape :=
            match m with
            | MoveL => Tape.move_left tape
            | MoveR => Tape.move_right tape
            end in
        {| tape := tape; state := s |}
      end.
    Functional Scheme step_ind := Induction for step Sort Prop.

    Lemma step_tape_size : forall machine tms,
        Tape.size (tape tms) <> 0 ->
        Tape.size (tape (step machine tms)) = Tape.size (tape tms).
    Proof.
      intros.
      destruct tms as [tape state].
      simpl in *.
      destruct state; simpl; auto.
      destruct transition as [[v m] state].
      destruct m; simpl.
      - rewrite !Tape.to_list_size.
        rewrite Tape.move_left_list.
        rewrite <- !Tape.to_list_size.
        now apply Tape.write_size.
      - rewrite !Tape.to_list_size.
        rewrite Tape.move_right_list.
        rewrite <- !Tape.to_list_size.
        now apply Tape.write_size.
    Qed.
    
    
    Fixpoint steps (n : nat) (machine : Machine) (tms : TMState) : TMState :=
      match n with
      | O => tms
      | S n' => steps n' machine (step machine tms)
      end.

    Lemma steps_1 : forall machine tms, steps 1 machine tms = step machine tms.
    Proof.
      reflexivity.
    Qed.

    Lemma steps_add : forall n m machine tms,
        steps n machine (steps m machine tms) = steps (n + m) machine tms.
    Proof.
      induction m; intros.
      - rewrite Nat.add_0_r.
        reflexivity.
      - rewrite Nat.add_succ_r.
        simpl.
        auto.
    Qed.

    Definition Steps n machine tms tms' := steps n machine tms = tms'.

    Inductive Halts : Machine -> TMState -> Prop :=
    | halts_halted : forall machine tms, state tms = None -> Halts machine tms
    | halts_step : forall machine tms, Halts machine (step machine tms) -> Halts machine tms.

    Lemma Halts_steps : forall machine tms,
        Halts machine tms <->
        exists n, state (steps n machine tms) = None.
    Proof.
      split; intro HH.
      - induction HH.
        + exists 0.
          auto.
        + destruct IHHH as (n & IHHH).
          exists (S n).
          auto.
      - destruct HH as (n & HH).
        revert tms HH.
        induction n; simpl.
        + apply halts_halted. 
        + auto using halts_step.
    Qed.

    Definition HaltWith machine tape tape' :=
      exists n, steps n machine (start machine tape) = {| state := None; tape := tape' |}.

    Lemma HaltWith_Halts : forall machine tape_init, (exists tape', HaltWith machine tape_init tape') <-> Halts machine (start machine tape_init).
    Proof.
      intros machine tape_init.
      split; intro HH.
      - destruct HH as (tms & n & Heq).
        rewrite Halts_steps.
        exists n.
        rewrite Heq.
        reflexivity.
      - rewrite Halts_steps in HH.
        destruct HH as [n Heq].
        exists (tape (steps n machine (start machine tape_init))).
        unfold HaltWith.
        exists n.
        destruct (steps n machine (start machine tape_init)).
        simpl in *.
        congruence.
    Qed.


    Fixpoint steps_history n machine tms :=
      match n with
      | O => [tms]
      | S n' =>
        match state tms with
        | None => [tms]
        | _ => tms :: steps_history n' machine (step machine tms)
        end
      end.
    
  End CTM.
End CTM.
