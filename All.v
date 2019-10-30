Require Import ZArith Lia.
Require Import List.
Require Import FunInd Recdef.
Require Import Program.
Require Import Morphisms Setoid.
Set Implicit Arguments.
Arguments nth_error A l n : simpl nomatch.

Ltac cut_hyp H := lapply H; [clear H; intro H|].

Ltac destruct_cmpb_in_prop P := match P with
           | context A [?p <=? ?q]  => destruct (Nat.leb_spec p q)
           | context A [?p <? ?q]  => destruct (Nat.ltb_spec p q)
           | context A [?p =? ?q]  => destruct (Nat.eqb_spec p q)
           end.
  
Ltac destruct_cmpb :=
  match goal with
  | |- ?G => destruct_cmpb_in_prop G
  | H : ?P |- _ => destruct_cmpb_in_prop P
  end.

Ltac destruct_cmpbs := repeat destruct_cmpb; auto with zarith.

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

Module Finite.
  Class class (A : Type) :=
    {
      card : nat;
      surj : nat -> A;
      surj_spec : forall (x : A), exists i, i < card /\ surj i = x;
  
    }.
End Finite.
Module Value.
  Class class (A : Type) `{Finite.class A} :=
    {
      eq_dec : forall (x y : A), {x = y} + {x <> y};
      zero : A;
      one : A;
      zero_ne_one : zero <> one;
    }.
End Value.

Instance BoolFinite : Finite.class bool :=
  {|
    Finite.card := 2;
    Finite.surj n := n =? 1;
  |}.
Proof.
  destruct x; eauto.
Defined.

Instance BoolValue : @Value.class bool BoolFinite :=
  {|
    Value.zero := false;
    Value.one := true;
  |}.
Proof.
  - decide equality.
  - auto.
Defined.

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

Module FunTape.
  Record t (V : Type): Type :=
    {
      size: nat;
      head: nat;
      vs: nat -> V
    }.

  Arguments size {V} t.
  Arguments head {V} t.
  Arguments vs {V} t.
  
  Definition modh {V} (tape : t V) : nat := (head tape) mod (size tape).

  Definition read {V} (tape : t V): V :=
    vs tape (modh tape).
  Definition write {V} (v : V) (tape : t V) : t V :=
    {|
      size := size tape;
      head := head tape;
      vs := fun i =>
             let i := i mod size tape in
             if Nat.eq_dec i (modh tape)
             then v
             else vs tape i
    |}.
  Definition move_right {V} (tape : t V) : t V :=
    {|
      size := size tape;
      head := S (head tape) mod (size tape);
      vs := vs tape
    |}.
  Definition move_left {V} (tape : t V) : t V :=
    {|
      size := size tape;
      head :=
        match head tape with
        | 0 => size tape - 1
        | S h => h
        end;
      vs := vs tape
    |}.

  Definition from_list {V} `{Value.class V}  (l : list V) : t V :=
    {|
      size := List.length l;
      head := 0;
      vs := fun i => nth i l Value.zero
    |}.

  Definition to_list {V} `{Value.class V} (tape : t V) : list V :=
    map (vs tape) (seq 0 (size tape)).
  Transparent to_list.
End FunTape.
Hint Resolve Nat.mod_upper_bound.

Lemma map_nth_in_range {A B} (f : A -> B) xs n da db:
  n < length xs ->
  nth n (map f xs) db = f (nth n xs da).
Proof.
  intro H.
  rewrite nth_indep with (d' := f da).
  - apply map_nth.
  - now rewrite map_length.
Qed.

Lemma nth_error_nth {A} : forall (l : list A) i d, i < length l -> nth_error l i = Some (nth i l d).
Proof.
  induction l; intros.
  - inversion H.
  - destruct i; simpl in *; auto.
    apply IHl.
    auto with arith.
Qed.

Lemma nth_error_Some_nth {A} : forall (l : list A) i x d, nth_error l i = Some x -> x = nth i l d.
Proof.
  induction l; intros.
  - destruct i; discriminate.
  - destruct i; simpl in *; auto.
    congruence.
Qed.

Instance FunTape_Tape V `{Value.class V} : Tape.class (FunTape.t V) V :=
  {|
    Tape.size := FunTape.size;
    Tape.head := fun t => FunTape.head t mod FunTape.size t;
    Tape.read := FunTape.read;
    Tape.write := FunTape.write;
    Tape.move_right := FunTape.move_right;
    Tape.move_left := FunTape.move_left;
    Tape.to_list := FunTape.to_list;
  |}.
Proof.
  all: intros.
  all: simpl.
  all: unfold FunTape.to_list.
  all:auto.
  - destruct t; simpl.
    now rewrite map_length, seq_length.
  - destruct t; simpl in *.
    unfold FunTape.modh; simpl.
    apply map_nth_error.
    rewrite nth_error_nth with (d := 0).
    + rewrite seq_nth; auto.
    + rewrite seq_length; auto.
  - destruct t.
    simpl in *.
    rewrite nth_error_nth with (d := v).
    + rewrite map_nth_in_range with (da := 0).
      * destruct Nat.eq_dec; auto.
        unfold FunTape.modh in *.
        simpl in *.
        rewrite seq_nth in *; auto.
        simpl in *.
        rewrite Nat.mod_mod in *; auto.
        congruence.
      * rewrite seq_length.
        auto.
    + rewrite map_length, seq_length.
      auto.
  - destruct t. simpl in *.
    destruct (Nat.ltb_spec i size) as [Hlt | Hge].
    + rewrite !nth_error_nth with (d := v).
      * rewrite !map_nth_in_range with (da := 0); try rewrite seq_length; auto.
        rewrite seq_nth; simpl; auto.
        rewrite Nat.mod_small; auto.
        unfold FunTape.modh.
        simpl.
        destruct Nat.eq_dec; auto.
        congruence.
      * now rewrite map_length, seq_length.
      * now rewrite map_length, seq_length.
    + rewrite !(proj2 (nth_error_None _ _)); auto.
      * now rewrite map_length, seq_length.
      * now rewrite map_length, seq_length.
  - destruct t.
    simpl in *.
    rewrite Nat.mod_mod; auto.
    replace (S (head mod size)) with (1 + head mod size); auto.
    rewrite Nat.add_mod; auto.
    rewrite Nat.mod_mod; auto.
    rewrite <- Nat.add_mod; auto.
  - destruct t; auto; simpl in *.
    destruct head.
    + rewrite Nat.mod_0_l; auto.
      rewrite Nat.mod_small; auto.
      lia.
    + remember (S head mod size) as x eqn: Heqx.
      replace (S head) with (1 + head) in Heqx; auto.
      rewrite Nat.add_mod in Heqx; auto.
      destruct x.
      * destruct (Nat.eq_dec size 1); subst; auto.
        rewrite Nat.mod_1_l in *; auto with zarith.
        destruct (Nat.eq_dec (1 + head mod size) size); try lia.
        rewrite Nat.mod_small in Heqx; try lia.
        cut (head mod size < size); auto with zarith.
      * assert (1 < size) as Hgt. {
           destruct (Nat.eq_dec size 1); try lia.
           subst.
           discriminate.
        }
        rewrite Nat.mod_1_l in Heqx; auto.
        simpl in *.
        rewrite Nat.mod_small in Heqx; try lia.
        destruct (Nat.eq_dec (S (head mod size)) size) as [Heq | Hne].
        -- rewrite Heq in *.
           rewrite Nat.mod_same in Heqx; lia.
        -- cut (head mod size < size); auto with zarith.
Qed.

Inductive Move := MoveL | MoveR.

Section TM.
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
  
End TM.


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

  Definition clearer_trans (s : State) (v : V) : (V * Move * option State) :=
    match s with
    | Init0 => (Value.one, MoveR, Some Init1)
    | Init1 => (Value.one, MoveR, Some Clear)
    | Clear =>
      if Value.eq_dec v Value.one
      then (Value.zero, MoveL, Some Back)
      else (Value.zero, MoveR, Some Clear)
    | Back =>
      if Value.eq_dec v Value.zero
      then (v, MoveL, Some Back)
      else (v, MoveL, Some Look)
    | Look =>
      if Value.eq_dec v Value.zero
      then (v, MoveR, Some Finish)
      else (v, MoveR, Some Skip)
    | Skip => (v, MoveR, Some Clear)
    | Finish =>
      (Value.zero, MoveR, None)
    end.
  Functional Scheme clearer_trans_ind := Induction for clearer_trans Sort Prop.
  
  Definition clearer : Machine V State :=
    {|
      init_state := Init0;
      transition := clearer_trans;
    |}.

  Definition zero_except_ix1 (l : list V) :=
    List.nth_error l 1 = Some Value.one /\
    forall i, i < List.length l -> i <> 1 -> List.nth_error l i = Some Value.zero.

  Definition measure (tms :TMState State T) : nat :=
    Tape.size (tape tms) - 
    List.count_occ Value.eq_dec (Tape.to_list (tape tms)) Value.zero.


  Definition PreCondition (tms : TMState State T) : Prop :=
    let state := state tms in
    let tape := tape tms in
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

  Definition PostCondition (tms tms': TMState State T) : Prop :=
    match state tms with
    | Some Init0 => True
    | Some Init1 => True
    | Some Clear =>
      match state tms' with
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

  Definition Valid (tms : TMState State T) :=
    2 < Tape.size (tape tms) /\ PreCondition tms.

  
  Hint Rewrite
       Tape.read_spec Tape.write_head
       Tape.move_right_list Tape.move_right_head
       Tape.move_left_list Tape.move_left_head
       Tape.write_size Tape.move_left_size Tape.move_right_size
       Tape.write_spec
    : tape.

  Lemma start_Valid : forall tape,
      2 < Tape.size tape -> Tape.head tape = 0 -> Valid (start clearer tape).
  Proof.
    intros.
    unfold Valid, start.
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

  Lemma step_Valid : forall tms, Valid tms -> Valid (step clearer tms).
  Proof.
    intros [tape state] HV.
    unfold Valid in *.
    assert (Tape.size tape <> 0) as Hnonempty. {
      simpl in *.
      auto with zarith.
    }
    split.
    {
      rewrite step_tape_size; auto with zarith.
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
        + rewrite Nat.mod_small; auto.
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
            rewrite Nat.mod_small in *; lia.
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
        + rewrite Nat.mod_small; auto.
        + destruct_cmpbs; try congruence.
          * split; try tauto. split; try tauto.
            intros i (Hle & Hlt).
            autorewrite with tape; try lia.
            destruct_cmpbs; subst; auto.
            rewrite Nat.mod_small in *; lia.
          * split; try tauto. split; try tauto.
            intros i (Hle & Hlt).
            rewrite Nat.mod_small in *; lia.
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
  
  Lemma steps_Valid : forall n tms, Valid tms -> Valid (steps n clearer tms).
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

  Lemma step_PostCondition : forall tms, Valid tms -> PostCondition tms (step clearer tms).
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
      state (steps n clearer tms) = Some Look ->
      match state tms with
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
      remember (step clearer tms) as tms' eqn: Heqtms'.
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
      match state tms with
      | Some s => exists n s', Trans1 s s' /\ state (steps n clearer tms) = s' /\ s' <> state tms
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
      remember {| tape := tape; state := Some Clear |} as tms eqn: Heqtms.
      remember (step clearer tms) as tms' eqn: Heqtms'def.
      pose proof Heqtms'def as Heqtms'.
      rewrite Heqtms in Heqtms'.
      simpl in Heqtms'.
      destruct Value.eq_dec in Heqtms'.
      + exists 1, (Some Back).
        rewrite steps_1, <- Heqtms'def, Heqtms'.
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
        * assert (Tape.head (Top.tape tms') = S h) as Hheadeq. {
            rewrite Heqtms'.
            simpl.
            repeat autorewrite with tape; auto with zarith.
            rewrite Nat.mod_small; auto.
            pose proof (Tape.head_spec tape).
            lia.
          }
          specialize (IH (S h)).
          cut_hyp IH.
          -- specialize (IH (Top.tape tms')).
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
        intuition.
      + remember {| tape := tape; state := Some Back |} as tms eqn: Htms.
        remember (step clearer tms) as tms'.
        specialize (IHh (Top.tape tms')).
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
               simpl Top.tape.
               rewrite Tape.move_left_head.
               ** rewrite Tape.write_head.
                  now rewrite <- Heqh.
               ** unfold Valid in HValid.
                  simpl in HValid.
                  rewrite Tape.write_size; auto with zarith.
             ++ exists (S n).
               rewrite <- Htms.
               simpl steps.
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
        match state (steps (S n) clearer tms) with
        | None | Some Look => True
        | _ => False
        end.
  Proof.
    intro tms.
    remember (state tms) as state eqn: Heqstate.
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
            -- specialize (IH (steps (S n) clearer tms)).
               cut_hyp IH; auto.
               cut_hyp IH; auto using steps_Valid.
               destruct IH as [m IH].
               rewrite steps_add in IH.
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
      tms' = steps (S n) clearer tms ->
      state tms' = Some Look ->
      match state tms with
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
      specialize (IHn (step clearer tms) tms').
      repeat (cut_hyp IHn; auto using step_Valid).
      remember (step clearer tms) as tms_next eqn: Hnext in *.
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
      state tms = Some Look ->
      Halts clearer tms.
  Proof.
    induction tms as [tms IH] using (induction_ltof1 _ measure).
    intros HValid HLook.
    destruct (look_or_halt HValid) as [n Hn].
    remember (steps (S n) clearer tms) as tms' eqn: Hdeftms'.
    specialize (IH tms').
    destruct tms' as [tape' state'] eqn: Heqtms'. rewrite <- Heqtms' in *.
    rewrite Heqtms' in Hn.
    destruct state' as [state' |].
    - destruct state'; simpl in Hn; try tauto.
      cut_hyp IH.
      + rewrite Halts_steps in *.
        destruct IH as [m Hm].
        * rewrite Hdeftms'.
          apply steps_Valid.
          assumption.
        * now subst.
        * rewrite Hdeftms', steps_add in Hm.
          eauto.
      + pose proof (@measure_decrease n tms tms' HValid Hdeftms') as Hlt.
        cut_hyp Hlt.
        * now rewrite HLook in Hlt.
        * subst; auto.
    - rewrite Halts_steps.
      exists (S n).
      now rewrite <- Hdeftms', Heqtms'.
  Qed.

  Lemma valid_clearer_halt : forall tms,
      Valid tms ->
      Halts clearer tms.
  Proof.
    intros tms HValid.
    destruct (look_or_halt HValid) as [n Hn].
    destruct (state (steps (S n) clearer tms)) as [state|] eqn: Hstate.
    - destruct state; try tauto.
      pose proof (@look_halts (steps (S n) clearer tms)) as HHalt.
      cut_hyp HHalt; auto using steps_Valid.
      rewrite Halts_steps in *.
      destruct HHalt as [m Hm]; auto.
      rewrite steps_add in Hm.
      eauto.
    - rewrite Halts_steps.
      eauto.
  Qed.

  Theorem clear_and_halt :
    forall tape : T,
      2 < Tape.size tape -> Tape.head tape = 0 ->
      exists tape', HaltWith clearer tape tape' /\ (forall v, In v (Tape.to_list tape') -> v = Value.zero).
  Proof.
    intro tape.
    intros Hsize Hhead.
    pose proof (start_Valid _ Hsize Hhead) as HValid.
    pose proof (valid_clearer_halt HValid) as HHalt.
    rewrite <- HaltWith_Halts in HHalt.
    destruct HHalt as [tape' Htape'].
    exists tape'.
    split; auto.
    intros v Hv.
    unfold HaltWith in Htape'.
    destruct Htape' as [n Hn].
    pose proof (steps_Valid n HValid) as HValid'.
    rewrite Hn in HValid'.
    unfold Valid, PreCondition in HValid'; simpl in HValid'.
    intuition.
  Qed.
End Clear.