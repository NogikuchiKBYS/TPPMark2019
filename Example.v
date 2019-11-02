Require Import Arith Lia.
Require Import List.
Import ListNotations.

Require Import TPPMark2019.Value.
Require Import TPPMark2019.Tape.
Require Import TPPMark2019.CTM.
Require Import TPPMark2019.Clearer.

Set Implicit Arguments.

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
    destruct size as [|s]; try congruence.
    rewrite Nat.mod_mod; auto.
    replace (S head) with (1 + head); try reflexivity.
    rewrite Nat.add_mod; auto.
    destruct (Nat.eqb_spec (head mod S s) s) as [Heq | ].
    + destruct s; auto.
      rewrite Nat.mod_1_l, Heq; try lia.
      rewrite Nat.mod_same; auto.
    + destruct s. simpl.
      * rewrite Nat.mod_1_r in *. congruence.
      * rewrite Nat.mod_1_l; auto with zarith.
        rewrite Nat.mod_small; auto.
        pose proof (Nat.mod_upper_bound head (S (S s))).
        auto with zarith.
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
Defined.


Definition bool_funtape := FunTape.t bool.
Definition example_tape : bool_funtape := FunTape.from_list [true; false; false; true; false; true; true].
Definition clearer := Clearer.clearer (V:= bool).
Definition history := CTM.steps_history 100 clearer (CTM.start clearer example_tape).
Definition history_list := map (fun tms =>  (Tape.to_list (CTM.tape tms), Tape.head (CTM.tape tms), CTM.state tms)) history.
Compute history_list.