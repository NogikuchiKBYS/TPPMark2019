Require Import Arith Lia.
Require Import List Bool.
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
End Clear.
