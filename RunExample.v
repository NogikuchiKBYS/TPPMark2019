Require Import List.
Import ListNotations.

Require Import TPPMark2019.Example.
Require Import TPPMark2019.CTM.
Require Import TPPMark2019.Tape.
Require Import TPPMark2019.Clearer.

Definition bool_tape_t := ListTape.t bool.
Definition example_tape : bool_tape_t := ListTape.from_list [true; false; false; true; false; true; true].
Definition clearer := Clearer.clearer (V:= bool).
Definition history := CTM.steps_history 100 clearer (CTM.start clearer example_tape).
Definition history_list := map (fun tms =>  (Tape.to_list (CTM.tape tms), Tape.head (CTM.tape tms), CTM.state tms)) history.
Compute history_list.
