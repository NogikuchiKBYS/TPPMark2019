Require Import Arith.
Require Import List.

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
Hint Resolve Nat.mod_upper_bound.
