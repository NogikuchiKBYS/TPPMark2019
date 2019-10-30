Set Implicit Arguments.

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
