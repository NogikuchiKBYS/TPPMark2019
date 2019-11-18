# Files
## Util.v
Auxiliary Ltacs, etc.

## Value.v
Specifications of TM's symbol, or values to be written in tapes.

Requirements of the symbol type are
* Decidable equality
* Finite (* this is not actually used in the proofs *)
* Have at least two values (named zero and one)

## Tape.v
Abstract operations (Tape.ops) and specifications (Tape.specs) of cyclic tapes.

## CTM.v
Definition of the turing machine, and its predicates.

## Clearer.v
Implementation of the turing machine for Task 4

## Example.v
Define actual instances for Value and Tape classes.

## RunExample.v
Execute Task 5

## ClearerProof.v
Proofs about the turing machine defined in Clearer.v.

The final theorem in this file is the solution for Task 6.



# Tasks
## Task 1
CTM.machine

## Task 2
CTM.step

## Task 3
CTM.Halts / CTM.HaltsWith
CTM.HaltsWith takes the resulting tape as the second argument

## Task 4
Clearer.clearer

## Task 5
CTM.step_history runs the given turing machine with the given tape until it halts or maximum step passes, and return snapshots of each steps.

You can run the actual example by running run_exmaple.sh
``` sh
./run_exampe.sh
```

## Task 6
ClearerProof.clear_and_halt 

