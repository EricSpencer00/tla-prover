---- MODULE MCMajority ----------------------------------------------
(* TLA+ module for model checking the majority vote algorithm for all
   sequences over three elements of bounded length. *)

EXTENDS Integers

CONSTANTS A, B, C, bound

(* The bound must be a natural number (including 0). *)
ASSUME bound \in Nat

Value == {A, B, C}

(* Set of all sequences (functions from 1..n to Value) whose length n is
   between 0 and the given bound. The empty sequence is represented by the
   empty function. *)
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

\* The Majority module provides the needed definitions and actions.
INSTANCE Majority

====