---- MODULE MCMajority ----------------------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The bound must be a natural number (including zero) *)
ASSUME bound \in Nat

Value == {A, B, C}

(* All sequences over Value whose length does not exceed bound.
   For each n in 0..bound we build the set of functions from 1..n to Value,
   and then take the union of those sets. *)
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(* --------------------------------------------------------------------- *)
(* Majority algorithm (Boyer-Moore)                                      *)
(* --------------------------------------------------------------------- *)

Init ==
    /\ seq \in BoundedSeq(Value)
    /\ i = 1
    /\ cand = A          \* any element of Value; A is chosen arbitrarily
    /\ cnt = 0

Next ==
    /\ i <= Len(seq)
    /\ IF cnt = 0 THEN
          /\ cand' = seq[i]
          /\ cnt' = 1
       ELSE
          /\ IF seq[i] = cand THEN cnt' = cnt + 1
                               ELSE cnt' = cnt - 1
          /\ cand' = cand
    /\ i' = i + 1
    /\ UNCHANGED <<seq>>

(* When the scan finishes, i points just past the last element. *)
Final ==
    /\ i = Len(seq) + 1
    /\ cand \in Value

(* --------------------------------------------------------------------- *)
(* Specification                                                          *)
(* --------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>> /\ Final

=============================================================================