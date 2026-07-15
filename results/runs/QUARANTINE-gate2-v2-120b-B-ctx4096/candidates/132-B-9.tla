---- MODULE MCMajority -----------------------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

(* The bound is a natural number (including zero) that limits the length   *)
(* of the sequences we consider.                                            *)
ASSUME bound \in Nat

Value == {A, B, C}

(* The set of all sequences over the set Value whose length is between 0   *)
(* and the constant bound, inclusive.                                        *)
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(* --------------------------------------------------------------------- *)
(*  Majority algorithm (Boyer-Moore)                                      *)
(* --------------------------------------------------------------------- *)

(* Initialization of the algorithm.                                       *)
Init ==
    /\ i   = 1
    /\ cand = A               \* any element of Value; choice does not affect correctness
    /\ cnt = 0
    /\ seq \in BoundedSeq(Value)

(* One step of the algorithm.                                             *)
Next ==
    \/ /\ i <= Len(seq)
       /\ IF cnt = 0
            THEN /\ cand' = seq[i]
                 /\ cnt'  = 1
            ELSE IF seq[i] = cand
                     THEN /\ cand' = cand
                          /\ cnt'  = cnt + 1
                     ELSE /\ cand' = cand
                          /\ cnt'  = cnt - 1
       /\ i' = i + 1
       /\ UNCHANGED seq
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* --------------------------------------------------------------------- *)
(*  Derived predicates                                                     *)
(* --------------------------------------------------------------------- *)

(* The candidate after the scan (when i has stepped past the last index). *)
Candidate ==
    /\ i = Len(seq) + 1
    /\ cand \in Value

(* The candidate appears more than half the time in the sequence.          *)
IsMajority ==
    /\ Candidate
    /\ Cardinality({ j \in 1..Len(seq) : seq[j] = cand }) > Len(seq) / 2

(* --------------------------------------------------------------------- *)
(*  Specification                                                         *)
(* --------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================