---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS A, B, C, bound

(* Ensure the bound is a natural number (including 0) *)
ASSUME bound \in Nat

(* The set of possible vote values *)
Value == {A, B, C}

VARIABLES seq, i, cand, cnt

(* The majority algorithm as defined in the included Majority module *)
Majority == INSTANCE Majority

(* The set of all sequences over Value with length up to bound *)
BoundedSeq(S) == UNION { [j \in 1..n |-> S[j]] : n \in 0..bound }

(* Initial state: empty sequence, index 0, no candidate, count 0 *)
Init ==
    /\ seq = <<>>
    /\ i = 0
    /\ cand = CHOOSE x \in Value : FALSE \* no candidate initially
    /\ cnt = 0

(* Extend the sequence with a new element from Value, update the algorithm state *)
Next ==
    \E v \in Value :
        /\ i < bound
        /\ i' = i + 1
        /\ seq' = Append(seq, v)
        /\ IF cnt = 0
              THEN /\ cand' = v
                   /\ cnt'  = 1
              ELSE IF cand = v
                      THEN /\ cnt' = cnt + 1
                           /\ cand' = cand
                      ELSE /\ cnt' = cnt - 1
                           /\ cand' = cand

(* Safety invariant: the current candidate, if any, is always an element of Value *)
CandidateIsValue == cand \in Value

(* Type invariant: all state variables stay within their intended domains *)
TypeOK ==
    /\ i \in 0..bound
    /\ seq \in BoundedSeq(Value)
    /\ cand \in Value
    /\ cnt \in Nat

====