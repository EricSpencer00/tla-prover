---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS A, B, C, bound
ASSUME bound \in Nat \ {0}

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* Include the definitions from the Majority module *)
INSTANCE Majority

(* Initial state: empty sequence, iterator at 1, no candidate, count 0 *)
Init ==
    /\ seq = {}
    /\ i = 1
    /\ cand = {}
    /\ cnt = 0

(* Action to extend the sequence with a new element from Value *)
Add ==
    /\ i <= bound
    /\ \E v \in Value :
         /\ seq' = seq \cup {i :> v}
         /\ i' = i + 1
         /\ cand' = cand
         /\ cnt'  = cnt

(* Action to run the majority algorithm on the current sequence *)
Run ==
    /\ i > bound
    /\ \E newCand, newCnt :
         /\ Majority(seq, newCand, newCnt)
         /\ cand' = newCand
         /\ cnt'  = newCnt
         /\ UNCHANGED <<seq, i>>

Next ==
    \/ Add
    \/ Run
    \/ UNCHANGED <<seq, i, cand, cnt>>

vars == <<seq, i, cand, cnt>>

Spec == Init /\ [][Next]_vars

(* Safety invariant: if a majority element exists, it is reported as the candidate *)
MajoritySafety ==
    \A e \in Value :
        (Cardinality({j \in DOMAIN seq : seq[j] = e}) > bound / 2) => cand = e

====