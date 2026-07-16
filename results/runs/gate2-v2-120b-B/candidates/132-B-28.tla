------------------------- MODULE MCMajority ----------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS A, B, C, bound

(* bound is a non‑negative integer (a natural number) *)
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* The majority algorithm instance *)
INSTANCE Majority

(* Initial state: start with the empty sequence and algorithm variables
   reset to their initial values. *)
Init ==
    /\ seq = {}
    /\ i = 0
    /\ cand \in Value
    /\ cnt = 0

(* Each step appends one element from the finite set Value to the sequence,
   respecting the global bound, and advances the algorithm's state. *)
Next ==
    /\ i < bound
    /\ \E v \in Value :
        /\ seq' = seq \cup {[ i + 1 |-> v ]}
        /\ i' = i + 1
        /\ cand' = IF cnt = 0 THEN v ELSE cand
        /\ cnt' = IF cnt = 0 THEN 1
                 ELSE IF v = cand THEN cnt + 1
                 ELSE cnt - 1

(* Behaviour specification for TLC *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* Safety invariant: if the algorithm finishes (i = bound) the candidate
   must be a majority element of the constructed sequence. *)
MajorityInv ==
    (i = bound) => (Majority(seq, cand))

=============================================================================