------------------------- MODULE MCMajority ----------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The bound must be a natural number (i.e., a non‑negative integer). *)
ASSUME bound \in Nat

(* The set of possible values that can appear in the sequence. *)
Value == {A, B, C}

(* A bounded sequence over a set S of length at most `bound`. *)
BoundedSeq(S) == UNION { [i \in 1..n |-> v] : n \in 0..bound, v \in [1..n -> S] }

VARIABLES seq, i, cand, cnt

(* Initial state: empty sequence, index 1, no candidate, count 0. *)
Init ==
    /\ seq = << >>
    /\ i   = 1
    /\ cand = {}
    /\ cnt = 0

(* Transition that adds a new element drawn from `Value` and updates the      *)
(* Boyer–Moore majority‑vote variables.                                        *)
Add ==
    /\ i <= bound
    /\ \E v \in Value :
        /\ seq' = Append(seq, v)
        /\ i'   = i + 1
        /\ IF cnt = 0
           THEN /\ cand' = {v}
                /\ cnt'  = 1
           ELSE IF v \in cand
                THEN /\ cand' = cand
                     /\ cnt'  = cnt + 1
                ELSE /\ cand' = cand
                     /\ cnt'  = cnt - 1

(* The specification's behavior. *)
Spec == Init /\ [][Add]_<<seq, i, cand, cnt>>

(* Safety property: if the algorithm finishes (i = bound+1) and a candidate *)
(* exists, then that candidate is a majority element of the sequence.        *)
MajorityCorrect ==
    /\ i = bound + 1
    /\ cand # {}
    => Cardinality({x \in seq : x \in cand}) > Cardinality(seq) \div 2

=============================================================================