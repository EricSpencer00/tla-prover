---- MODULE MCMajority ----------------------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The bound must be a natural number (i.e., a non‑negative integer). *)
ASSUME bound \in Nat

(* The three possible vote values. *)
Value == {A, B, C}

(* All finite sequences (including the empty sequence) over Value whose
   length does not exceed the constant `bound`. *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

(* The initial state: the empty sequence, index 0, no candidate, and count 0. *)
Init ==
    /\ seq = <<>>
    /\ i   = 0
    /\ cand = Null
    /\ cnt = 0

(* Next-state relation.  The algorithm can either extend the sequence with
   a new vote (chosen nondeterministically from Value) or stay in the same
   state when the bound has been reached.  The definitions of `cand` and
   `cnt` follow the classic Boyer‑Moore majority‑vote algorithm. *)
Next ==
    \/ /\ Len(seq) < bound
       /\ \E v \in Value :
            /\ seq' = Append(seq, v)
            /\ i'   = Len(seq) + 1
            /\ IF cnt = 0
               THEN /\ cand' = v
                    /\ cnt' = 1
               ELSE IF cand = v
                    THEN /\ cand' = cand
                         /\ cnt' = cnt + 1
                    ELSE /\ cand' = cand
                         /\ cnt' = cnt - 1
    \/ /\ Len(seq) = bound
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* Safety invariant: the candidate `cand` is always a member of the set of
   possible values, or Null when no candidate has been selected. *)
CandInValue ==
    /\ cand = Null \/ cand \in Value

(* Safety invariant: the counter `cnt` is always a natural number (including 0). *)
CntNat ==
    cnt \in Nat

(* Safety invariant: the length of the current sequence never exceeds `bound`. *)
LenBounded ==
    Len(seq) <= bound

(* Safety invariant that captures the core property of the Boyer‑Moore
   algorithm: if a value occurs more than half the time in the current
   sequence, then that value must be the current candidate. *)
MajorityCorrect ==
    \A v \in Value :
        (2 * Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq))
        => cand = v

(* Full specification: the initial predicate together with the temporal
   behavior defined by the always‑eventually (stuttering) closure of `Next`. *)
Spec ==
    Init /\ [][Next]_<<seq, i, cand, cnt>>

(* The specification is the conjunction of the safety invariants. *)
Inv ==
    CandInValue /\ CntNat /\ LenBounded /\ MajorityCorrect

====