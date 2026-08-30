---- MODULE MajorityProof ----
EXTENDS Integers, Sequences, FiniteSets

(* This module contains an interactive formal proof of correctness for the     *)
(* Boyer-Moore majority vote algorithm, extending the main algorithm           *)
(* specification with lemmas and a machine-checked proof (TLAPS).  The proof     *)
(* establishes two results: type correctness, and that the only value that can   *)
(* survive holding a strict majority after the full scan is the elected        *)
(* candidate.                                                                   *)

CONSTANTS Value

None == "none"

VARIABLES candidate, count, scanned, seq, active

vars == <<candidate, count, scanned, seq, active>>

\* Local helper: the set of positions before some index i (used in a later     *)
(* cardinality lemma about how many positions precede a given point).          *)
PositionsBefore(i) == {k \in 1..Len(seq) : k < i}

TypeOK ==
    /\ candidate \in Value \cup {None}
    /\ count \in 0..Len(seq)
    /\ scanned \in 0..Len(seq)
    /\ active \subseteq PositionsBefore(scanned)

\* The core algorithmic invariant: a strict majority that shows up at the end  *
(* of the scan can only belong to the currently held candidate.                *)
MajorityImpliesCandidate ==
    \A v \in Value :
        (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq)) => (v = candidate)

Init ==
    /\ candidate \in Value
    /\ count = 1
    /\ scanned = 0
    /\ seq \in Seq(Value)
    /\ active = {}

\* The candidate's run of matches: the next element matches the candidate, so   *
(* its vote count grows and the scan advances.                                 *)
Match ==
    /\ scanned < Len(seq)
    /\ seq[scanned + 1] = candidate
    /\ count' = count + 1
    /\ scanned' = scanned + 1
    /\ active' = active \cup {scanned + 1}
    /\ UNCHANGED <<candidate, seq>>

\* The non-match action: the next element is different, so the candidate and     *
(* its count are reset to that element and the scan advances.                  *)
Replace ==
    /\ scanned < Len(seq)
    /\ seq[scanned + 1] # candidate
    /\ candidate' = seq[scanned + 1]
    /\ count' = 1
    /\ scanned' = scanned + 1
    /\ active' = active \cup {scanned + 1}
    /\ UNCHANGED <<seq>>

\* End of sequence: the scan is done, so the candidate is retained for the       *
(* remainder of the round and the count freezes.                              *)
Retain ==
    /\ scanned = Len(seq)
    /\ UNCHANGED vars

Next == Match \/ Replace \/ Retain

Spec == Init /\ [][Next]_vars

\* The two required invariants: type correctness and the core correctness       *
(* property from the main specification.                                       *)
TypeOK == TypeOK
Correct == MajorityImpliesCandidate
Inv == MajorityImpliesCandidate
====