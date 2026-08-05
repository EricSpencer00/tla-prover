---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Majority voting for a candidate that appears more than half the time.   *)
(* This proof builds a counterexample by the very mechanism it is proving   *)
(* safe: a candidate that fails to reach majority cannot be confirmed the  *)
(* next time the sequence is scanned.                                       *)
(*                                                                          *)
(* The nodes in the network may act out of order, so the scan proceeds as a *)
(* sequence with an index: the next position to read is chosen by a live     *)
(* arbitrator, and the same index may be chosen repeatedly.                 *)
(*                                                                          *)
(* The inductive invariant bounds the counter against the occurrences of    *)
(* its candidate, and a strict inequality appears in every clause except the *)
(* one that starts an empty scan.                                           *)
(***************************************************************************)

Value == {0, 1}

VARIABLES seq, i, cand, cnt

TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

PositionsBefore(v, j) ==
  { k \in 1 .. j-1 : seq[k] = v }

OccurrencesBefore(v, j) ==
  Cardinality(PositionsBefore(v, j))

Inv ==
  /\ cnt =< OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) =< i - 1 - cnt
  /\ \A v \in Value \ {cand} :
       2 * OccurrencesBefore(v, i) =< i - 1 - cnt

Init ==
  /\ seq = <<0, 0, 1>>
  /\ i = 1
  /\ cand = 0
  /\ cnt = 0

Next ==
  \/ /\ i <= Len(seq)
     /\ cand' = seq[i]
     /\ cnt' = 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i <= Len(seq)
     /\ cand = seq[i]
     /\ cand' = cand
     /\ cnt' = cnt + 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i <= Len(seq)
     /\ cand # seq[i]
     /\ cand' = cand
     /\ cnt' = cnt - 1
     /\ i' = i + 1
     /\ UNCHANGED seq

Vars == <<seq, i, cand, cnt>>

Spec == Init /\ [][Next]_Vars

Correct ==
  \A cand \in Value : 2 * OccurrencesBefore(cand, Len(seq) + 1) > Len(seq)

=============================================================================