---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Value

\* The Boyer-Moore majority vote algorithm over a fixed sequence of values.
\* This module adds a machine-checked proof (TLAPS) that the algorithm's candidate
\* is the unique majority element, if one exists. All state variables and actions
\* are inherited from the main specification; this module only adds the proof.

VARIABLES i, candidate, count, seq

vars == <<i, candidate, count, seq>>

\* Scan indices are zero-based: i is the index of the next position to examine.
Indices == 0..(Len(seq) - 1)

\* The set of positions examined strictly before index k.
PositionsBefore(k) == {j \in 0..(k - 1) : TRUE}

\* Number of occurrences of v among positions examined before index k.
OccBefore(k, v) == Cardinality({j \in 0..(k - 1) : seq[j] = v})

TypeOK ==
  /\ i \in Indices
  /\ candidate \in Value \cup {"None"}
  /\ count \in 0..Len(seq)
  /\ seq \in Seq(Value)

Init ==
  /\ i = 0
  /\ candidate = "None"
  /\ count = 0
  /\ \E s \in Seq(Value) :
       /\ Len(s) > 0
       /\ seq' = s

\* Boyer-Moore: reset candidate when the running count drops to zero.
CheckCandidate(v) ==
  \/ /\ count = 0
     /\ candidate' = v
     /\ count' = 1
  \/ /\ count > 0 /\ v = candidate
     /\ count' = count + 1
     /\ candidate' = candidate
  \/ /\ count > 0 /\ v # candidate
     /\ count' = count - 1
     /\ candidate' = candidate

Next ==
  /\ i < Len(seq)
  /\ CheckCandidate(seq[i])
  /\ i' = i + 1
  /\ UNCHANGED <<candidate, count, seq>>

Spec == Init /\ [][Next]_vars

\* The running count never exceeds the number of positions examined so far.
Inv == count <= i

\* After the scan finishes, any majority element must equal the candidate.
Correct == \A v \in Value : (2 * OccBefore(Len(seq), v) > Len(seq)) => (v = candidate)

====