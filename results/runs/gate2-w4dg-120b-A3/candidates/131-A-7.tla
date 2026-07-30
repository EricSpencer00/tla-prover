---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* Any candidate is always a value from the input domain or the
\* distinguished "no candidate" marker; candidate and count are only
\* ever updated together on a transition that consumes one input.
CandDomain == {Value, 0}

VARIABLES seq, candidate, count, idx
vars == <<seq, candidate, count, idx>>

TypeOK ==
  /\ seq \in SUBSET Value
  /\ candidate \in CandDomain
  /\ count \in 0..3
  /\ idx \in 0..3

\* No majority exists among an empty scanned prefix.
NoMajority ==
  \A x \in Value : Cardinality({i \in 0..(idx - 1) : seq[i] = x}) * 2 <= idx

Init ==
  /\ seq = {}
  /\ candidate = 0
  /\ count = 0
  /\ idx = 0

\* The input is modeled as an infinite stream of values, but the
\* bounded model only ever consumes values for index < 3.
Read(v) ==
  /\ idx < 3
  /\ seq' = [seq EXCEPT ![idx] = v]
  /\ idx' = idx + 1
  /\ IF candidate = 0 THEN candidate' = v ELSE candidate' = candidate
  /\ IF count = 0 THEN count' = 1 ELSE count' = count + 1

Reset ==
  /\ count = 0
  /\ count' = 1
  /\ candidate' = seq[idx]
  /\ UNCHANGED <<seq, idx>>

Decline ==
  /\ count > 0
  /\ count' = count - 1
  /\ UNCHANGED <<seq, candidate, idx>>

Next ==
  \/ \E v \in Value : Read(v)
  \/ Reset
  \/ Decline

Spec == Init /\ [][Next]_vars

\* The candidate is only well-defined once some input has been read,
\* or when it is the distinguished marker.
Inv == (idx > 0) => (candidate \in Value)
Correct == NoMajority => (candidate = seq[0])

====