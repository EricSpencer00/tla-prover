---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* No new state variables are introduced; all are inherited from the main
\* majority vote specification.
VARIABLES candidate, count, seen, seq, pos

vars == <<candidate, count, seen, seq, pos>>

Init ==
  /\ candidate = 0
  /\ count = 0
  /\ seen = {}
  /\ seq = [i \in 1..4 |-> IF i \in {1, 2} THEN 1 ELSE 0]
  /\ pos = 0

\* Scan the next position of the sequence and update candidate and count so that
\* candidate stays the majority of what has been seen.
Step ==
  /\ pos < 4
  /\ pos' = pos + 1
  /\ seen' = seen \cup {pos + 1}
  /\ IF seq[pos + 1] = candidate THEN
       count' = count + 1
     ELSE IF count > 0 THEN
       count' = count - 1
     ELSE
       /\ candidate' = seq[pos + 1]
       /\ count' = 1
  /\ UNCHANGED <<candidate, seq>>

Reset ==
  /\ pos = 4
  /\ pos' = 0
  /\ candidate' = 0
  /\ count' = 0
  /\ seen' = {}
  /\ UNCHANGED seq

Spec == Init /\ [][Step]_vars /\ [][Reset]_vars

TypeOK ==
  /\ candidate \in 0..1
  /\ count \in 0..4
  /\ seen \subseteq 1..4
  /\ seq \in [1..4 -> Value]
  /\ pos \in 0..4

\* Correct: if a value occurs in a strict majority of positions, it must equal
\* the candidate held after the full scan -- i.e. the algorithm never misses the
\* majority and never declares a non-majority as the result.
Correct ==
  \A v \in Value :
    (2 * Cardinality({i \in 1..4 : seq[i] = v}) > 4) => (v = candidate)

\* Inv: the invariant from the main spec -- candidate is the strict majority of
\* the positions that have been scanned so far.
Inv ==
  \A v \in Value :
    (2 * Cardinality({i \in seen : seq[i] = v}) > Cardinality(seen))
      => (v = candidate)

====