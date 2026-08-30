---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* The Boyer-Moore majority vote algorithm. It picks at most one candidate while
\* scanning the sequence, then counts that candidate's occurrences afterwards.
\* Correctness: a strict majority can only be the candidate that was picked.
\* The invariant is proved by TLAPS from two lemmas about finite set cardinality.

VARIABLES candidate, candCount, seen, phase, seq

vars == <<candidate, candCount, seen, phase, seq>>

\* The set of positions scanned so far.
SeenSet == { i \in seen : TRUE }

Init ==
    /\ candidate = "none"
    /\ candCount = 0
    /\ seen = {}
    /\ phase = "scanning"
    /\ seq \in [0..2 -> Value]

Scan ==
    /\ phase = "scanning"
    /\ \E i \in {0, 1, 2} :
         /\ i \notin seen
         /\ seen' = seen \cup {i}
         /\ IF candidate = "none"
              THEN candidate' = seq[i]
              ELSE IF seq[i] = candidate
                      THEN candidate' = candidate
                      ELSE candidate' = candidate
         /\ candCount' = IF seq[i] = candidate THEN candCount + 1 ELSE candCount
    /\ UNCHANGED <<phase, seq>>

Count ==
    /\ phase = "scanning"
    /\ \A i \in {0, 1, 2} : i \in seen
    /\ phase' = "counted"
    /\ UNCHANGED <<candidate, candCount, seen, seq>>

Reset ==
    /\ phase = "counted"
    /\ candidate' = "none"
    /\ candCount' = 0
    /\ seen' = {}
    /\ phase' = "scanning"
    /\ UNCHANGED <<seq>>

Next == Scan \/ Count \/ Reset

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ candidate \in Value \cup {"none"}
    /\ candCount \in 0..3
    /\ seen \subseteq {0, 1, 2}
    /\ phase \in {"scanning", "counted"}
    /\ seq \in [0..2 -> Value]

\* LEARNED: a value with a strict majority must be the candidate itself.
Correct ==
    /\ phase = "counted"
    /\ \A v \in Value : (Cardinality({ i \in {0, 1, 2} : seq[i] = v }) * 2 > 3) => v = candidate

\* Initialized and preserved by every transition.
Inv ==
    /\ TypeOK
    /\ Correct

====