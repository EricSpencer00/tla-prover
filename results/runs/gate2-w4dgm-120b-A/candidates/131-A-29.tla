---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

VARIABLES arr, seen, candidate, count, index

vars == <<arr, seen, candidate, count, index>>

TypeOK ==
  /\ arr \in Value^3
  /\ seen \subseteq (0..2)
  /\ candidate \in Value
  /\ count \in 0..3
  /\ index \in 0..3

Init ==
  /\ arr = <<>>
  /\ seen = {}
  /\ candidate = CHOOSE v \in Value : TRUE
  /\ count = 0
  /\ index = 0

Load(v) ==
  /\ Len(arr) < 3
  /\ arr' = Append(arr, v)
  /\ UNCHANGED <<seen, candidate, count, index>>

Observe(i) ==
  /\ i \in 0..(Len(arr) - 1)
  /\ i \notin seen
  /\ seen' = seen \cup {i}
  /\ UNCHANGED <<arr, candidate, count, index>>

Reindex ==
  /\ index = 0
  /\ index' = 1
  /\ UNCHANGED <<arr, seen, candidate, count>>

Vote ==
  /\ index = 1
  /\ index < Len(arr)
  /\ LET v == arr[index] IN
       /\ candidate' = IF count = 0 THEN v ELSE candidate
       /\ count' = IF count = 0 THEN 1
                  ELSE IF v = candidate THEN count + 1 ELSE count - 1
  /\ index' = index + 1
  /\ UNCHANGED <<arr, seen>>

Finalize ==
  /\ index = Len(arr)
  /\ UNCHANGED vars

Next ==
  \/ \E v \in Value : Load(v)
  \/ \E i \in 0..2 : Observe(i)
  \/ Reindex
  \/ Vote
  \/ Finalize

Spec == Init /\ [][Next]_vars

Inv ==
  /\ index = 0 => count = 0
  /\ index > 0 => count >= 1

Correct ==
  /\ index = Len(arr)
  /\ \A i \in 0..(Len(arr) - 1) :
       (2 * Cardinality(seen \cap (0..i)) > i + 1) => arr[i] = candidate

====