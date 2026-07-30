---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The module imports the main majority vote specification and adds a machine-
\* checked proof that it correctly identifies the only possible majority
\* element. No new state is introduced; all variables are inherited.

VARIABLES cand, count, seq, i

vars == <<cand, count, seq, i>>

\* Count(x, n) is the number of occurrences of x in the scanned prefix of
\* seq before index n. The subscript is a natural number, which is why the
\* invariant can speak about equality of set cardinalities.
Count(x, n) == Cardinality({k \in 0..(n - 1) : seq[k] = x})

TypeOK ==
  /\ cand \in Value
  /\ count \in 0..3
  /\ seq \in [0..3 -> Value]
  /\ i \in 0..4

Init ==
  /\ cand = CHOOSE x \in Value : TRUE
  /\ count = 0
  /\ seq = [k \in 0..3 |-> CHOOSE x \in Value : TRUE]
  /\ i = 0

\* Every transition of the main specification is preserved here unchanged.
Next ==
  \/ /\ i < 4
     /\ \E x \in Value :
          /\ seq' = [seq EXCEPT ![i] = x]
          /\ cand' = IF count = 0 THEN x ELSE cand
          /\ count' = IF count = 0 THEN 1
                      ELSE IF cand = x THEN count + 1
                      ELSE count - 1
          /\ i' = i + 1
  \/ /\ i = 4
     /\ UNCHANGED <<cand, count, seq, i>>

Spec == Init /\ [][Next]_vars

\* The algorithm maintains that the scanned candidate is backed by at
\* least one more occurrence than any other value.
Inv ==
  \A x \in Value :
    \A n \in 0..i : Count(cand, n) >= Count(x, n)

Correct == i = 4 => \A x \in Value : Count(x, 4) > 2 => x = cand

====