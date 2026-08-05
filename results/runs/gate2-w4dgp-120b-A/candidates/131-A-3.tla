---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

ASSUME Value # {}

VARIABLES seq, cand, count, pos

vars == <<seq, cand, count, pos>>

Occurs(v, S) == Cardinality({i \in S : seq[i] = v})

TypeOK ==
    /\ seq \in [1..4 -> Value]
    /\ cand \in Value \cup {"none"}
    /\ count \in 0..4
    /\ pos \in 0..4

Init ==
    /\ seq = [i \in 1..4 |-> CHOOSE v \in Value : TRUE]
    /\ cand = "none"
    /\ count = 0
    /\ pos = 0

Step ==
    /\ pos < 4
    /\ LET v == seq[pos + 1] IN
         IF count = 0
         THEN /\ cand' = v
              /\ count' = 1
         ELSE IF v = cand
              THEN /\ cand' = cand
                   /\ count' = count + 1
              ELSE /\ cand' = cand
                   /\ count' = count - 1
    /\ pos' = pos + 1

Spec == Init /\ [][Step]_vars

Inv == \A v \in Value : (Occurs(v, 1..4) > 2) => (cand = v)

TypeOKInv == TypeOK

====