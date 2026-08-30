---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES pos, cand, count, majority, seen

vars == <<pos, cand, count, majority, seen>>

Positions == 0..4
Before(i) == { k \in Positions : k < i }

TypeOK ==
    /\ pos \in Positions
    /\ cand \in Value
    /\ count \in 0..5
    /\ majority \in Value
    /\ seen \subseteq Value

Init ==
    /\ pos = 0
    /\ cand = (CHOOSE v \in Value : TRUE)
    /\ count = 0
    /\ majority = (CHOOSE v \in Value : TRUE)
    /\ seen = {}

Read(v) ==
    /\ pos \notin Before(5)
    /\ v \notin seen
    /\ seen' = seen \cup {v}
    /\ UNCHANGED <<pos, cand, count, majority>>

Match(v) ==
    /\ pos \notin Before(5)
    /\ cand' = IF v = cand THEN cand ELSE v
    /\ count' = IF v = cand THEN count + 1 ELSE 1
    /\ pos' = pos + 1
    /\ UNCHANGED <<majority, seen>>

Finish ==
    /\ pos \notin Before(5)
    /\ majority' = IF count * 2 > pos THEN cand ELSE majority
    /\ UNCHANGED <<pos, cand, count, seen>>

Reset ==
    /\ pos \in Before(5)
    /\ pos' = 0
    /\ count' = 0
    /\ UNCHANGED <<cand, majority, seen>>

Next ==
    \/ \E v \in Value : Read(v)
    \/ \E v \in Value : Match(v)
    \/ Finish
    \/ Reset

Spec == Init /\ [][Next]_vars

Inv ==
    /\ TypeOK
    /\ \A v \in Value : (count * 2 > pos) => (v = cand)

Correct ==
    /\ TypeOK
    /\ Inv

====