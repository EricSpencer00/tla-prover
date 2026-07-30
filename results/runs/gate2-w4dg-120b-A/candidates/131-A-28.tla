---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANT Value

ASSUME Value \in FiniteSets

VARIABLES seq, candidate, count, voted, instances, seen
vars == <<seq, candidate, count, voted, instances, seen>>

TypeOK ==
    /\ seq \in [0..3 -> Value \cup {"none"}]
    /\ candidate \in Value \cup {"none"}
    /\ count \in 0..3
    /\ voted \in 0..3
    /\ instances \in [Value -> 0..3]
    /\ seen \in SUBSET Nat

Init ==
    /\ seq = [i \in 0..3 |-> IF i = 0 THEN Value ELSE "none"]
    /\ candidate = "none"
    /\ count = 0
    /\ voted = 0
    /\ instances = [v \in Value |-> 0]
    /\ seen = {}

Next ==
    \/ /\ seq' = [seq EXCEPT ![voted] = candidate]
       /\ candidate' = IF candidate = "none" THEN seq[voted] ELSE candidate
       /\ count' = IF count = 0 THEN 1 ELSE count + 1
       /\ voted' = voted + 1
       /\ instances' = [instances EXCEPT ![seq[voted]] = @ + 1]
       /\ seen' = IF seq[voted] = "none" THEN seen ELSE seen \cup {voted}
    \/ /\ candidate' = "none"
       /\ count' = 0
       /\ seq' = seq

Spec == Init /\ [][Next]_vars

Correct ==
    /\ TypeOK
    /\ (\A i \in 0..voted => seq[i] \in Value \cup {"none"})
    /\ (voted = 3 => candidate # "none")
    /\ \A x \in Value : instances[x] <= voted

Inv ==
    /\ TypeOK
    /\ (voted = 3 /\ candidate # "none")
       => \A x \in Value : instances[x] > (voted \div 2) => x = candidate
    /\ (voted = 3 /\ candidate = "none")
       => \A x \in Value : instances[x] > (voted \div 2) => FALSE

====