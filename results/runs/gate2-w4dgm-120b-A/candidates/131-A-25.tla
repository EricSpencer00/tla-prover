---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

Spec == MajoritySpec

Init == MajorityInit

Vote == MajorityVote

Next == MajorityNext

vars == MajorityVars

TypeOK ==
    /\ candidate \in Value \cup {"none"}
    /\ count \in 0..Len(seq)
    /\ idx \in 0..Len(seq)
    /\ seen \subseteq Value

Init ==
    /\ candidate = "none"
    /\ count = 0
    /\ idx = 0
    /\ seen = {}

Vote ==
    /\ idx < Len(seq)
    /\ LET x == seq[idx] IN
        /\ candidate' = IF count = 0 THEN x ELSE candidate
        /\ count' = IF count = 0 THEN 1
                    ELSE IF x = candidate THEN count + 1 ELSE count - 1
        /\ seen' = seen \cup {x}
    /\ idx' = idx + 1

Next ==
    \/ Vote
    \/ UNCHANGED vars

Inv ==
    /\ count = Cardinality({k \in 0..(idx - 1) : seq[k] = candidate})
    /\ candidate # "none" => candidate \in seen

Correct ==
    \A v \in Value : (Occurs(v) > Len(seq) \div 2) => (candidate = v)

TypeOKInv ==
    /\ candidate \in Value \cup {"none"}
    /\ count \in 0..Len(seq)
    /\ idx \in 0..Len(seq)
    /\ seen \subseteq Value

====