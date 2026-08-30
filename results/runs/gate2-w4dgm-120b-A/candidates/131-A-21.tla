---- MODULE MajorityProof ----
EXTENDS Majority, Naturals, FiniteSets

CONSTANTS Value

VARIABLES seq, pos, left, seen, candidate
vars == <<seq, pos, left, seen, candidate>>

TypeOK ==
    /\ seq \subseteq Value
    /\ pos \in 0..Cardinality(seq)
    /\ left \subseteq Value
    /\ seen \in [Value -> BOOLEAN]
    /\ candidate \in Value \cup {"none"}

Init ==
    /\ seq = {}
    /\ pos = 0
    /\ left = Value
    /\ seen = [v \in Value |-> FALSE]
    /\ candidate = "none"

Vote(v) ==
    /\ v \in left
    /\ seq' = seq \cup {v}
    /\ pos' = pos + 1
    /\ left' = left \ {v}
    /\ seen' = [seen EXCEPT ![v] = TRUE]
    /\ candidate' = IF candidate = "none" THEN v ELSE candidate

Skip ==
    /\ \E v \in left : left' = left \ {v}
    /\ pos' = pos + 1
    /\ seen' = [v \in Value |-> seen[v] \/ (v \in left)]
    /\ candidate' = IF candidate = "none" /\ Cardinality(Value \ left) > 0
                     THEN CHOOSE v \in (Value \ left) : TRUE
                     ELSE candidate
    /\ UNCHANGED <<seq>>

Reset ==
    /\ pos = Cardinality(Value)
    /\ pos' = 0
    /\ seq' = {}
    /\ left' = Value
    /\ seen' = [v \in Value |-> FALSE]
    /\ candidate' = "none"

Next == (\E v \in Value : Vote(v)) \/ Skip \/ Reset

Spec == Init /\ [][Next]_vars

Inv ==
    /\ TypeOK
    /\ (pos = Cardinality(seq))
    /\ (left = Value \ seq)
    /\ (\A v \in seq : seen[v])
    /\ (pos = Cardinality(Value) => candidate # "none")
    /\ (cardinality(seq) >= 2 => candidate \in seq)

Correct == (pos = Cardinality(Value)) => (\A v \in Value : Cardinality(seq) > Cardinality(Value) / 2 => v = candidate)

TypeOKProp == TypeOK
====