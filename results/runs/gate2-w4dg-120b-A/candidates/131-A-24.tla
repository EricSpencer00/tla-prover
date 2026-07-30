---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

ASSUME Value \in NONEMPTYFINITE

VARIABLES candidate, tally, pos, major

vars == <<candidate, tally, pos, major>>

RECURSIVE NumOcc(_)
NumOcc(S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN tally[x] + NumOcc(S \ {x})

TypeOK ==
    /\ candidate \in Value
    /\ tally \in [Value -> 0..2]
    /\ pos \in 0..2
    /\ major \in Value \cup {"none"}

Init ==
    /\ candidate \in Value
    /\ tally = [v \in Value |-> 0]
    /\ pos = 0
    /\ major = "none"

Vote(x) ==
    /\ candidate' = x
    /\ tally' = [tally EXCEPT ![x] = @ + 1]
    /\ pos' = (pos + 1) % 3
    /\ major' = IF tally[x] + 1 > 2 THEN x ELSE major

Spec ==
    /\ Init
    /\ [][Vote(_)]_vars

Inv ==
    /\ candidate \in Value
    /\ tally \in [Value -> 0..2]
    /\ pos \in 0..2
    /\ major \in Value \cup {"none"}

Correct ==
    /\ Inv
    /\ (\A x \in Value : NumOcc(Value) > 1 => candidate = x)

====