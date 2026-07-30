---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES inCS, number, choosing, id

vars == <<inCS, number, choosing, id>>

TypeOK ==
    /\ inCS \in [Nat -> BOOLEAN]
    /\ number \in [Nat -> 0..MaxNat]
    /\ choosing \in [Nat -> BOOLEAN]
    /\ id \in 0..MaxNat

Init ==
    /\ inCS = [p \in Nat |-> FALSE]
    /\ number = [p \in Nat |-> 0]
    /\ choosing = [p \in Nat |-> FALSE]
    /\ id = 0

MaxNumber ==
    LET f[S \in SUBSET Nat] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : \A z \in S : number[z] <= number[y]
             IN number[x]
    IN f[Nat]

Enter(p) ==
    /\ ~inCS[p]
    /\ ~choosing[p]
    /\ id < MaxNat
    /\ \A q \in Nat : ~inCS[q]
    /\ number' = [number EXCEPT ![p] = MaxNumber + 1]
    /\ id' = id + 1
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ UNCHANGED choosing

Leave(p) ==
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ number' = [number EXCEPT ![p] = 0]
    /\ UNCHANGED <<choosing, id>>

ISpec == Init /\ [][UNION {Enter(p), Leave(p)} : p \in Nat]_vars

MutualExclusion ==
    \A p, q \in Nat : (inCS[p] /\ inCS[q]) => p = q

Inv ==
    \A p \in Nat :
        /\ inCS[p] => number[p] > 0
        /\ \A q \in Nat : inCS[q] => number[p] <= number[q]

====