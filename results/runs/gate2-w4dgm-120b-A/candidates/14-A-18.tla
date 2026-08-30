---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

RECURSIVE SumOver(_)
SumOver(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN x + SumOver(S \ {x})

VARIABLES cs, ticket, admin, readVal, active, nextFree

Vars == <<cs, ticket, admin, readVal, active, nextFree>>

TypeOK ==
    /\ cs \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ admin \in BOOLEAN
    /\ readVal \in [1..N -> 0..MaxNat]
    /\ active \in 0..N
    /\ nextFree \in 0..MaxNat

Init ==
    /\ cs = [p \in 1..N |-> FALSE]
    /\ ticket = [p \in 1..N |-> 0]
    /\ admin = FALSE
    /\ readVal = [p \in 1..N |-> 0]
    /\ active = 0
    /\ nextFree = 0

Read(p) ==
    /\ ~cs[p]
    /\ readVal' = [readVal EXCEPT ![p] = ticket[p]]
    /\ UNCHANGED <<cs, ticket, admin, active, nextFree>>

EnterCAS(p) ==
    /\ ~cs[p]
    /\ readVal[p] = ticket[p]
    /\ ticket[p] < nextFree
    /\ nextFree < MaxNat
    /\ cs' = [cs EXCEPT ![p] = TRUE]
    /\ ticket' = [ticket EXCEPT ![p] = ticket[p] + 1]
    /\ active' = active + 1
    /\ nextFree' = nextFree + 1
    /\ UNCHANGED <<admin, readVal>>

Leave(p) ==
    /\ cs[p]
    /\ cs' = [cs EXCEPT ![p] = FALSE]
    /\ active' = active - 1
    /\ UNCHANGED <<ticket, admin, readVal, nextFree>>

AdminForce(p) ==
    /\ ~admin
    /\ ~cs[p]
    /\ ticket[p] < nextFree
    /\ nextFree < MaxNat
    /\ admin' = TRUE
    /\ cs' = [cs EXCEPT ![p] = TRUE]
    /\ ticket' = [ticket EXCEPT ![p] = ticket[p] + 1]
    /\ active' = active + 1
    /\ nextFree' = nextFree + 1
    /\ UNCHANGED readVal

AdminClear(p) ==
    /\ admin
    /\ cs[p]
    /\ cs' = [cs EXCEPT ![p] = FALSE]
    /\ admin' = FALSE
    /\ active' = active - 1
    /\ UNCHANGED <<ticket, readVal, nextFree>>

Next ==
    \/ \E p \in 1..N : Read(p)
    \/ \E p \in 1..N : EnterCAS(p)
    \/ \E p \in 1..N : Leave(p)
    \/ \E p \in 1..N : AdminForce(p)
    \/ \E p \in 1..N : AdminClear(p)

Spec == Init /\ [][Next]_Vars

MutualExclusion ==
    /\ active <= 1
    /\ \A p \in 1..N : cs[p] => (active = 1)

Inv ==
    /\ \A p \in 1..N : cs[p] => (ticket[p] = nextFree)
    /\ nextFree <= SumOver(1..N)

NatOverride == Nat
====