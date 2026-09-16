---------------------------- MODULE W4Od16m0p2t1 ----------------------------
EXTENDS Naturals

CONSTANTS Workers, Total, MaxVer, NONE

VARIABLES
    stock,        \* pills on the shelf
    inTransit,    \* pills in processing
    dispensed,    \* pills already dispensed
    shelfVersion, \* optimistic lock version on shelf stock
    pending,      \* worker -> base version of its outstanding request, or NONE
    beacon

vars == <<stock, inTransit, dispensed, shelfVersion, pending, beacon>>

TypeOK ==
    /\ stock \in 0..Total
    /\ inTransit \in 0..Total
    /\ dispensed \in 0..Total
    /\ shelfVersion \in 0..MaxVer
    /\ pending \in [Workers -> (0..MaxVer) \cup {NONE}]
    /\ beacon \in BOOLEAN

Init ==
    /\ stock = Total
    /\ inTransit = 0
    /\ dispensed = 0
    /\ shelfVersion = 0
    /\ pending = [w \in Workers |-> NONE]
    /\ beacon = FALSE

Request(w) ==
    /\ pending[w] = NONE
    /\ pending' = [pending EXCEPT ![w] = shelfVersion]
    /\ UNCHANGED <<stock, inTransit, dispensed, shelfVersion, beacon>>

\* Optimistic reserve; serviced out of order, applied only if version still matches.
Reserve(w) ==
    /\ pending[w] # NONE
    /\ pending[w] = shelfVersion
    /\ stock > 0
    /\ shelfVersion < MaxVer
    /\ stock' = stock - 1
    /\ inTransit' = inTransit + 1
    /\ shelfVersion' = shelfVersion + 1
    /\ pending' = [pending EXCEPT ![w] = NONE]
    /\ UNCHANGED <<dispensed, beacon>>

RejectStale(w) ==
    /\ pending[w] # NONE
    /\ pending[w] # shelfVersion
    /\ pending' = [pending EXCEPT ![w] = NONE]
    /\ UNCHANGED <<stock, inTransit, dispensed, shelfVersion, beacon>>

Deliver ==
    /\ inTransit > 0
    /\ inTransit' = inTransit - 1
    /\ dispensed' = dispensed + 1
    /\ UNCHANGED <<stock, shelfVersion, pending, beacon>>

Return ==
    /\ dispensed > 0
    /\ shelfVersion < MaxVer
    /\ dispensed' = dispensed - 1
    /\ stock' = stock + 1
    /\ shelfVersion' = shelfVersion + 1
    /\ UNCHANGED <<inTransit, pending, beacon>>

Heartbeat ==
    /\ beacon' = ~beacon
    /\ UNCHANGED <<stock, inTransit, dispensed, shelfVersion, pending>>

Next ==
    \/ \E w \in Workers : Request(w)
    \/ \E w \in Workers : Reserve(w)
    \/ \E w \in Workers : RejectStale(w)
    \/ Deliver
    \/ Return
    \/ Heartbeat

Spec == Init /\ [][Next]_vars

PillsConserved ==
    stock + inTransit + dispensed = Total

=============================================================================