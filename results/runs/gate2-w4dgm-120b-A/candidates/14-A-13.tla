---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

VARIABLES cs, inCS, read, ticket, nextTicket
vars == <<cs, inCS, read, ticket, nextTicket>>

Init ==
    /\ cs = 0
    /\ inCS = [p \in 1..N |-> FALSE]
    /\ read = [p \in 1..N |-> 0]
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 1

Request(p) ==
    /\ ~inCS[p]
    /\ ticket[p] = 0
    /\ read' = [read EXCEPT ![p] = nextTicket]
    /\ UNCHANGED <<cs, inCS, ticket, nextTicket>>

Acquire(p) ==
    /\ ~inCS[p]
    /\ ticket[p] = 0
    /\ cs = 0
    /\ read[p] = nextTicket
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ ticket' = [ticket EXCEPT ![p] = read[p]]
    /\ cs' = 1
    /\ nextTicket' = read[p] + 1
    /\ UNCHANGED read

Retry(p) ==
    /\ ~inCS[p]
    /\ ticket[p] = 0
    /\ read[p] # nextTicket
    /\ read' = [read EXCEPT ![p] = nextTicket]
    /\ UNCHANGED <<cs, inCS, ticket, nextTicket>>

Release(p) ==
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ cs' = 0
    /\ UNCHANGED <<read, nextTicket>>

Next == \E p \in 1..N : Request(p) \/ Acquire(p) \/ Retry(p) \/ Release(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == cs <= 1

TypeOK ==
    /\ cs \in 0..N
    /\ inCS \in [1..N -> BOOLEAN]
    /\ read \in [1..N -> 0..MaxNat]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 1..(MaxNat + 1)

Inv ==
    /\ \A p \in 1..N : inCS[p] => ticket[p] > 0
    /\ \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => p = q
    /\ \A p \in 1..N : inCS[p] => ticket[p] = cs

FiniteNatBound == \A p \in 1..N : ticket[p] < MaxNat

Properties == FiniteNatBound
====