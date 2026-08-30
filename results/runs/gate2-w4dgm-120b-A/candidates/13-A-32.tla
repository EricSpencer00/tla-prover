---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, interested, served, crashed

vars == <<inCS, ticket, interested, served, crashed>>

TypeOK ==
    /\ inCS \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ interested \in [1..N -> BOOLEAN]
    /\ served \in 0..MaxNat
    /\ crashed \subseteq (1..N)

Init ==
    /\ inCS = [p \in 1..N |-> FALSE]
    /\ ticket = [p \in 1..N |-> 0]
    /\ interested = [p \in 1..N |-> FALSE]
    /\ served = 0
    /\ crashed = {}

Request(p) ==
    /\ p \notin crashed
    /\ ~interested[p]
    /\ ~inCS[p]
    /\ served < MaxNat
    /\ interested' = [interested EXCEPT ![p] = TRUE]
    /\ ticket' = [ticket EXCEPT ![p] = served + 1]
    /\ served' = served + 1
    /\ UNCHANGED <<inCS, crashed>>

Enter(p) ==
    /\ p \notin crashed
    /\ interested[p]
    /\ ~inCS[p]
    /\ \A q \in 1..N : (~interested[q] \/ ticket[q] > ticket[p])
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<ticket, interested, served, crashed>>

Exit(p) ==
    /\ p \notin crashed
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ interested' = [interested EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<ticket, served, crashed>>

Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<inCS, ticket, interested, served>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)
    \/ \E p \in 1..N : Crash(p)

MutualExclusion ==
    \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => (p = q)

Inv == TypeOK /\ MutualExclusion

ISpec == Init /\ [][Next]_vars

====