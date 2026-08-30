---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, nextTicket

vars == <<inCS, want, ticket, nextTicket>>

Init ==
    /\ inCS = {}
    /\ want = [p \in 1..N |-> FALSE]
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 1

Request(p) ==
    /\ ~want[p]
    /\ want' = [want EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<inCS, ticket, nextTicket>>

Enter(p) ==
    /\ want[p]
    /\ inCS = {}
    /\ inCS' = {p}
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE MaxNat
    /\ UNCHANGED want

Exit(p) ==
    /\ p \in inCS
    /\ inCS' = {}
    /\ want' = [want EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<ticket, nextTicket>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

Spec == Next

MutualExclusion == \A a, b \in inCS : a = b
TypeOK ==
    /\ inCS \subseteq 1..N
    /\ want \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
Inv ==
    /\ MutualExclusion
    /\ TypeOK

ISpec == Spec

====