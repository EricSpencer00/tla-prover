---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, nextTicket

vars == <<inCS, want, ticket, nextTicket>>

TypeOK ==
    /\ inCS \subseteq (1..N)
    /\ want \subseteq (1..N)
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

MutualExclusion ==
    \A a, b \in inCS : a = b

Inv ==
    /\ MutualExclusion
    /\ TypeOK

Init ==
    /\ inCS = {}
    /\ want = {}
    /\ ticket = [i \in 1..N |-> 0]
    /\ nextTicket = 0

Request(i) ==
    /\ i \notin want
    /\ i \notin inCS
    /\ want' = want \cup {i}
    /\ UNCHANGED <<inCS, ticket, nextTicket>>

Enter(i) ==
    /\ i \in want
    /\ inCS = {}
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ inCS' = {i}
    /\ want' = want \ {i}
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket

Exit(i) ==
    /\ i \in inCS
    /\ inCS' = {}
    /\ UNCHANGED <<want, ticket, nextTicket>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

ISpec == Init /\ [][Next]_vars

NatOverride == Nat

====