---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES waiting, cs, ticket, nextTicket

vars == <<waiting, cs, ticket, nextTicket>>

\* Overrides the infinite Nat type from Naturals with a finite range so the
\* Bakery model stays within a bounded state space (required for MC).
NatOverride(n) == n % (MaxNat + 1)

Init ==
    /\ waiting = {}
    /\ cs = {}
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0

Request(p) ==
    /\ p \notin waiting
    /\ p \notin cs
    /\ waiting' = waiting \cup {p}
    /\ ticket' = [ticket EXCEPT ![p] = NatOverride(nextTicket)]
    /\ nextTicket' = NatOverride(nextTicket + 1)
    /\ UNCHANGED cs

Enter(p) ==
    /\ p \in waiting
    /\ waiting' = waiting \ {p}
    /\ cs' = cs \cup {p}
    /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
    /\ p \in cs
    /\ cs' = cs \ {p}
    /\ UNCHANGED <<waiting, ticket, nextTicket>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

ISpec == Init /\ [][Next]_vars

MutualExclusion == cs \cap waiting = {} /\ Cardinality(cs) <= 1
TypeOK ==
    /\ waiting \subseteq (1..N)
    /\ cs \subseteq (1..N)
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
Inv == MutualExclusion /\ TypeOK

====