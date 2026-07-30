---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

NONE == "NONE"

VARIABLES inCS, wants, ticket, nextTicket

vars == <<inCS, wants, ticket, nextTicket>>

TypeOK ==
    /\ inCS \subseteq 1..N
    /\ wants \subseteq 1..N
    /\ ticket \in [1..N -> 0..(MaxNat - 1)]
    /\ nextTicket \in 0..(MaxNat - 1)

Init ==
    /\ inCS = {}
    /\ wants = {}
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0

Request(p) ==
    /\ p \notin wants
    /\ p \notin inCS
    /\ wants' = wants \cup {p}
    /\ UNCHANGED <<inCS, ticket, nextTicket>>

Enter(p) ==
    /\ p \in wants
    /\ inCS = {}
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = IF nextTicket < MaxNat - 1 THEN nextTicket + 1 ELSE nextTicket
    /\ inCS' = {p}
    /\ UNCHANGED wants

Exit(p) ==
    /\ p \in inCS
    /\ inCS' = {}
    /\ wants' = wants \ {p}
    /\ UNCHANGED <<ticket, nextTicket>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p1, p2 \in inCS : p1 = p2

Inv == TypeOK /\ MutualExclusion

====