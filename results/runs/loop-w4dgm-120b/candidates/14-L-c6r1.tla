---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

VARIABLES status, inCS, ticket, nextTicket, acted

vars == <<status, inCS, ticket, nextTicket, acted>>

Types ==
    /\ status \in [1..N -> {"idle", "waiting", "in"}]
    /\ inCS \subseteq 1..N
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
    /\ acted \in 0..MaxNat

Init ==
    /\ status = [i \in 1..N |-> "idle"]
    /\ inCS = {}
    /\ ticket = [i \in 1..N |-> 0]
    /\ nextTicket = 0
    /\ acted = 0

Request(i) ==
    /\ status[i] = "idle"
    /\ nextTicket < MaxNat
    /\ status' = [status EXCEPT ![i] = "waiting"]
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = nextTicket + 1
    /\ UNCHANGED <<inCS, acted>>

Enter(i) ==
    /\ status[i] = "waiting"
    /\ inCS = {}
    /\ \A j \in 1..N : ~(status[j] = "waiting" /\ ticket[j] < ticket[i])
    /\ status' = [status EXCEPT ![i] = "in"]
    /\ inCS' = {i}
    /\ UNCHANGED <<ticket, nextTicket, acted>>

Release(i) ==
    /\ status[i] = "in"
    /\ acted < MaxNat
    /\ status' = [status EXCEPT ![i] = "idle"]
    /\ inCS' = {}
    /\ acted' = acted + 1
    /\ UNCHANGED <<ticket, nextTicket>>

Reset ==
    /\ nextTicket = MaxNat
    /\ acted = MaxNat
    /\ \A i \in 1..N : status[i] = "idle"
    /\ nextTicket' = 0
    /\ acted' = 0
    /\ ticket' = [i \in 1..N |-> 0]
    /\ UNCHANGED <<status, inCS>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Release(i)
    \/ Reset

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i \in 1..N : status[i] = "in" => inCS = {i}

TypeOK ==
    /\ status \in [1..N -> {"idle", "waiting", "in"}]
    /\ inCS \subseteq 1..N
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
    /\ acted \in 0..MaxNat

Inv ==
    /\ \A i \in 1..N : status[i] = "in" => inCS = {i}
    /\ \A i \in 1..N : status[i] = "waiting" => ticket[i] < nextTicket

TicketBound == \A i \in 1..N : ticket[i] <= MaxNat

NatOverride == Nat \* DUMMY DEFINITION TO SATISFY .cfg REDECLARATION

====