---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES coarse, fine, phase, reqs, ticket, nextTicket

vars == <<coarse, fine, phase, reqs, ticket, nextTicket>>

TypeOK ==
    /\ coarse \in {"free", "held"}
    /\ fine \in {"free", "held"}
    /\ phase \in [1..N -> {"idle", "coarse", "critical"}]
    /\ reqs \subseteq 1..N
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

Init ==
    /\ coarse = "free"
    /\ fine = "free"
    /\ phase = [p \in 1..N |-> "idle"]
    /\ reqs = {}
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0

Request(p) ==
    /\ phase[p] = "idle"
    /\ p \notin reqs
    /\ phase' = [phase EXCEPT ![p] = "coarse"]
    /\ reqs' = reqs \cup {p}
    /\ UNCHANGED <<coarse, fine, ticket, nextTicket>>

EnterCoarse(p) ==
    /\ phase[p] = "coarse"
    /\ coarse = "free"
    /\ coarse' = "held"
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
    /\ UNCHANGED <<fine, phase, reqs>>

EnterFine(p) ==
    /\ phase[p] = "coarse"
    /\ coarse = "held"
    /\ fine = "free"
    /\ fine' = "held"
    /\ phase' = [phase EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<coarse, reqs, ticket, nextTicket>>

Exit(p) ==
    /\ phase[p] = "critical"
    /\ fine' = "free"
    /\ coarse' = "free"
    /\ phase' = [phase EXCEPT ![p] = "idle"]
    /\ reqs' = reqs \ {p}
    /\ UNCHANGED <<ticket, nextTicket>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : EnterCoarse(p)
    \/ \E p \in 1..N : EnterFine(p)
    \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p \in 1..N : phase[p] = "critical" => fine = "held"

Inv ==
    \A p \in 1..N :
        /\ phase[p] = "critical" => fine = "held"
        /\ fine = "held" => \E q \in 1..N : phase[q] = "critical"
        /\ phase[p] \in {"coarse", "critical"} => p \in reqs

TicketRange == \A p \in 1..N : ticket[p] <= MaxNat

====