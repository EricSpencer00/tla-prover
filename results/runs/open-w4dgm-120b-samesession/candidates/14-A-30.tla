---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES phase, inCS, wants, ticket, nextTicket

vars == <<phase, inCS, wants, ticket, nextTicket>>

Phases == {"idle", "waiting", "cs"}

TypeOK ==
    /\ phase \in [1..N -> Phases]
    /\ inCS \in [1..N -> BOOLEAN]
    /\ wants \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 1..MaxNat]
    /\ nextTicket \in 1..(MaxNat + 1)

Init ==
    /\ phase = [p \in 1..N |-> "idle"]
    /\ inCS = [p \in 1..N |-> FALSE]
    /\ wants = [p \in 1..N |-> FALSE]
    /\ ticket = [p \in 1..N |-> 1]
    /\ nextTicket = 1

Request(p) ==
    /\ phase[p] = "idle"
    /\ phase' = [phase EXCEPT ![p] = "waiting"]
    /\ wants' = [wants EXCEPT ![p] = TRUE]
    /\ ticket' = [t EXCEPT ![p] = IF nextTicket <= MaxNat THEN nextTicket ELSE MaxNat]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE MaxNat + 1
    /\ UNCHANGED inCS

Enter(p) ==
    /\ phase[p] = "waiting"
    /\ \A q \in 1..N : (phase[q] # "cs") \/ (ticket[p] < ticket[q])
    /\ phase' = [phase EXCEPT ![p] = "cs"]
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<wants, ticket, nextTicket>>

Leave(p) ==
    /\ phase[p] = "cs"
    /\ phase' = [phase EXCEPT ![p] = "idle"]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ wants' = [wants EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<ticket, nextTicket>>

Next == \E p \in 1..N : Request(p) \/ Enter(p) \/ Leave(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p \in 1..N : inCS[p] => (\A q \in 1..N \ {p} : ~inCS[q])

Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A p \in 1..N : phase[p] = "cs" => (wants[p] /\ inCS[p])
    /\ \A p \in 1..N : phase[p] = "idle" => (~wants[p] /\ ~inCS[p])

TicketBound == \A p \in 1..N : ticket[p] <= MaxNat

====