---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

State == [phase : {"idle", "waiting", "critical"},
          want : 0..N-1, ticket : 0..MaxNat]

VARIABLES proc state, nextTicket

vars == <<state, nextTicket>>

TypeOK ==
    /\ state \in [1..N -> State]
    /\ nextTicket \in 0..MaxNat

Init ==
    /\ state = [p \in 1..N |-> [phase |-> "idle", want |-> 0, ticket |-> 0]]
    /\ nextTicket = 0

Request(p) ==
    /\ state[p].phase = "idle"
    /\ \A q \in 1..N : state[q].phase # "waiting" => state[p].want' = q
    /\ state' = [state EXCEPT ![p] = [@ EXCEPT !.phase = "waiting"]]
    /\ UNCHANGED nextTicket

Enter(p) ==
    /\ state[p].phase = "waiting"
    /\ nextTicket < MaxNat
    /\ state' = [state EXCEPT ![p] = [@ EXCEPT !.phase = "critical", !.ticket = nextTicket]]
    /\ nextTicket' = nextTicket + 1
    /\ UNCHANGED state

Exit(p) ==
    /\ state[p].phase = "critical"
    /\ state' = [state EXCEPT ![p] = [@ EXCEPT !.phase = "idle"]]
    /\ UNCHANGED nextTicket

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A a, b \in 1..N :
        (state[a].phase = "critical" /\ state[b].phase = "critical") => a = b

Inv ==
    \A p \in 1..N :
        (state[p].phase = "waiting") =>
            /\ (\A q \in 1..N : state[q].phase # "critical")
            /\ state[p].want \in 1..N
            /\ (\A r \in 1..N : state[r].phase = "critical" => state[r].want < state[p].want)

TicketBound == \A p \in 1..N : state[p].ticket >= 0 /\ state[p].ticket < MaxNat

====