---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, nextTicket, active

vars == <<inCS, ticket, nextTicket, active>>

Nnat == 0..MaxNat

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ active = 0

Enter(p) ==
  /\ active < N
  /\ ~inCS[p]
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ active' = active + 1

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ active' = active - 1
  /\ UNCHANGED <<ticket, nextTicket>>

Reset ==
  /\ \A p \in 1..N : ~inCS[p]
  /\ nextTicket = MaxNat
  /\ nextTicket' = 0
  /\ ticket' = [p \in 1..N |-> 0]
  /\ UNCHANGED <<inCS, active>>

Next ==
  \/ Reset
  \/ \E p \in 1..N : Enter(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => p = q

TypeOK ==
  /\ nextTicket \in Nnat
  /\ \A p \in 1..N : ticket[p] \in Nnat

Inv ==
  /\ \A p \in 1..N : inCS[p] => ticket[p] < nextTicket
  /\ (active = 0 => nextTicket = 0)
  /\ (active > 0 => nextTicket > 0)

TicketBound == \A p \in 1..N : ticket[p] < MaxNat

====