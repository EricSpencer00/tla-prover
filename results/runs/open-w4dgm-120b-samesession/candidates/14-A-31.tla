---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES holder, ticket, inCS, nextTicket

vars == <<holder, ticket, inCS, nextTicket>>

Elems == 1..N

Init ==
  /\ holder = 0
  /\ ticket = [p \in Elems |-> 0]
  /\ inCS = [p \in Elems |-> FALSE]
  /\ nextTicket = 1

Acquire(p) ==
  /\ holder = 0
  /\ ~inCS[p]
  /\ holder' = p
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE MaxNat
  /\ UNCHANGED inCS

Enter(p) ==
  /\ holder = p
  /\ ~inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<holder, ticket, nextTicket>>

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ holder' = 0
  /\ UNCHANGED <<ticket, nextTicket>>

Next ==
  \E p \in Elems :
    \/ Acquire(p
    \/ Enter(p)
    \/ Exit(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ holder \in 0..N
  /\ ticket \in [Elems -> 0..MaxNat]
  /\ inCS \in [Elems -> BOOLEAN]
  /\ nextTicket \in 0..MaxNat

MutualExclusion ==
  \A p \in Elems : inCS[p] => (holder = p)

Inv ==
  \A p \in Elems : inCS[p] => (holder = p)

TicketBounded ==
  \A p \in Elems : ticket[p] < MaxNat

====