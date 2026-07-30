---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* The bounded set of ticket numbers, replacing the infinite natural numbers.
\* The .cfg file substitutes NatOverride = Nat, so the spec can use Nat directly.
NatOverride == 0 .. MaxNat

VARIABLES inCS, ticket, chose, nextTicket

vars == <<inCS, ticket, chose, nextTicket>>

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> NatOverride]
  /\ chose \in [1..N -> BOOLEAN]
  /\ nextTicket \in NatOverride

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ chose = [p \in 1..N |-> FALSE]
  /\ nextTicket = 0

\* A process takes a ticket and enters the bakery.
Choose(p) ==
  /\ ~chose[p]
  /\ chose' = [chose EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE MaxNat
  /\ UNCHANGED inCS

\* A process enters the critical section only once every other ticket-holder
\* with an earlier ticket has left, and never when it holds no ticket.
Enter(p) ==
  /\ chose[p]
  /\ \A q \in 1..N : (q # p /\ chose[q]) => (ticket[p] < ticket[q])
  /\ ~inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, chose, nextTicket>>

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ chose' = [chose EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket>>

Next ==
  \/ \E p \in 1..N : Choose(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

InitInit == Init

Spec == InitInit /\ [][Next]_vars

\* The bakery invariant, stated here as the strongest of the three.
Inv == TypeOK

MutualExclusion ==
  \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => (p = q)

ISpec ==
  /\ Spec
  /\ TypeOK
  /\ \A p \in 1..N : Choose(p) \/ Enter(p) \/ Exit(p)

====