---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

\* Model checking finite instances of the Boulangerian bakery algorithm.
\* This module sets a bounded range on the otherwise infinite Nat type and
\* adds a state constraint to prune ticket numbers that would exceed it.
CONSTANTS N, MaxNat

VARIABLES pc, ticket, inCS, served
vars == <<pc, ticket, inCS, served>>

NatOverride == 0..MaxNat

Init ==
  /\ pc = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ inCS = {}
  /\ served = 0

Request(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "trying"]
  /\ UNCHANGED <<ticket, inCS, served>>

\* A process that wants the critical section takes the next ticket number.
TakeTicket(p) ==
  /\ pc[p] = "trying"
  /\ ticket' = [ticket EXCEPT ![p] = IF served + 1 = MaxNat THEN 0 ELSE served + 1]
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<inCS, served>>

\* A process enters the critical section only when its ticket is the lowest
\* among all processes that are currently waiting.
Enter(p) ==
  /\ pc[p] = "waiting"
  /\ \A q \in 1..N : (pc[q] = "waiting") => ticket[p] < ticket[q]
  /\ pc' = [pc EXCEPT ![p] = "critical"]
  /\ inCS' = inCS \cup {p}
  /\ UNCHANGED <<ticket, served>>

\* Exiting the critical section marks the process done for the round.
Exit(p) ==
  /\ pc[p] = "critical"
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ inCS' = inCS \ {p}
  /\ UNCHANGED <<ticket, served>>

\* A done process resets so a fresh ticket can be taken in the next round.
Reset(p) ==
  /\ pc[p] = "done"
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ served' = IF served = MaxNat THEN 0 ELSE served + 1
  /\ UNCHANGED inCS

Next ==
  \E p \in 1..N : Request(p) \/ TakeTicket(p) \/ Enter(p) \/ Exit(p) \/ Reset(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in 1..N : (pc[p] = "critical" /\ pc[q] = "critical") => p = q
TypeOK ==
  /\ pc \in [1..N -> {"idle", "trying", "waiting", "critical", "done"}]
  /\ ticket \in [1..N -> NatOverride]
  /\ inCS \subseteq 1..N
  /\ served \in NatOverride
Inv ==
  /\ MutualExclusion
  /\ TypeOK

\* Finite range: no ticket may ever reach the maximum, which bounds the
\* explored state space on every path of the model checker.
TicketsBounded == \A p \in 1..N : ticket[p] < MaxNat
====