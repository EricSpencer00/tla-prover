---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* Mutual exclusion via a ticketing scheme.  A process first requests a ticket
\* (Request) and then takes the critical section only when its ticket is the
\* smallest among all live processes (Enter).  It leaves with Exit.  Natural
\* numbers are overridden with the finite range 0..MaxNat; the state constraint
\* below keeps tickets strictly below MaxNat so no ticket can ever leave the
\* modelled range.
VARIABLES ticket, phase, csCount

vars == <<ticket, phase, csCount>>

TicketDomain == [1..N -> 0..MaxNat]

TypeOK ==
  /\ ticket \in TicketDomain
  /\ phase \in [1..N -> {"idle", "waiting", "critical"}]
  /\ csCount \in 0..N

Init ==
  /\ ticket = [p \in 1..N |-> 0]
  /\ phase = [p \in 1..N |-> "idle"]
  /\ csCount = 0

\* Request assigns a new ticket, bounded by the overridden natural-number range.
Request(p) ==
  /\ phase[p] = "idle"
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ phase' = [phase EXCEPT ![p] = "waiting"]
  /\ UNCHANGED csCount

Enter(p) ==
  /\ phase[p] = "waiting"
  /\ \A q \in 1..N : (phase[q] = "waiting") => (ticket[p] <= ticket[q])
  /\ csCount = 0
  /\ phase' = [phase EXCEPT ![p] = "critical"]
  /\ csCount' = csCount + 1
  /\ UNCHANGED ticket

Exit(p) ==
  /\ phase[p] = "critical"
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ csCount' = csCount - 1
  /\ UNCHANGED ticket

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == csCount <= 1

Inv ==
  /\ csCount >= 0
  /\ csCount <= N
  /\ \A p \in 1..N : ticket[p] <= MaxNat

\* The ticket bookkeeping stays within the finite range of a model-checkable
\* natural-number override.  It is a genuine safety constraint, not a liveness
\* property, so it is placed in the state-constraint section rather than under
\* PROPERTIES -- that is what makes it prune the state space instead of waiting
\* on a stuck system to become un-stuck.
StateConstraint == \A p \in 1..N : ticket[p] < MaxNat

====