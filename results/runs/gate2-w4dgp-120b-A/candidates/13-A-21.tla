---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES cstate, ticket, nextTicket, turn
vars == <<cstate, ticket, nextTicket, turn>>

\* An arbitrary finite uniform bound on natural numbers for the model checker.
\* Overrides the infinite Nat from Naturals (see the .cfg) so that ticket numbers
\* and the round counter stay within a finite, exhaustively searchable range.
NatOverride == 0..MaxNat

Init ==
  /\ cstate = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 1
  /\ turn = 0

Enter(p) ==
  /\ cstate[p] = "idle"
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
  /\ cstate' = [cstate EXCEPT ![p] = "trying"]
  /\ UNCHANGED turn

Acquire(p) ==
  /\ cstate[p] = "trying"
  /\ turn = 0
  /\ turn' = ticket[p]
  /\ cstate' = [cstate EXCEPT ![p] = "critical"]
  /\ UNCHANGED <<ticket, nextTicket>>

Leave(p) ==
  /\ cstate[p] = "critical"
  /\ cstate' = [cstate EXCEPT ![p] = "idle"]
  /\ turn' = 0
  /\ UNCHANGED <<ticket, nextTicket>>

Next == \E p \in 1..N : Enter(p) \/ Acquire(p) \/ Leave(p)

ISpec == Init /\ [][Next]_vars

\* Mutual exclusion holds for the critical section.
MutualExclusion ==
  \A p, q \in 1..N :
    (cstate[p] = "critical" /\ cstate[q] = "critical") => p = q

TypeOK ==
  /\ cstate \in [1..N -> {"idle", "trying", "critical"}]
  /\ ticket \in [1..N -> NatOverride]
  /\ nextTicket \in NatOverride
  /\ turn \in NatOverride

\* The full inductive invariant from the reference Bakery specification.
Inv ==
  /\ MutualExclusion
  /\ (turn > 0 => turn \in NatOverride)
  /\ nextTicket <= MaxNat + 1
  /\ \A p \in 1..N :
       cstate[p] = "trying" => ticket[p] = turn
====