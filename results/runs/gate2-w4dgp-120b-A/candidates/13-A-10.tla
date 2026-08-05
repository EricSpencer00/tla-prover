---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, nextTicket, served, maxServed

vars == <<inCS, ticket, nextTicket, served, maxServed>>

\* The full set of processes, 1-indexed for readability
Procs == 1..N

\* Overridden finite version of Nat for model checking: a set of natural numbers
\* bounded by MaxNat, so ticket numbers are never unbounded.
NatOverride == 0..MaxNat

TypeOK ==
  /\ inCS \subseteq Procs
  /\ ticket \in [Procs -> NatOverride]
  /\ nextTicket \in NatOverride
  /\ served \in 0..N
  /\ maxServed \in 0..N

Init ==
  /\ inCS = {}
  /\ ticket = [p \in Procs |-> 0]
  /\ nextTicket = 0
  /\ served = 0
  /\ maxServed = 0

Enter(p) ==
  /\ p \notin inCS
  /\ \A q \in inCS : ticket[p] < ticket[q]
  /\ inCS' = inCS \cup {p}
  /\ UNCHANGED <<ticket, nextTicket, served, maxServed>>

Exit(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ served' = served + 1
  /\ maxServed' = IF served + 1 > maxServed THEN served + 1 ELSE maxServed
  /\ UNCHANGED <<ticket, nextTicket>>

\* Taking a ticket is bounded by MaxNat so the model stays finite.
TakeTicket(p) ==
  /\ p \notin inCS
  /\ ticket[p] = 0
  /\ nextTicket > 0
  /\ nextTicket <= MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket - 1
  /\ UNCHANGED <<inCS, served, maxServed>>

NextT ==
  /\ \E p \in Procs :
       Enter(p) \/ Exit(p) \/ TakeTicket(p)

MutualExclusion == \A p, q \in Procs : (p \in inCS /\ q \in inCS) => p = q

Inv == TypeOK /\ MutualExclusion

ISpec == Init /\ [][NextT]_vars

====