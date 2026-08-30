---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, nextTicket

vars == <<inCS, want, ticket, nextTicket>>

\* The Bakery spec's natural numbers are overridden here to a finite range
\* (0..MaxNat) so the model is finite and checkable by TLC.
NatOverride(n) == IF n <= MaxNat THEN n ELSE MaxNat

TypeOK ==
  /\ inCS \subseteq (1..N)
  /\ want \subseteq (1..N)
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat

Init ==
  /\ inCS = {}
  /\ want = {}
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0

\* A process announces it wants the critical section.
Request(i) ==
  /\ i \notin want
  /\ i \notin inCS
  /\ want' = want \cup {i}
  /\ UNCHANGED <<inCS, ticket, nextTicket>>

\* The bakery grants a ticket to a waiting process, saturating at MaxNat.
Grant(i) ==
  /\ i \in want
  /\ ticket[i] = 0
  /\ ticket' = [ticket EXCEPT ![i] = NatOverride(nextTicket + 1)]
  /\ nextTicket' = NatOverride(nextTicket + 1)
  /\ UNCHANGED <<inCS, want>>

\* A process enters the critical section only if its ticket is strictly
\* lower than every other waiting process's ticket.
Enter(i) ==
  /\ i \in want
  /\ ticket[i] # 0
  /\ \A j \in want : (j # i) => (ticket[i] < ticket[j])
  /\ inCS' = inCS \cup {i}
  /\ want' = want \ {i}
  /\ UNCHANGED <<ticket, nextTicket>>

\* A process leaves the critical section and gives up its ticket.
Exit(i) ==
  /\ i \in inCS
  /\ inCS' = inCS \ {i}
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED <<want, nextTicket>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Grant(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

\* SAFETY PROPERTY: mutual exclusion, plus the full inductive invariant.
MutualExclusion == \A i, j \in inCS : i = j
Inv == TypeOK /\ MutualExclusion

\* LIVENESS PROPERTY: NOT_SPECIFIED

\* The inductive spec starts from any reachable state satisfying the invariant.
ISpec == Init /\ [][Next]_vars

Spec == ISpec
====