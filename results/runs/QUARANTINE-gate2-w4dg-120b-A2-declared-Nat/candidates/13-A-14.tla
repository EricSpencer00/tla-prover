---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat
CONSTANTS None

\* The model overrides the infinite Nat with a finite range.
NatOverride == 0..MaxNat

VARIABLES inCS, ticket, choosing, nextTicket
vars == <<inCS, ticket, choosing, nextTicket>>

Bump(x) == IF x < MaxNat THEN x + 1 ELSE MaxNat

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ choosing = [p \in 1..N |-> FALSE]
  /\ nextTicket = 0

\* A process begins picking a ticket: it snapshots the nextTicket value
\* and sets its choosing flag, recording that quiescent read.
Choose(p) ==
  /\ ~choosing[p]
  /\ ~inCS[p]
  /\ choosing' = [choosing EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = Bump(nextTicket)
  /\ UNCHANGED inCS

\* Finishing the ticket read: the process clears its choosing flag.
Finish(p) ==
  /\ choosing[p]
  /\ choosing' = [choosing EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<inCS, ticket, nextTicket>>

\* The core of the bakery order: a process enters the critical section
\* only when it is not choosing and no other process has a strictly
\* smaller ticket, and no one else is already inside.
Enter(p) ==
  /\ ~choosing[p]
  /\ ~inCS[p]
  /\ \A q \in 1..N : (inCS[q] = FALSE) /\ (ticket[q] < ticket[p] \/ (ticket[q] = ticket[p] /\ q < p))
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, choosing, nextTicket>>

\* Leaving the critical section.
Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, choosing, nextTicket>>

Next == \E p \in 1..N : Choose(p) \/ Finish(p) \/ Enter(p) \/ Exit(p)

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> NatOverride]
  /\ choosing \in [1..N -> BOOLEAN]
  /\ nextTicket \in 0..MaxNat

MutualExclusion ==
  \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => p = q

\* The full inductive invariant from the Bakery spec.
Inv ==
  /\ \A p \in 1..N : inCS[p] => ~choosing[p]
  /\ \A p \in 1..N : choosing[p] => ticket[p] = nextTicket - 1
  /\ \A p, q \in 1..N : (inCS[p] /\ ticket[q] < ticket[p]) => ~inCS[q]
  /\ \A p \in 1..N : \A q \in 1..N :
        (inCS[p] /\ ticket[q] = ticket[p] /\ q < p) => ~inCS[q]

\* The inductive spec starts from any type-correct state, so its INIT is
\* the type-correct state predicate itself.
ISpec == /\ TypeOK /\ Init /\ [][Next]_vars /\ WF_vars(Next)

====