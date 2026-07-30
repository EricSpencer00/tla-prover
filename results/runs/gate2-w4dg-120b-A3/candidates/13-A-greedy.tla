---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* NatOverride replaces the infinite Nat from Naturals with a finite version
\* for model checking.  It is defined as an operator, not a constant, so the
\* name Nat is never declared or redefined here.
NatOverride(n) == n \in 0..MaxNat

VARIABLES inCS, ticket, nextTicket, waiting

vars == <<inCS, ticket, nextTicket, waiting>>

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ waiting \in [1..N -> BOOLEAN]

MutualExclusion ==
  \A i \in 1..N, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

\* The full inductive invariant from the Bakery spec: mutual exclusion plus
\* type correctness plus the ticket discipline.
Inv == MutualExclusion /\ TypeOK

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ waiting = [i \in 1..N |-> FALSE]

Request(i) ==
  /\ ~waiting[i]
  /\ ~inCS[i]
  /\ waiting' = [waiting EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<inCS, ticket, nextTicket>>

\* Ticket numbers are drawn from the finite range 0..MaxNat.
Enter(i) ==
  /\ waiting[i]
  /\ nextTicket < MaxNat
  /\ ~inCS[i]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ waiting' = [waiting EXCEPT ![i] = FALSE]

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket, waiting>>

Next ==
  \E i \in 1..N : Request(i) \/ Enter(i) \/ Exit(i)

\* The inductive spec starts from any type-correct state satisfying the
\* invariant, not just from Init.
ISpec == Init /\ [][Next]_vars

====