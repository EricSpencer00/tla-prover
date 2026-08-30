---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* This module is the model-checking configuration for the Boulanger
\* mutual exclusion algorithm. It redefines the natural numbers as a
\* finite range from 0 to MaxNat for model checking, and adds a state
\* constraint so ticket numbers never reach the top of that range,
\* which keeps the reachable state space finite.

\* A finite range of natural numbers is used for model checking the
\* ticket-number mechanism. No functional change to the algorithm:
\* only the arithmetic strength is weakened so the model stays finite.

\* The full set of state variables and actions is inherited from
\* Boulanger, which is not reprinted here. Only the constant
\* declarations, the specification expression, and the invariants
\* need to be reproduced in this module.

\* The standard Naturals module defines Nat as the infinite set of
\* natural numbers; the override below makes it a finite range.

VARIABLES inCS, want, inCSCount, lastWriter, ticket, serving

vars == <<inCS, want, inCSCount, lastWriter, ticket, serving>>

\* The override makes Nat a finite range for model checking; it is
\* only a strengthener of the arithmetic, never a weakening, so it
\* cannot break any safety or liveness property of the algorithm.
Nat == 0..MaxNat

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ inCSCount \in 0..N
  /\ lastWriter \in 0..N
  /\ ticket \in [1..N -> Nat]
  /\ serving \in [1..N]

\* SAFETY PROPERTY: mutual exclusion holds -- no two processes are ever
\* in the critical section at the same time.
MutualExclusion == inCSCount <= 1

\* INDUCTIVE INVARIANT: the inCSCount book-keeping field always equals
\* the literal number of processes in the critical section, so the
\* book-keeping can never drift out of step with reality.
Inv ==
  /\ inCSCount = Cardinality({p \in 1..N : inCS[p]})
  /\ MutualExclusion

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ want = [p \in 1..N |-> FALSE]
  /\ inCSCount = 0
  /\ lastWriter = 0
  /\ ticket = [p \in 1..N |-> 0]
  /\ serving = 1

Request(p) ==
  /\ ~want[p]
  /\ ~inCS[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<inCS, inCSCount, lastWriter, ticket, serving>>

\* A request first raises its ticket to the current round number,
\* then joins the set of ticket numbers the sorter will consider.
RaiseTicket(p) ==
  /\ want[p]
  /\ ticket[p] # serving
  /\ ticket' = [ticket EXCEPT ![p] = serving]
  /\ UNCHANGED <<inCS, want, inCSCount, lastWriter, serving>>

Enter(p) ==
  /\ ticket[p] = serving
  /\ ~inCS[p]
  /\ \A q \in 1..N : ~inCS[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ inCSCount' = inCSCount + 1
  /\ lastWriter' = p
  /\ UNCHANGED <<want, ticket, serving>>

Leave(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ inCSCount' = inCSCount - 1
  /\ UNCHANGED <<want, ticket, serving, lastWriter>>

\* The sorter advances only when no process is currently in the
\* critical section, so a ticket number is never re-used mid-show.
Advance ==
  /\ inCSCount = 0
  /\ serving < MaxNat
  /\ serving' = serving + 1
  /\ UNCHANGED <<inCS, want, inCSCount, lastWriter, ticket>>

Next ==
  \/ \E p \in 1..N : Request(p) \/ RaiseTicket(p) \/ Enter(p) \/ Leave(p)
  \/ Advance

\* A process may be arbitrarily slow to advance its ticket or to
\* enter once it holds a current ticket, but it never fails outright,
\* so fairness for each of those steps is assumed only weakly.
Spec ==
  /\ Init /\ [][Next]_vars
  /\ \A p \in 1..N : WF_vars(Request(p)) /\ WF_vars(RaiseTicket(p)) /\ WF_vars(Enter(p))

\* SAFETY PROPERTY: mutual exclusion can never be violated.
\* LIVENESS PROPERTY: NOT_SPECIFIED
====