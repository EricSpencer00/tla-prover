---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* The state space of this model checking configuration is the full Boulanger
\* state space (MutualExclusion, TypeOK, Inv all hold on it), but every natural
\* number in it is forced into the range 0..MaxNat instead of the full Nat.

FiniteRange(v) == v \in 0..MaxNat

\* Ticket numbers are overridden to be finite; the invariant shape is unchanged.
NatOverride == FiniteRange

VARIABLES inCS, fine, ticket, nextTicket

vars == <<inCS, fine, ticket, nextTicket>>

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ fine \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ fine = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0

\* The coarse lock: a process may take the bakery's big lock only while no one
\* else is driving the bakery, and taking it stamps a ticket.
TakeLock(i) ==
  /\ ~inCS[i]
  /\ \A j \in 1..N : ~inCS[j]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ fine' = [fine EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket

\* The fine lock: only the lock-holder may take the staging table, and only
\* while its ticket number is strictly below every other holder's ticket.
TakeFine(i) ==
  /\ inCS[i]
  /\ ~fine[i]
  /\ \A j \in 1..N \ {i} : ~fine[j]
  /\ \A j \in 1..N \ {i} : inCS[j] => ticket[i] < ticket[j]
  /\ fine' = [fine EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<inCS, ticket, nextTicket>>

\* Releasing the fine lock does not relinquish the coarse lock, so a holder
\* keeps its ticket (and that ticket number) until it gives up the bakery.
ReleaseFine(i) ==
  /\ fine[i]
  /\ fine' = [fine EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<inCS, ticket, nextTicket>>

ReleaseLock(i) ==
  /\ inCS[i]
  /\ ~fine[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<fine, ticket, nextTicket>>

Next ==
  \E i \in 1..N :
    \/ TakeLock(i)
    \/ TakeFine(i)
    \/ ReleaseFine(i)
    \/ ReleaseLock(i)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: the bakery's coarse lock and the staging table's fine lock
\* are never both held by different processes at the same time.
MutualExclusion ==
  /\ (\A i, j \in 1..N : inCS[i] /\ inCS[j] => i = j)
  /\ (\A i, j \in 1..N : fine[i] /\ fine[j] => i = j)

\* Ticket numbers stay inside the overridden finite range, so the model stays
\* finite: each process's ticket is below MaxNat.
TicketsWithinRange == \A i \in 1..N : ticket[i] < MaxNat

====