---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* A process ticket bounded below the overridden maximum; the override keeps
\* Nat finite so model checking stays in a bounded domain.
VARIABLES ticket, inCS, crashed, crashedBy

vars == <<ticket, inCS, crashed, crashedBy>>

Processes == 0..(N - 1)

Init ==
  /\ ticket = [p \in Processes |-> 0]
  /\ inCS = [p \in Processes |-> FALSE]
  /\ crashed = {}
  /\ crashedBy = [p \in Processes |-> 0]

\* A live process grabs the free lock and takes the next ticket.
Acquire(p) ==
  /\ p \notin crashed
  /\ \A q \in Processes : ~inCS[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = (ticket[p] + 1) % MaxNat]
  /\ UNCHANGED <<crashed, crashedBy>>

Release(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, crashed, crashedBy>>

Crash(p) ==
  /\ p \notin crashed
  /\ crashed' = crashed \cup {p}
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, crashedBy>>

\* A crashed process may be revived by another process, recorded.
Recover(p, q) ==
  /\ p \in crashed
  /\ p # q
  /\ crashed' = crashed \ {p}
  /\ crashedBy' = [crashedBy EXCEPT ![p] = q]
  /\ UNCHANGED <<ticket, inCS>>

Next =
  \/ \E p \in Processes : Acquire(p)
  \/ \E p \in Processes : Release(p)
  \/ \E p \in Processes : Crash(p)
  \/ \E p \in Processes, q \in Processes : Recover(p, q)

Spec == Init /\ [][Next]_vars

\* SAFETY: at most one process may hold the lock at once.
MutualExclusion == Cardinality({p \in Processes : inCS[p]}) <= 1

TypeOK ==
  /\ ticket \in [Processes -> 0..(MaxNat - 1)]
  /\ inCS \in [Processes -> BOOLEAN]
  /\ crashed \subseteq Processes
  /\ crashedBy \in [Processes -> Processes]

\* The full inductive invariant: mutual exclusion plus type correctness.
Inv == MutualExclusion /\ TypeOK

\* SAFETY: ticket numbers stay strictly below the overridden maximum.
TicketBound == \A p \in Processes : ticket[p] < MaxNat

====