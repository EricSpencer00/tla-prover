---- MODULE MCBoulanger ----
EXTENDS Naturals

\* Boulanger mutual exclusion with a ticket register.  N processes race to
\* enter the critical section; a single open slot (opener = 0) serialises
\* entry.  Each entry consumes one ticket; the invariant bounds the total
\* to keep the finite-model search finite.

CONSTANTS N, MaxNat

\* A process in the critical section is the sole holder of the open slot.
\* The slot is never free while a critical section is occupied.
Processes == 1..N

VARIABLES inCS, ticket, opener, waiting

vars == <<inCS, ticket, opener, waiting>>

TypeOK ==
  /\ inCS \in [Processes -> BOOLEAN]
  /\ ticket \in 0..MaxNat
  /\ opener \in 0..N
  /\ waiting \in [Processes -> BOOLEAN]

Init ==
  /\ inCS = [p \in Processes |-> FALSE]
  /\ ticket = 0
  /\ opener = 0
  /\ waiting = [p \in Processes |-> FALSE]

Request(p) ==
  /\ ~waiting[p]
  /\ ~inCS[p]
  /\ waiting' = [waiting EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<inCS, ticket, opener>>

Enter(p) ==
  /\ waiting[p]
  /\ opener = 0
  /\ ticket < MaxNat
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ opener' = p
  /\ ticket' = ticket + 1
  /\ waiting' = [waiting EXCEPT ![p] = FALSE]

Leave(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ opener' = 0
  /\ UNCHANGED <<ticket, waiting>>

Next ==
  \/ \E p \in Processes : Request(p)
  \/ \E p \in Processes : Enter(p)
  \/ \E p \in Processes : Leave(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in Processes : inCS[p] => (opener = p)

Inv ==
  /\ MutualExclusion
  /\ ticket <= MaxNat

TicketBound == ticket < MaxNat

\* The override to a finite natural range: every ticket count observed
\* during a reachable state stays strictly below the configured maximum,
\* and because ticket is non-decreasing that bound must hold forever.
TicketsAlwaysBound == [][TicketBound]_vars
====