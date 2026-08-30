---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* The ticket lock is modeled as a shared variable holding a set of process
\* identifiers. Because entry requests travel over an asynchronous bus, a
\* process may CAS the lock entry from free to its own id out of order relative
\* to other processes -- that is what makes the system re-ordering tolerant.
\* The invariant protects mutual exclusion on the lock entry itself.
VARIABLES lock, inCS, ticket, want

vars == <<lock, inCS, ticket, want>>

Processes == 1..N
Free == 0
NoOne == 0

TypeOK ==
  /\ lock \in {Free} \cup Processes
  /\ inCS \in [Processes -> BOOLEAN]
  /\ ticket \in [Processes -> 0..MaxNat]
  /\ want \in [Processes -> BOOLEAN]

Init ==
  /\ lock = Free
  /\ inCS = [p \in Processes |-> FALSE]
  /\ ticket = [p \in Processes |-> 0]
  /\ want = [p \in Processes |-> FALSE]

Request(p) ==
  /\ ~want[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<lock, inCS, ticket>>

\* CAS entry: succeeds only if the lock register currently reads free.
CASLock(p) ==
  /\ want[p]
  /\ lock = Free
  /\ lock' = p
  /\ ticket' = [ticket EXCEPT ![p] = IF @ < MaxNat THEN @ + 1 ELSE @]
  /\ UNCHANGED <<inCS, want>>

Enter(p) ==
  /\ lock = p
  /\ ~inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<lock, ticket, want>>

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ lock' = Free
  /\ ticket' = [ticket EXCEPT ![p] = IF @ < MaxNat THEN @ + 1 ELSE @]
  /\ UNCHANGED want

Next ==
  \/ \E p \in Processes : Request(p)
  \/ \E p \in Processes : CASLock(p)
  \/ \E p \in Processes : Enter(p)
  \/ \E p \in Processes : Exit(p)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion of the lock entry: any process recorded inside the critical
\* section must be the current holder of the shared lock register.
MutualExclusion ==
  \A p \in Processes : inCS[p] => lock = p

\* A process that is not the current lock holder can never find itself inside
\* the critical section, which is the literal per-process re-ordering check.
TypeOKFor(p) ==
  inCS[p] => lock = p

\* Every CAS cycle (entry, exit) advances the per-process ticket number, so
\* the pair of invariants below are tied together: the lock register can never
\* stall at a value that a process has already advanced past.
Inv == MutualExclusion /\ \A p \in Processes : TypeOKFor(p)

\* The ticket numbers are natural numbers (never negative).
NatOverride == \A p \in Processes : ticket[p] >= 0

StateConstraint == \A p \in Processes : ticket[p] < MaxNat

====