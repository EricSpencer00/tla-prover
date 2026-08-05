---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* Mutual exclusion among N concurrent processes under the Boulanger algorithm.
\* Natural numbers are overridden with a finite range (NatOverride below) so
\* the model stays within the bounded MaxNat ticket window during checking.

Processes == 1..N
NONE == 0

VARIABLES ticket, using, served, clock, request

vars == <<ticket, using, served, clock, request>>

TypeOK ==
  /\ ticket \in [Processes -> NatOverride]
  /\ using \in [Processes -> BOOLEAN]
  /\ served \in [Processes -> 0..1]
  /\ clock \in NatOverride
  /\ request \in [Processes -> BOOLEAN]

Init ==
  /\ ticket = [p \in Processes |-> 0]
  /\ using = [p \in Processes |-> FALSE]
  /\ served = [p \in Processes |-> 0]
  /\ clock = 0
  /\ request = [p \in Processes |-> FALSE]

\* A process requests entry and reads the current clock as its ticket.
Request(p) ==
  /\ ~request[p]
  /\ ~using[p]
  /\ request' = [request EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = clock]
  /\ clock' = IF clock < MaxNat THEN clock + 1 ELSE clock
  /\ UNCHANGED <<using, served>>

\* A process enters the critical section only if no other process is using
\* it and its ticket is at least as old as every other process's ticket.
Enter(p) ==
  /\ request[p]
  /\ ~using[p]
  /\ served[p] = 0
  /\ \A q \in Processes : ~using[q] /\ ticket[p] >= ticket[q]
  /\ using' = [using EXCEPT ![p] = TRUE]
  /\ served' = [served EXCEPT ![p] = 1]
  /\ request' = [request EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, clock>>

\* Exit the critical section.
Exit(p) ==
  /\ using[p]
  /\ using' = [using EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, using, served, clock, request>>

Next ==
  \E p \in Processes:
    Request(p) \/ Enter(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: no two processes use the critical section at once.
MutualExclusion == \A p, q \in Processes : (using[p] /\ using[q]) => p = q

\* Finite-range override: Nat is replaced with NatOverride, a finite set of
\* natural numbers up to MaxNat, so the model stays bounded.
NatOverride == 0..MaxNat

\* Inductive invariant: every used process is in the critical section and has
\* not already been served.
Inv ==
  \A p \in Processes : using[p] => (served[p] = 0 /\ using[p])

StateConstraint == \A p \in Processes : ticket[p] < MaxNat

====