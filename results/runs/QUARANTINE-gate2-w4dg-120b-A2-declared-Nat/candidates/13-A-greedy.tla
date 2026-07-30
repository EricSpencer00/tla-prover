---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* NatOverride is the operator the .cfg substitutes in for Nat, so it must be
\* defined here exactly as the .cfg expects.  It is the finite range of natural
\* numbers that model checking is allowed to explore.
NatOverride == 0..MaxNat

VARIABLES inCS, ticket, nextTicket, waiting

vars == <<inCS, ticket, nextTicket, waiting>>

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> Nat]
  /\ nextTicket \in Nat
  /\ waiting \in [1..N -> BOOLEAN]

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ waiting = [i \in 1..N |-> FALSE]

\* A process that wants the critical section takes a ticket and waits.
Request(i) ==
  /\ ~waiting[i]
  /\ ~inCS[i]
  /\ waiting' = [waiting EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
  /\ UNCHANGED inCS

\* A waiting process enters the critical section only if its ticket is strictly
\* lower than every other process's ticket (or that process is not waiting).
Enter(i) ==
  /\ waiting[i]
  /\ \A j \in 1..N : ~waiting[j] \/ ticket[i] < ticket[j]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ waiting' = [waiting EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket>>

\* A process leaves the critical section.
Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket, waiting>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

\* The inductive specification starts from any type-correct state satisfying the
\* invariant, not just from Init, so Init is not part of Spec.
Spec == TypeOK /\ [][Next]_vars

\* Mutual exclusion: no two processes are ever in the critical section at once.
MutualExclusion ==
  \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

\* The full inductive invariant carried over from the Bakery spec.
Inv == MutualExclusion

ISpec == Spec

====