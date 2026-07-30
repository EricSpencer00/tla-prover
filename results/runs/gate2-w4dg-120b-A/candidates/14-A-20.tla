---- MODULE MCBoulanger ----
EXTENDS Integers, FiniteSets

CONSTANTS N, MaxNat

\* Nat is the finite set that replaces the infinite natural numbers
\* during model checking.
Nat == 0..MaxNat

VARIABLES pc, ticket, next
vars == <<pc, ticket, next>>

TypeOK ==
  /\ pc \in [1..N -> {"idle", "trying", "critical"}]
  /\ ticket \in [1..N -> Nat]
  /\ next \in Nat

Init ==
  /\ pc = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ next = 0

Request(p) ==
  /\ pc[p] = "idle"
  /\ next < MaxNat
  /\ pc' = [pc EXCEPT ![p] = "trying"]
  /\ ticket' = [ticket EXCEPT ![p] = next]
  /\ next' = next + 1

Enter(p) ==
  /\ pc[p] = "trying"
  /\ \A q \in 1..N : (pc[q] = "critical") => (ticket[p] < ticket[q])
  /\ pc' = [pc EXCEPT ![p] = "critical"]
  /\ UNCHANGED <<ticket, next>>

Exit(p) ==
  /\ pc[p] = "critical"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<ticket, next>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: at most one process is in the critical section.
MutualExclusion == Cardinality({p \in 1..N : pc[p] = "critical"}) <= 1

\* The inductive invariant from the Boulanger specification.
Inv == /\ MutualExclusion
       /\ TypeOK

\* Ticket numbers stay strictly below the configured maximum; this state
\* constraint is what makes the finite Nat set safe to explore.
StateConstraint == \A p \in 1..N : ticket[p] < MaxNat

====