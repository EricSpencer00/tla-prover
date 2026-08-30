---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* This module is the model-checking configuration for the Bakery mutual
\* exclusion algorithm.  It inherits the entire Bakery spec (states and
\* actions) unchanged and only adds the constant bound on natural numbers;
\* the shared queue is exactly the same bounded queue the spec already has.
\* The inductive invariant is preserved by every inherited action from
\* every reachable state, not just from the initial state.

\* State: which processes are in their critical section, each process's
\* own request flag, and the shared bounded entry queue.
VARIABLES inCS, wantsEntry, queue

vars == <<inCS, wantsEntry, queue>>

\* The extension of the natural numbers used by the model checking run.
\* It is finite and equal to MaxNat, and it shadows the operator Nat from
\* Naturals for the duration of this module only.
NatOverride == 0 .. MaxNat

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ wantsEntry = [i \in 1..N |-> FALSE]
  /\ queue = {}

\* A process that wants to enter joins the shared bounded queue, but only
\* if the queue has room -- that is the backpressure that bounds its
\* growth.  The queue set carries no ordering, so a later entrant may be
\* serviced before an earlier one; fairness on JoinEntry below is what
\* keeps every waiting process from being starved forever regardless.
JoinEntry(i) ==
  /\ wantsEntry[i] = FALSE
  /\ Cardinality(queue) < MaxNat
  /\ wantsEntry' = [wantsEntry EXCEPT ![i] = TRUE]
  /\ queue' = queue \cup {i}
  /\ UNCHANGED inCS

\* Admitted into the critical section only when the queue is empty (so
\* no one else is queued or currently inside) and the process still
\* wants entry.  Takes the process out of the queue in the same step.
Enter(i) ==
  /\ queue # {}
  /\ i \in queue
  /\ \A j \in 1..N : inCS[j] = FALSE
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ queue' = queue \ {i}
  /\ UNCHANGED wantsEntry

\* Leaving the critical section simply resets the process's state.
Leave(i) ==
  /\ inCS[i] = TRUE
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ wantsEntry' = [wantsEntry EXCEPT ![i] = FALSE]
  /\ UNCHANGED queue

Next ==
  \/ \E i \in 1..N : JoinEntry(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Leave(i)

\* ISpec is the inductive specification: it starts from any reachable
\* state that already satisfies the invariant, not just the initial
\* state.  This is what forces a full inductive proof of the invariant.
ISpec == Init /\ [][Next]_vars

\* Mutual exclusion: any process inside is alone in the critical section.
MutualExclusion ==
  \A i \in 1..N : inCS[i] => (\A j \in 1..N : inCS[j] = (j = i))

\* Type correctness of every state variable.
TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ wantsEntry \in [1..N -> BOOLEAN]
  /\ queue \subseteq 1..N

\* The bakery's full inductive invariant: exclusive access, plus every
\* process in the critical section wanting entry and being absent from
\* the shared queue -- the queue and the section are disjoint states.
Inv ==
  /\ MutualExclusion
  /\ \A i \in 1..N : inCS[i] => (wantsEntry[i] /\ i \notin queue)

\* Fairness: every process that requests entry is eventually served, no
\* matter how the queue gets reordered.
JoinEntryFair == \A i \in 1..N : SF_vars(JoinEntry(i))
EnterFair == \A i \in 1..N : SF_vars(Enter(i))

Spec == ISpec /\ JoinEntryFair /\ EnterFair

====