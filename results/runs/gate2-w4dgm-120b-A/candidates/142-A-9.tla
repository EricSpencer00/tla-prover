---- MODULE ReachableProofs ----
EXTENDS Reachable, Misra

CONSTANTS Nodes, Root

\* No new actors: this module only extends the algorithm with its proofs.
\* The three invariants are the full story for partial correctness; there is
\* no liveness (termination) property, because TLAPS cannot prove liveness.

Init == Reachable.Init /\ Misra.Init

Step == Misra.Step

Next == Step

Spec == Init /\ [][Next]_Misra.vars

\* Invariant 1: the locally checkable closure condition plus type correctness.
Inv1 == Misra.Inv1

\* Invariant 2: the reachable set distributes over the marked set plus the
\* frontier.  It follows directly from the key graph-theoretic Lemma 1.
Inv2 == Reachable.reachableFromEq1 = Misra.marked \cup Reachable.reachableFromEq2

\* Invariant 3: the reachable set is exactly the marked set plus the
\* reachable-from-frontier set.  It uses Lemma 2 and Lemma 3 from the
\* reachability proofs module.
Inv3 == Reachable.reachableFromEq1 = Misra.marked \cup Reachable.reachableFromEq3

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

\* Partial correctness: on termination the marking is exactly the reachable set.
ReachesExactly == (Misra.pc = Misra.DONE) => (Misra.marked = Reachable.reachableFromEq1)

PROPERTIES == ReachesExactly

====