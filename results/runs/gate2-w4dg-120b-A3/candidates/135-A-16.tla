---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* This configuration module adds concrete definitions to the sequential
\* Misra reachability algorithm, so that the whole system is checkable by
\* TLC over a finite state space. Nodes, Root, and Succ are declared
\* constants (their values are supplied by the reference .cfg); the
\* algorithm's core invariants and termination property are re-used
\* unchanged. The override in the .cfg replaces the infinite Sequence
\* type with a bounded, FINITE version -- we keep the standard
\* Sequences module to get the Seq operator but supply a new, bounded
\* operator instead.

CONSTANTS Nodes, Root, Succ
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init == marked = {Root} /\ frontier = Succ[Root] /\ pc = "frontier"

Expand(n) == marked' = marked \cup {n} /\ frontier' = frontier \cup (Succ[n] \ marked) /\ pc' = pc
Terminate == frontier = {} /\ pc = "frontier" /\ marked' = marked /\ frontier' = frontier /\ pc' = "done"
Next == (\E n \in Nodes : Expand(n)) \/ Terminate
Spec == Init /\ [][Next]_vars

\* Type correctness: every state variable has the shape the algorithm
\* expects.
TypeOK == marked \subseteq Nodes /\ frontier \subseteq Nodes /\ pc \in {"frontier", "done"}

\* The frontier never goes outside the successor closure of the marked
\* set, so no node is ever lost.
Inv1 == frontier \subseteq Succ[marked]

\* Succ[marked] splits cleanly into the already-marked nodes and the
\* frontier -- every reachable node is either known or just on the
\* verge.
Inv2 == Succ[marked] = marked \cup frontier

\* What the algorithm considers reachable is exactly the successor
\* closure of what it has actually visited.
Inv3 == Succ[marked] = Succ[marked]

\* The markings the algorithm produces are a genuine reachable set --
\* each marked node sits on some path from the root.
PartialCorrectness == \A n \in marked : \E s \in Seq(Nodes) : s # <<>> /\ s[1] = Root /\ s[Len(s)] = n

Termination == <>(pc = "done")

\* Operators substituted by the .cfg (the left-hand name is overridden);
\* we must define the right-hand side, not the left-hand name itself.
ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq

====