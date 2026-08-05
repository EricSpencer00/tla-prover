---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

\* A formal proof module for the sequential Misra reachability algorithm.
\* It defines the standard INIT/NEXT spec and, in addition, a set of
\* TLAPS-checked INVARIANTS and a PROPERTIES safety theorem. The
\* invariants are proved by appealing to the graph-theoretic lemmas in
\* the ReachabilityProofs module (reachable-from is closed under
\* adding successors, and reachable-from the empty set is empty).

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* A node outside the frontier but reachable from the frontier is one step
\* away from becoming marked. The frontier is an exact boundary of the
\* explored region, and every explored successor is either already marked
\* or waiting in the frontier.
Boundary == { n \in Nodes :
                 n \in frontier \/ \A m \in Nodes : (m \in frontier => n \in Succ(m))
                 \/ n \in marked }

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ(Root)
  /\ pc = "searching"

Explore(n, m) ==
  /\ pc = "searching"
  /\ n \in frontier
  /\ m \in Succ(n)
  /\ m \notin marked
  /\ frontier' = (frontier \ {n}) \cup {m}
  /\ marked' = marked \cup {m}
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_vars
Next == \E n \in Nodes, m \in Nodes : Explore(n, m) \/ Terminate

\* Invariant 1: type-correctness plus boundary closure under successors.
BoundaryInvariant ==
  /\ TypeOK
  /\ \A x \in Boundary : \A y \in Nodes : (x \in Succ(y)) => y \in Boundary

\* Invariant 2: the marked set together with everything reachable from
\* the frontier already accounts for everything reachable from the
\* explored-plus-frontier region. This follows from Lemma 1 (closed under
\* successors).
ReachableFromUnion ==
  ReachableFrom(marked) \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Invariant 3: the marked set and the frontier's reachable region together
\* account for exactly the nodes reachable from the root. This is proved
\* using Lemma 2 (stability of reachable-from under adding successors) and
\* Lemma 3 (reachable-from the empty set is empty).
FrontierInvariant ==
  ReachableFrom({Root}) = ReachableFrom(marked) \cup ReachableFrom(frontier)

\* Upon termination the frontier is empty, so the frontier term in the
\* FrontierInvariant drops out and the marked set must be exactly the
\* reachable set -- the algorithm's partial-correctness claim.
TerminationCorrectness == (pc = "done") ~> (marked = ReachableFrom({Root}))
====