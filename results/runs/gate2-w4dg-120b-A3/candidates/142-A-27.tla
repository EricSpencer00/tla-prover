---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* The algorithm's own stepwise definition, imported from the Reachable
\* module, is what drives the reachable set; this module only adds the
\* TLAPS-checked partial-correctness proofs.
Init == Reachable!Init

Next == Reachable!Next

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "scanning", "done"}

\* Every successor of a marked node is already marked or on the frontier.
MarkCoherent ==
  /\ TypeOK
  /\ \A x \in marked : \A y \in Nodes : (x \in marked /\ Edge(x, y)) => (y \in marked \/ y \in frontier)

\* Invariant 2 is proved as a corollary of the graph-theoretic Lemma 1
\* (predecessor closure of the frontier). It relates the marked set and
\* the frontier's reachable closure.
ReachFrontierClosure ==
  /\ TypeOK
  /\ ReachableFrom(marked) \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Invariant 3 uses Lemma 2 (ReachableFrom is closed under adding a
\* successor) and Lemma 3 (ReachableFrom of the empty set is empty); it
\* ties the marked set directly to the reachable set.
MarkingComplete ==
  /\ TypeOK
  /\ ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

Spec == Init /\ [][Next]_vars

INVARIANTS == <<MarkCoherent, ReachFrontierClosure, MarkingComplete>>

\* TLAPS checks the three invariants; no termination proof is attempted.
PROPERTIES == INVARIANTS
====