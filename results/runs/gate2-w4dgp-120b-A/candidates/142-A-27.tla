---- MODULE ReachableProofs ----
EXTENDS Naturals
CONSTANTS Nodes, Root
ASSUME Root \in Nodes

\* Type-correctness plus closure of the marked set under taking successors.
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ /\ \A x \in Marked : \A y \in Nodes : (x, y) \in Edge => y \in Marked \cup Frontier
     /\ \A x \in Frontier : \A y \in Nodes : (x, y) \in Edge => y \in Marked \cup Frontier

\* Lemma 1: reachable-from distributes over a union of a reachable set and another set.
ReachUnion ==
  \A S, T \subseteq Nodes :
    reachableFrom(Root, S \cup T) = reachableFrom(Root, S) \cup reachableFrom(Root \cup reachableFrom(Root, S), T)

\* Lemma 2: reachable-from is unchanged if the source set is expanded by successors.
ReachStep == reachableFrom(Root, Marked \cup Frontier) = reachableFrom(Root, Marked)

\* Lemma 3: reachable-from the empty set is empty.
ReachEmpty == reachableFrom(Root, {}) = {}

\* Invariant 1: type-correctness plus closure under successors.
Inv1 == TypeOK

\* Invariant 2: the marked set plus reachable-from-Frontier is exactly reachable-from-marked-union-Frontier.
Inv2 == Marked \cup reachableFrom(Root, Frontier) = reachableFrom(Root, Marked \cup Frontier)

\* Invariant 3: the reachable nodes from the root equal the marked set plus reachable-from-Frontier.
Inv3 == reachableFrom(Root, Nodes) = Marked \cup reachableFrom(Root, Frontier)

Spec == Init /\ Next
PROPERTIES == Inv1 /\ Inv2 /\ Inv3
====