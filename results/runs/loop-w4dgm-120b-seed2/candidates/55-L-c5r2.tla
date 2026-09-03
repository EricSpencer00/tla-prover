---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

TypeOK ==
  /\ R \subseteq (Node \X Node)
  /\ initiator \in Node
  /\ NoNode \notin Node

Graph ==
  {n \in Node : Cardinality({m \in Node : <<n, m>> \in R}) = Cardinality(Node) - 1}

Init ==
  /\ Graph
  /\ initiator \in Node
  /\ \A n \in Node : Cardinality({m \in Node : <<n, m>> \in R}) = Cardinality(Node) - 1

Spec == Init

\* Inherited from the Echo specification; included here for model checking.
AncestorProperties ==
  /\ initiator # NoNode
  /\ \A n \in Node : initiator # n => <<initiator, n>> \in R
  /\ \A a, b \in Node : (<<a, b>> \in R /\ <<b, a>> \in R) => a = b

Vars == {R initiator}

Init ==
  /\ R = {}
  /\ initiator \in Node

AddLink(a, b) ==
  /\ <<a, b>> \notin R
  /\ R' = R \cup {<<a, b>>}
  /\ UNCHANGED initiator

\* The Echo protocol's actions would go here; omitted for brevity.

Next ==
  \E a \in Node, b \in Node : AddLink(a, b)

Spec == Init /\ [][Next]_Vars

TestSpec == Spec /\ (\A n \in Node : Cardinality({m \in Node : <<n, m>> \in R}) = Cardinality(Node) - 1)

====