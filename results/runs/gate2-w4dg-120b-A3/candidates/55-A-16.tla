---- MODULE MCEcho ----
EXTENDS Naturals, Sequences

CONSTANTS Node, initiator, R, NoNode

\* N1, I1, and R1 are aliases the .cfg substitutes for the infinite versions
\* Node, initiator, and R, so they must exist here and mean exactly the same.
N1 == Node
I1 == initiator
R1 == R

ASSUME NoNode \notin Node
ASSUME initiator \in Node

\* A concrete 3-node fully-meshed graph; every unordered distinct pair is an edge.
Edges == {e \in [Node -> Node] : e \in [Node -> Node] /\ \A x \in Node : e[x] \in Node /\ e[x] # x}

VARIABLES parent, ready
vars == << parent, ready >>

Init ==
  /\ parent = [n \in Node |-> IF n = initiator THEN initiator ELSE NoNode]
  /\ ready = {}

Expect(n) == IF n = initiator THEN {} ELSE {n}

\* The Echo algorithm's actions, unmodified here.
EchoStep(n) ==
  /\ parent[n] = NoNode
  /\ \E m \in Node : [n = n /\ parent' = [parent EXCEPT ![n] = m]]
  /\ UNCHANGED ready

Ready(n) ==
  /\ parent[n] # NoNode
  /\ ready' = [ready EXCEPT ![n] = ready[n] \cup Expect(n)]
  /\ UNCHANGED parent

Acknowledge(n) ==
  /\ parent[n] # NoNode
  /\ parent' = [parent EXCEPT ![parent[n]] = parent[n]]
  /\ UNCHANGED ready

TestSpec ==
  /\ Init
  /\ UNCHANGED vars
  /\ PrintEdges

PrintEdges ==
  /\ Cardinality(Node) > 2
  /\ ~ \E e \in Edges : TRUE
  /\ Cardinality(Edges) = Cardinality(Node) * (Cardinality(Node) - 1)
  /\ Cardinality(R) = Cardinality(Node)
  /\ \A e \in Edges : Cardinality(e) = Cardinality(Node)

Next ==
  \/ \E n \in Node : EchoStep(n) \/ Ready(n) \/ Acknowledge(n)
  \/ PrintEdges

Spec == TestSpec /\ [][Next]_vars

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ ready \in [Node -> SUBSET Node]

AncestorProperties ==
  /\ \A n \in Node : initiator \in Expect^* n
  /\ \A a, b \in Node : (a # b /\ a \in Expect^* b) => b \notin Expect^* a

====