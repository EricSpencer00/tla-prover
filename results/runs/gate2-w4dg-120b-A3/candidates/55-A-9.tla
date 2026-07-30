---- MODULE MCEcho ----
EXTENDS Naturals

\* Model checking configuration for the Echo algorithm: a concrete
\* three-node fully-meshed graph, with a test variant that prints the
\* adjacency relation.
CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, children, phase, echo, maxDepth
vars == <<parent, children, phase, echo, maxDepth>>

\* Deterministic three-node fully-meshed graph (every pair of distinct
\* nodes is adjacent); initiator is chosen deterministically.
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<<x, y>> : x \in N1 /\ y \in N1 /\ x # y}

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ phase \in [Node -> {"init", "sent", "replied"}]
  /\ echo \in [Node -> Node]
  /\ maxDepth \in Nat

Init ==
  /\ parent = [x \in Node |-> NoNode]
  /\ children = [x \in Node |-> {}]
  /\ phase = [x \in Node |-> "init"]
  /\ echo = [x \in Node |-> "n1"]
  /\ maxDepth = 0

SendEcho(x, y) ==
  /\ x # y
  /\ phase[x] = "init"
  /\ phase' = [phase EXCEPT ![x] = "sent"]
  /\ parent' = [parent EXCEPT ![x] = y]
  /\ children' = [children EXCEPT ![y] = @ \cup {x}]
  /\ UNCHANGED <<echo, maxDepth>>

Reply(x) ==
  /\ x # initiator
  /\ phase[x] = "sent"
  /\ \A c \in children[x] : phase[c] = "replied"
  /\ echo' = [echo EXCEPT ![x] = echo[parent[x]]]
  /\ maxDepth' = IF maxDepth < Cardinality(children[x]) THEN Cardinality(children[x]) ELSE maxDepth
  /\ phase' = [phase EXCEPT ![x] = "replied"]
  /\ UNCHANGED <<parent, children>>

InitReply ==
  /\ phase[initiator] = "init"
  /\ \A c \in children[initiator] : phase[c] = "replied"
  /\ phase' = [phase EXCEPT ![initiator] = "replied"]
  /\ UNCHANGED <<parent, children, echo, maxDepth>>

Next ==
  \/ \E x \in Node, y \in Node : SendEcho(x, y)
  \/ \E x \in Node : Reply(x)
  \/ InitReply

Spec == Init /\ [][Next]_vars

\* Ancestor relation: the initiator is an ancestor of every other node
\* and no node is its own ancestor (acyclicity).
Ancestor(x) == {y \in Node : (x = initiator \/ x \in Ancestor(parent[y])) /\ parent[y] # NoNode}
AncestorProperties ==
  /\ \A x \in Node : x # initiator => initiator \in Ancestor(x)
  /\ \A x \in Node : x \notin Ancestor(x)

\* Test variant: prints the adjacency relation to the console.
TestSpec == Spec /\ (Print("\nAdjacency relation:\n") /\ Print(R))

\* The .cfg file substitutes these finite instances for the constants.
N1 == N1
I1 == I1
R1 == R1

====