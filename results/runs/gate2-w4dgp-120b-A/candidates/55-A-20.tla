---- MODULE MCEcho ----
\* A model-checking configuration of the Echo spanning tree algorithm.
\* This module is deliberately small: a fully-meshed three-node graph.
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES visited, parent, recvCount, pending

vars == <<visited, parent, recvCount, pending>>

TypeOK ==
  /\ visited \in [Node -> BOOLEAN]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ recvCount \in [Node -> 0..Cardinality(Node)]
  /\ pending \in SUBSET (Node \X Node)

\* The initiator is the only node initially visited; others must be reached.
Init ==
  /\ visited = [n \in Node |-> n = initiator]
  /\ parent = [n \in Node |-> IF n = initiator THEN NoNode ELSE NoNode]
  /\ recvCount = [n \in Node |-> 0]
  /\ pending = {}

\* A visited node sends a discover/reply message to a neighbor; messages travel
\* asynchronously and arrive in any order.
Send ==
  /\ \E u, v \in Node :
       /\ u # v
       /\ u \in visited
       /\ <<u, v>> \notin pending
       /\ pending' = pending \cup {<<u, v>>}
  /\ UNCHANGED <<visited, parent, recvCount>>

\* A pending message is delivered; visiting a fresh node records the sender as
\* parent and acknowledges the receipt.
Recv ==
  /\ \E u, v \in Node :
       /\ <<u, v>> \in pending
       /\ visited' = [visited EXCEPT ![v] = TRUE]
       /\ parent' = [parent EXCEPT ![v] = u]
       /\ recvCount' = [recvCount EXCEPT ![v] = @ + 1]
       /\ pending' = pending \ {<<u, v>>}
  /\ UNCHANGED <<visited, parent, recvCount>>

\* A visited node may retry sending a message that was not delivered.
Retry ==
  /\ \E u, v \in Node :
       /\ <<u, v>> \in pending
       /\ visited[u]
       /\ u # v
       /\ pending' = pending \cup {<<u, v>>}
  /\ UNCHANGED <<visited, parent, recvCount>>

\* Traversal is complete once all nodes are visited and no messages remain
\* pending; at that point the system settles and the model checker may close.
Finish ==
  /\ \A n \in Node : visited[n]
  /\ pending = {}
  /\ UNCHANGED vars

Next == Send \/ Recv \/ Retry \/ Finish

Spec == Init /\ [][Next]_vars

\* Ancestor Properties: the initiator is the sole source of any visited node,
\* and the parent relation is acyclic.
AncestorProperties ==
  /\ \A n \in Node : visited[n] => (n = initiator \/ (parent[n] \in Node))
  /\ \A n \in Node : parent[n] = NoNode => n = initiator
  /\ \A n \in Node, k \in Nat :
       (k > 0 /\ parent[n] # NoNode) => (parent^[k][n] # n)

\* TestSpec is the version the .cfg runs: it prints the adjacency relation at
\* startup (a one-shot side effect, not a semantic action) and otherwise behaves
\* exactly like Spec.
TestSpec ==
  /\ Spec
  /\ \A u, v \in Node : IF (u = initiator) /\ (u # v) THEN PrintT(~u ~ " -> " ~ v) ELSE UNCHANGED vars

====