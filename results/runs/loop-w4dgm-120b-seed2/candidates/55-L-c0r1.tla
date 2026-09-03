---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

\* A test variant that prints the graph adjacency relation at startup.
PrintAdjacency == \E f \in [Node -> SUBSET Node] :
  /\ \A n \in Node : f[n] = Node \ {n}
  /\ \A n \in Node : Cardinality(f[n]) = Cardinality(Node) - 1
  /\ UNCHANGED <<>>

\* The Echo algorithm's state: parent links, the set of nodes that have
\* echoed, the set of nodes that have been visited, and the set of nodes
\* that have been sent a message.
VARIABLES parent, echoed, visited, sent

vars == <<parent, echoed, visited, sent>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ echoed \subseteq Node
  /\ visited \subseteq Node
  /\ sent \subseteq Node

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ echoed = {}
  /\ visited = {}
  /\ sent = {}

\* The initiator starts the spanning tree by sending a message to itself.
Send(n) ==
  /\ n = initiator
  /\ n \notin sent
  /\ sent' = sent \cup {n}
  /\ UNCHANGED <<parent, echoed, visited>>

\* A node that receives a message records its parent and marks itself visited.
Receive(n, m) ==
  /\ n \in sent
  /\ n \notin visited
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ visited' = visited \cup {n}
  /\ UNCHANGED <<echoed, sent>>

\* A visited node echoes back toward the initiator.
Echo(n) ==
  /\ n \in visited
  /\ n \notin echoed
  /\ echoed' = echoed \cup {n}
  /\ UNCHANGED <<parent, visited, sent>>

\* The initiator, once echoed, sends a message to every other node.
Broadcast(n) ==
  /\ n = initiator
  /\ n \in echoed
  /\ sent' = sent \cup (Node \ {n})
  /\ UNCHANGED <<parent, echoed, visited>>

\* A node that has echoed and been visited may send a message to any other node.
Relay(n, m) ==
  /\ n \in echoed
  /\ n \in visited
  /\ m \notin sent
  /\ sent' = sent \cup {m}
  /\ UNCHANGED <<parent, echoed, visited>>

\* Once every node has echoed, the initiator may reset the round.
Reset ==
  /\ \A n \in Node : n \in echoed
  /\ parent' = [n \in Node |-> NoNode]
  /\ echoed' = {}
  /\ visited' = {}
  /\ sent' = {}

Next ==
  \/ Reset
  \/ \E n \in Node : Send(n) \/ Echo(n) \/ Broadcast(n)
  \/ \E n \in Node, m \in Node : Receive(n, m) \/ Relay(n, m)

\* Ancestor is the transitive closure of the parent relation.
Ancestor(n, m) ==
  \/ parent[m] = n
  \/ \E k \in Node : parent[m] = k /\ Ancestor(n, k)

AncestorProperties ==
  /\ \A n \in Node : n # initiator => parent[n] # NoNode
  /\ \A n \in Node : n # initiator => Ancestor(initiator, n)
  /\ \A n \in Node : parent[n] # NoNode => ~Ancestor(n, parent[n])

Spec == Init /\ [][Next]_vars

\* The .cfg file substitutes concrete finite sets for the abstract constants
\* (N1, I1, R1) so the model stays finite and exhaustive.
TestSpec == Spec /\ PrintAdjacency

====