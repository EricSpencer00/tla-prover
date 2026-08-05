---- MODULE MCEcho ----
EXTENDS Naturals

\* MC stands for Model-Checking configuration: a fully meshed 3-node graph
\* of the Echo spanning tree protocol, specialized enough to be explored
\* exhaustively by TLC.

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, sender, visited, messages

vars == <<parent, sender, visited, messages>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ sender \in [Node -> Node \cup {NoNode}]
  /\ visited \in [Node -> BOOLEAN]
  /\ messages \subseteq [from: Node, to: Node]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ sender = [n \in Node |-> NoNode]
  /\ visited = [n \in Node |-> FALSE]
  /\ messages = {}

Send(n, m) ==
  /\ n # m
  /\ <<n, m>> \notin messages
  /\ messages' = messages \cup {<<n, m>>}
  /\ UNCHANGED <<parent, sender, visited>>

Deliver(n, m) ==
  /\ <<n, m>> \in messages
  /\ ~ visited[m]
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ sender' = [sender EXCEPT ![m] = n]
  /\ visited' = [visited EXCEPT ![m] = TRUE]
  /\ messages' = messages \ {<<n, m>>}

Idle == UNCHANGED vars

Next ==
  \/ \E n \in Node, m \in Node : Send(n, m)
  \/ \E n \in Node, m \in Node : Deliver(n, m)
  \/ Idle

Spec == Init /\ [][Next]_vars

\* The spanning tree rooted at the initiator covers all nodes and has no
\* cycles (no node is its own ancestor).
Ancestor ==
  LET a(n) == IF parent[n] = NoNode THEN {} ELSE {parent[n]} \cup a(parent[n])
  IN {n \in Node : initiator \notin a(n)}

PrintAdjacency ==
  /\ UNCHANGED vars
  /\ ~ \E x \in Node : <<NoNode, NoNode>> \in messages
  /\ \E x \in Node : messages' = messages \cup {<<NoNode, NoNode>>}
  /\ \A n \in Node : PrintS(SUPERSET(R, {n}))

====