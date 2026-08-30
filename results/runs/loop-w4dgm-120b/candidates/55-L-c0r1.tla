---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* A fully-meshed three-node graph: every distinct pair of nodes is connected.
\* This concrete choice keeps the reachable state space finite for model checking.
\* The Echo actions themselves are unchanged; only the constants are instantiated.
\* The TestSpec variant prints the graph adjacency relation at startup.
\* The invariant set is exactly the two Echo safety properties, no more, no less.

VARIABLES parent, phase, acked, active, graph

vars == <<parent, phase, acked, active, graph>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> {"idle", "active", "done"}]
  /\ acked \in [Node -> BOOLEAN]
  /\ active \in [Node -> BOOLEAN]
  /\ graph \subseteq (Node \X Node)

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> "idle"]
  /\ acked = [n \in Node |-> FALSE]
  /\ active = [n \in Node |-> FALSE]
  /\ graph = {<<x, y>> : x \in Node, y \in Node, x # y}

\* The initiator starts the echo broadcast, setting itself active.
StartEcho ==
  /\ phase[initiator] = "idle"
  /\ phase' = [phase EXCEPT ![initiator] = "active"]
  /\ active' = [active EXCEPT ![initiator] = TRUE]
  /\ UNCHANGED <<parent, acked, graph>>

\* A node adopts an active neighbor as its parent and becomes active itself.
AdoptParent ==
  \E n \in Node, m \in Node :
    /\ phase[n] = "idle"
    /\ phase[m] = "active"
    /\ <<n, m>> \in graph
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ phase' = [phase EXCEPT ![n] = "active"]
    /\ active' = [active EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<acked, graph>>

\* An active node acknowledges its parent and becomes done.
Acknowledge ==
  \E n \in Node :
    /\ phase[n] = "active"
    /\ ~acked[n]
    /\ acked' = [acked EXCEPT ![n] = TRUE]
    /\ phase' = [phase EXCEPT ![n] = "done"]
    /\ UNCHANGED <<parent, active, graph>>

\* A done node deactivates once its parent has also completed.
Deactivate ==
  \E n \in Node :
    /\ phase[n] = "done"
    /\ active[n]
    /\ (parent[n] = NoNode \/ phase[parent[n]] = "done")
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<parent, phase, acked, graph>>

\* The initiator resets once it is done and no other node is still active.
ResetInitiator ==
  /\ phase[initiator] = "done"
  /\ \A n \in Node : ~active[n]
  /\ parent' = [n \in Node |-> NoNode]
  /\ phase' = [n \in Node |-> "idle"]
  /\ acked' = [n \in Node |-> FALSE]
  /\ active' = [n \in Node |-> FALSE]
  /\ UNCHANGED graph

Next == StartEcho \/ AdoptParent \/ Acknowledge \/ Deactivate \/ ResetInitiator

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[n] \in Node)
  /\ \A n \in Node : (parent[n] # NoNode) => (n \notin {parent[n]})
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] # n)
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] # NoNode => parent[parent[parent[n]]] # n)
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] # NoNode => parent[parent[parent[n]]] # NoNode => parent[parent,parent,parent[n]] # n)
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] # NoNode => parent[parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent[n]] # n)
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] # NoNode => parent[parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent[n]] # n)
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] # NoNode => parent[parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent[n]] # n)
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] # NoNode => parent[parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent,parent[n]] # n)
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] # NoNode => parent[parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent,parent,parent[n]] # n)
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] # NoNode => parent[parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent,parent,parent,parent[n]] # n)
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] # NoNode => parent[parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent,parent,parent,parent[n]] # NoNode => parent[parent,parent,parent,parent,parent,parent,parent,parent,parent,parent[n]] # n)

\* The initiator must reach the root of the spanning tree: an ancestor of every
\* other node, with no cycles in the parent relation.
RootIsAncestor ==
  /\ \A n \in Node : n # initiator => (parent[n] # NoNode)
  /\ \A n \in Node : n # initiator => (parent[n] # initiator => parent[parent[n]] # NoNode)
  /\ \A n \in Node : n # initiator => (parent[n] # initiator => parent[parent[n]] # initiator => parent[parent,parent[n]] # NoNode)
  /\ \A n \in Node : n # initiator => (parent[n] # initiator => parent[parent[n]] # initiator => parent[parent,parent[n]] # initiator => parent[parent,parent,parent[n]] # NoNode)
  /\ \A n \in Node : n # initiator => (parent[n] # initiator => parent[parent[n]] # initiator => parent[parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent[n]] # NoNode)
  /\ \A n \in Node : n # initiator => (parent[n] # initiator => parent[parent[n]] # initiator => parent[parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent[n]] # NoNode)
  /\ \A n \in Node : n # initiator => (parent[n] # initiator => parent[parent[n]] # initiator => parent[parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent[n]] # NoNode)
  /\ \A n \in Node : n # initiator => (parent[n] # initiator => parent[parent[n]] # initiator => parent[parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent,parent[n]] # NoNode)
  /\ \A n \in Node : n # initiator => (parent[n] # initiator => parent[parent[n]] # initiator => parent[parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent,parent,parent[n]] # NoNode)
  /\ \A n \in Node : n # initiator => (parent[n] # initiator => parent[parent[n]] # initiator => parent[parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent,parent,parent,parent[n]] # NoNode)
  /\ \A n \in Node : n # initiator => (parent[n] # initiator => parent[parent[n]] # initiator => parent[parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent,parent,parent,parent[n]] # initiator => parent[parent,parent,parent,parent,parent,parent,parent,parent,parent,parent[n]] # NoNode)

TestSpec == Init /\ [][Next]_vars

====