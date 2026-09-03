---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* Fully meshed three-node graph: every distinct pair of nodes is connected.
Connected == { <<x, y>> \in Node \X Node : x # y }

VARIABLES origin, alive, active, parent, done, beacon

vars == <<origin, alive, active, parent, done, beacon>>

TypeOK ==
    /\ origin \subseteq Node
    /\ alive \subseteq Node
    /\ active \subseteq [Node -> Node \cup {NoNode}]
    /\ parent \subseteq [Node -> Node \cup {NoNode}]
    /\ done \subseteq Node
    /\ beacon \in 0..R

Init ==
    /\ origin = {initiator}
    /\ alive = Node
    /\ active = [n \in Node |-> IF n = initiator THEN initiator ELSE NoNode]
    /\ parent = [n \in Node |-> NoNode]
    /\ done = {}
    /\ beacon = 0

\* The initiator starts the tree, and any active node may add a fresh node as a child.
Activate(m, n) ==
    /\ m \in alive
    /\ active[m] # NoNode
    /\ n \in alive
    /\ n \notin origin
    /\ origin' = origin \cup {n}
    /\ active' = [active EXCEPT ![n] = n]
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ UNCHANGED <<origin, alive, done, beacon>>

\* A node already in the tree may join a different active node as a second parent.
Rejoin(m, n) ==
    /\ m \in alive
    /\ active[m] # NoNode
    /\ n \in origin
    /\ n \notin done
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ UNCHANGED <<origin, alive, active, done, beacon>>

Done(n) ==
    /\ n \in origin
    /\ n \notin done
    /\ done' = done \cup {n}
    /\ UNCHANGED <<origin, alive, active, parent, beacon>>

\* Slow-but-not-failed nodes: a node is never removed, only demoted from active.
Deactivate(n) ==
    /\ n \in active
    /\ n # initiator
    /\ active' = [active EXCEPT ![n] = NoNode]
    /\ UNCHANGED <<origin, alive, parent, done, beacon>>

Heartbeat ==
    /\ beacon' = (beacon + 1) % (R + 1)
    /\ UNCHANGED <<origin, alive, active, parent, done>>

Next ==
    \/ \E m \in Node, n \in Node : Activate(m, n)
    \/ \E m \in Node, n \in Node : Rejoin(m, n)
    \/ \E n \in Node : Done(n) \/ Deactivate(n)
    \/ Heartbeat

Ancestor(m, n) == (m = n) \/ (parent[n] # NoNode /\ Ancestor(m, parent[n]))

\* Safety: typing + the spanning tree shape: the initiator is an ancestor of everyone
\* and the ancestor relation is acyclic (no node is its own ancestor).
TreeOK ==
    /\ \A n \in Node : Cardinality(parent[n]) <= 1
    /\ \A n \in Node : initiator \in origin => Ancestor(initiator, n)
    /\ \A n \in Node : ~Ancestor(n, n)

AncestorProperties == TreeOK

TestSpec == Init /\ [][Next]_vars

====