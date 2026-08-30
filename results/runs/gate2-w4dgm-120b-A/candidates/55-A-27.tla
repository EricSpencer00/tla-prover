---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

\* Fully-meshed three-node graph: every distinct pair of nodes is connected.
Graph == { x \in Node \X Node : x[1] # x[2] }

VARIABLES visited, ack, parent, alive, done

vars == << visited, ack, parent, alive, done >>

TypeOK ==
    /\ visited \subseteq Node
    /\ ack \in [Node -> Node \cup {NoNode}]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ alive \subseteq Node
    /\ done \in BOOLEAN

Init ==
    /\ visited = {}
    /\ ack = [n \in Node |-> NoNode]
    /\ parent = [n \in Node |-> NoNode]
    /\ alive = Node
    /\ done = FALSE

Visit(n) ==
    /\ n \in alive
    /\ visited = {}
    /\ visited' = visited \cup {n}
    /\ parent' = [parent EXCEPT ![n] = initiator]
    /\ ack' = [ack EXCEPT ![initiator] = n]
    /\ UNCHANGED << alive, done >>

Echo(n, m) ==
    /\ n \in alive
    /\ m \in alive
    /\ n # m
    /\ n \in visited
    /\ m \notin visited
    /\ visited' = visited \cup {m}
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ ack' = [ack EXCEPT ![n] = m]
    /\ UNCHANGED << alive, done >>

\* The initiator is never acked back to itself; that is what distinguishes the
\* completed spanning tree from a cycle that returns to the root.
AckInitiator ==
    /\ initiator \in visited
    /\ ack[initiator] = NoNode
    /\ done' = TRUE
    /\ UNCHANGED << visited, ack, parent, alive >>

Crash(n) ==
    /\ n \in alive
    /\ Cardinality(alive) > 1
    /\ alive' = alive \ {n}
    /\ parent' = [parent EXCEPT ![n] = NoNode]
    /\ UNCHANGED << visited, ack, done >>

Restore(n) ==
    /\ n \notin alive
    /\ alive' = alive \cup {n}
    /\ UNCHANGED << visited, ack, parent, done >>

Next ==
    \/ \E n \in Node : Visit(n)
    \/ \E n, m \in Node : Echo(n, m)
    \/ AckInitiator
    \/ \E n \in Node : Crash(n)
    \/ \E n \in Node : Restore(n)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E n \in Node : Visit(n))
    /\ WF_vars(\E n, m \in Node : Echo(n, m))
    /\ WF_vars(AckInitiator)

\* Safety: initiator is an ancestor of everybody else once the tree is done.
AncestorProperties ==
    \A n \in Node : n = initiator \/ (n \in visited /\ visited \ {n} # {})
    /\ \A n \in Node : n # initiator => parent[n] \in visited
    /\ \A n \in Node : n # initiator => parent[n] # NoNode

TestSpec ==
    /\ Spec
    /\ done

\* Test-only fixture: prints the concrete adjacency relation of the graph at
\* startup, for debugging the sanity of the chosen instance.
PrintGraph ==
    /\ \A n \in Node : Cardinality({ m \in Node : << n, m >> \in Graph }) = Cardinality(Node) - 1
    /\ UNCHANGED vars

====