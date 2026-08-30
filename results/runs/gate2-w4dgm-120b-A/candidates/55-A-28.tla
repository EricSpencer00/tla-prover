---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* Echo spanning tree over a fixed node set; the graph is fully meshed, which
\* satisfies connectivity, symmetry, and irreflexivity for all three nodes.
Neighbors(n) == { m \in Node : m # n }

VARIABLES parent, sent, received, active
vars == << parent, sent, received, active >>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ sent \in SUBSET (Node \X Node)
    /\ received \in SUBSET (Node \X Node)
    /\ active \in BOOLEAN

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ sent = {}
    /\ received = {}
    /\ active = FALSE

Send(n, m) ==
    /\ parent[n] = NoNode
    /\ m \in Neighbors(n)
    /\ << n, m >> \notin sent
    /\ sent' = sent \cup {<< n, m >>}
    /\ UNCHANGED << parent, received, active >>

Deliver(n, m) ==
    /\ << n, m >> \in sent
    /\ << n, m >> \notin received
    /\ parent[n] = NoNode
    /\ n # initiator
    /\ received' = received \cup {<< n, m >>}
    /\ UNCHANGED << parent, sent, active >>

SetParent(n, m) ==
    /\ << n, m >> \in received
    /\ parent[n] = NoNode
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ UNCHANGED << sent, received, active >>

Activate(n) ==
    /\ parent[n] = NoNode
    /\ received' = received \cup {<< n, n >>}
    /\ active' = TRUE
    /\ UNCHANGED << parent, sent >>

Next ==
    \/ \E n \in Node, m \in Node : Send(n, m)
    \/ \E n \in Node, m \in Node : Deliver(n, m)
    \/ \E n \in Node, m \in Node : SetParent(n, m)
    \/ \E n \in Node : Activate(n)

InitSpanningTree == Init

SpanningTreeStep ==
    \E n \in Node, m \in Node : Send(n, m) \/ Deliver(n, m) \/ SetParent(n, m)

Ancestor(m, n) ==
    IF n = m THEN TRUE
    ELSE IF parent[n] = NoNode THEN FALSE
    ELSE Ancestor(m, parent[n])

AncestorProperties ==
    /\ \A n \in Node \ {initiator} : Ancestor(initiator, n)
    /\ \A n \in Node : (parent[n] # NoNode) => (parent[n] # n)

AncestorsAreIrreflexive ==
    \A n \in Node : (~(n = initiator) /\ (parent[n] # NoNode)) => parent[n] # n

TestSpec == InitSpanningTree /\ [][SpanningTreeStep]_vars /\ AncestorProperties

====