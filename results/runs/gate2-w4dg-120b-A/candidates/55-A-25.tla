---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS
    Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES
    parent, echoSeen, ackSeen, sentActive, recvdActive

vars == <<parent, echoSeen, ackSeen, sentActive, recvdActive>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ echoSeen \subseteq Node
    /\ ackSeen \subseteq Node
    /\ sentActive \subseteq [from : Node, to : Node]
    /\ recvdActive \subseteq [from : Node, to : Node]

Ancestor(x, y) ==
    IF x = y THEN TRUE
    ELSE IF parent[y] = NoNode THEN FALSE
    ELSE Ancestor(x, parent[y])

AncestorProperties ==
    /\ parent[initiator] = NoNode
    /\ \A n \in Node : n # initiator => parent[n] # NoNode
    /\ \A n \in Node : n # initiator => Ancestor(initiator, n)
    /\ \A x, y \in Node : (x # y /\ parent[y] = x) => ~Ancestor(y, x)

Init ==
    /\ parent = [n \in Node |-> IF n = initiator THEN NoNode ELSE initiator]
    /\ echoSeen = {initiator}
    /\ ackSeen = {}
    /\ sentActive = {}
    /\ recvdActive = {}

SendEcho(n, m) ==
    /\ parent[m] = n
    /\ sentActive' = sentActive \cup {[from |-> n, to |-> m]}
    /\ UNCHANGED <<parent, echoSeen, ackSeen, recvdActive>>

RecvEcho(n, m) ==
    /\ [from |-> n, to |-> m] \in sentActive
    /\ recvdActive' = recvdActive \cup {[from |-> n, to |-> m]}
    /\ echoSeen' = echoSeen \cup {m}
    /\ sentActive' = sentActive \ {[from |-> n, to |-> m]}
    /\ UNCHANGED <<parent, ackSeen>>

SendAck(m, n) ==
    /\ [from |-> m, to |-> n] \in recvdActive
    /\ ackSeen' = ackSeen \cup {n}
    /\ recvdActive' = recvdActive \ {[from |-> m, to |-> n]}
    /\ UNCHANGED <<parent, echoSeen, sentActive>>

Next ==
    \/ \E n, m \in Node : SendEcho(n, m)
    \/ \E n, m \in Node : RecvEcho(n, m)
    \/ \E m, n \in Node : SendAck(m, n)

Spec == Init /\ [][Next]_vars

PrintGraph ==
    /\ Cardinality(Node) = 3
    /\ Cardinality(R) = 6
    /\ \A n \in Node : Cardinality({m \in Node : <<n, m>> \in R}) = 2
    /\ UNCHANGED vars

TestSpec == Spec /\ PrintGraph

====