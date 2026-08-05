---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, found, top, visited, Q, traversed

vars == <<parent, found, top, visited, Q, traversed>>

RECURSIVE Reachable(_)
Reachable(x) == {x} \cup UNION {Reachable(p) : p \in {y \in Node : parent[y] = x}}

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ found \in [Node -> BOOLEAN]
    /\ top \in Node
    /\ visited \in SUBSET Node
    /\ Q \in SUBSET Node
    /\ traversed \in SUBSET R

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ found = [n \in Node |-> FALSE]
    /\ top = initiator
    /\ visited = {initiator}
    /\ Q = {}
    /\ traversed = {}

StartExplore(n) ==
    /\ n \notin visited
    /\ parent' = [parent EXCEPT ![n] = top]
    /\ visited' = visited \cup {n}
    /\ Q' = Q \cup {n}
    /\ UNCHANGED <<found, top, traversed>>

ReceiveAck(n) ==
    /\ n \in Q
    /\ ~found[n]
    /\ found' = [found EXCEPT ![n] = TRUE]
    /\ Q' = Q \ {n}
    /\ UNCHANGED <<parent, top, visited, traversed>>

Propagate(n, m) ==
    /\ n \in Q
    /\ <<n, m>> \in R
    /\ m \notin visited
    /\ StartExplore(m)
    /\ UNCHANGED <<found, top, visited, Q, traversed>>

AckNow(n) ==
    /\ found[n]
    /\ top' = n
    /\ traversed' = traversed \cup {{n, top}}
    /\ UNCHANGED <<parent, found, visited, Q>>

Done ==
    /\ Q = {}
    /\ \A n \in Node : found[n]
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node : StartExplore(n)
    \/ \E n \in Node : ReceiveAck(n)
    \/ \E n \in Node, m \in Node : Propagate(n, m)
    \/ \E n \in Node : AckNow(n)
    \/ Done

Spec == Init /\ [][Next]_vars

AncestorProperties ==
    /\ initiator \in Reachable(initiator)
    /\ \A n \in Node : n # initiator => initiator \in Reachable(n)
    /\ \A n1, n2 \in Node :
        (n1 \in Reachable(n2) /\ n2 \in Reachable(n1)) => n1 = n2

TestSpec ==
    /\ Spec
    /\ Traversal == UNION {Reachable(n) : n \in Node}

====