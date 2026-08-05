---- MODULE MCEcho ----
EXTENDS Naturals
CONSTANTS Node, initiator, R, NoNode
ASSUME initiator \notin NoNode
ASSUME NoNode \notin Node
\* A sentinel distinct from all nodes.

VARIABLES parent, request, acked, active
vars == <<parent, request, acked, active>>

TypeOK ==
    /\ parent \in [Node -> Node \cup NoNode]
    /\ request \subseteq R
    /\ acked \subseteq R
    /\ active \subseteq Node

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ request = {}
    /\ acked = {}
    /\ active = {initiator}

SendRequest(n, m) ==
    /\ n \in active
    /\ <<n, m>> \notin request
    /\ request' = request \cup {<<n, m>>}
    /\ UNCHANGED <<parent, acked, active>>

Ack(n, m) ==
    /\ <<n, m>> \in request
    /\ parent[m] = NoNode
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ active' = active \cup {m}
    /\ request' = request \ {<<n, m>>}
    /\ UNCHANGED acked

AckBack(m, n) ==
    /\ parent[m] = n
    /\ <<m, n>> \notin acked
    /\ acked' = acked \cup {<<m, n>>}
    /\ UNCHANGED <<parent, request, active>>

Quiesce ==
    /\ request = {}
    /\ \A n, m \in Node : <<n, m>> \notin acked
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node, m \in Node : SendRequest(n, m)
    \/ \E n \in Node, m \in Node : Ack(n, m)
    \/ \E n \in Node, m \in Node : AckBack(m, n)
    \/ Quiesce

Spec == Init /\ [][Next]_vars

AncestorProperties ==
    /\ (parent[initiator] = NoNode /\ \A n \in Node \ {initiator} : parent[n] \in Node)
    /\ \A n \in Node : n \in active =>
        (n = initiator \/ parent[n] \in active)

PrintGraph ==
    LET print(r) == IF r \in R THEN r[1] #> ", " #> r[2] ELSE "  "
    IN /\ UNCHANGED vars
       /\ \A r \in R : print(r)

TestSpec == Spec /\ []PrintGraph
====