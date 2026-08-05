---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, active, acked
vars == <<parent, active, acked>>

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ active = {initiator}
    /\ acked = {}

SendEcho(n, m) ==
    /\ n \in active
    /\ <<n, m>> \in R
    /\ parent[m] = NoNode
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ active' = active \cup {m}
    /\ UNCHANGED acked

Ack(m) ==
    /\ m \in active
    /\ \A k \in Node : <<m, k>> \in R => parent[k] # NoNode
    /\ acked' = acked \cup {m}
    /\ UNCHANGED <<parent, active>>

Quiesce ==
    /\ \A n \in Node : n \in acked
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node, m \in Node : SendEcho(n, m)
    \/ \E m \in Node : Ack(m)
    \/ Quiesce

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ active \subseteq Node
    /\ acked \subseteq Node

AncestorProperties ==
    /\ initiator \in acked
    /\ \A n \in Node : n # initiator => parent[n] # NoNode
    /\ \A n \in Node : (n \in acked /\ parent[n] # NoNode) => parent[n] \in acked
    /\ \A n \in Node : (parent[n] # NoNode) ~> (n \in acked)

PrintGraph ==
    LET show(S) == IF S = {} THEN "{}" ELSE "{" ^ (CHOOSE x \in S : TRUE) ^ "}"
    IN
        /\ ~ \E e \in R : TRUE
        /\ (PrintT("R: " ^ show(R)) /\ TRUE)

TestSpec == Spec \/ PrintGraph
====