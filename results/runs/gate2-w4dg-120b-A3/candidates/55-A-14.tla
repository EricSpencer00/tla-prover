---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Node, initiator, R, NoNode

CONSTANTS N1, I1, R1

ASSUME N1 = Node /\ I1 = initiator /\ R1 = R

Nodes == Node

VARIABLES parent, done, echoCount

vars == <<parent, done, echoCount>>

TypeOK ==
    /\ parent \in [Nodes -> Nodes \cup {NoNode}]
    /\ done \subseteq Nodes
    /\ echoCount \in [Nodes -> 0..Cardinality(Nodes)]

Init ==
    /\ parent = [n \in Nodes |-> IF n = initiator THEN NoNode ELSE initiator]
    /\ done = {}
    /\ echoCount = [n \in Nodes |-> 0]

SendEcho(n) ==
    /\ n \notin done
    /\ echoCount[n] < Cardinality(Nodes)
    /\ echoCount' = [echoCount EXCEPT ![n] = echoCount[n] + 1]
    /\ \E m \in Nodes \ {{n}} :
         /\ <<n, m>> \in R
         /\ parent[m] = n
         /\ done' = done \cup {m}
    /\ UNCHANGED parent

Quiesce ==
    /\ \A n \in Nodes : n \in done
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : SendEcho(n)
    \/ Quiesce

Spec == Init /\ [][Next]_vars

TestSpec == Spec

AncestorProperties ==
    /\ \A n \in Nodes \ {initiator} : parent[n] # NoNode
    /\ \A n \in Nodes \ {initiator} : parent[n] # n
    /\ \A n1, n2 \in Nodes :
         (parent[n1] = n2) => (parent[n2] # n1)

====