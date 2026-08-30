---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node /\ NoNode \notin Node

VARIABLES parent, echoCount, respond, round, graph
vars == <<parent, echoCount, respond, round, graph>>

InitState ==
    /\ parent = [n \in Node |-> NoNode]
    /\ echoCount = [n \in Node |-> 0]
    /\ respond = [n \in Node |-> FALSE]
    /\ round = 0
    /\ graph = {<<n1, n2>> \in Node \X Node : n1 # n2}

TestSpec == InitState /\ [][Next]_vars

Start(n) ==
    /\ round = 0
    /\ n = initiator
    /\ round' = 1
    /\ parent' = [parent EXCEPT ![n] = n]
    /\ UNCHANGED <<echoCount, respond, graph>>

Travel(a, b) ==
    /\ round = 1
    /\ <<a, b>> \in graph
    /\ parent[b] = NoNode
    /\ parent' = [parent EXCEPT ![b] = a]
    /\ UNCHANGED <<echoCount, respond, round, graph>>

Echo(b) ==
    /\ parent[b] # NoNode
    /\ parent[b] # b
    /\ respond[b] = FALSE
    /\ respond' = [respond EXCEPT ![b] = TRUE]
    /\ echoCount' = [echoCount EXCEPT ![parent[b]] = @ + 1]
    /\ UNCHANGED <<parent, round, graph>>

Quiesce ==
    /\ round = 1
    /\ \A n \in Node : parent[n] # NoNode => respond[n] = TRUE
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node : Start(n)
    \/ \E a \in Node, b \in Node : Travel(a, b)
    \/ \E b \in Node : Echo(b)
    \/ Quiesce

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ echoCount \in [Node -> 0 .. Cardinality(Node)]
    /\ respond \in [Node -> BOOLEAN]
    /\ round \in 0 .. 1
    /\ graph \subseteq Node \X Node

AncestorProperties ==
    /\ \A n \in Node : parent[n] # NoNode => (parent[n] = n \/ parent[n] \in Node)
    /\ \A n \in Node : parent[n] = n => n = initiator
    /\ \A n \in Node : parent[n] # NoNode /\ parent[n] # n => parent[n] \in Node
    /\ \A n \in Node : parent[n] # NoNode => parent[n] \in {m \in Node : <<m, n>> \in graph}

Spec == TestSpec
====