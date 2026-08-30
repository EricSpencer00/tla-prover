---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES state, acked, parent, echoCount, graph

vars == <<state, acked, parent, echoCount, graph>>

TypeOK ==
    /\ state \in [Node -> {"init", "pending", "done"}]
    /\ acked \in [Node -> BOOLEAN]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ echoCount \in [Node -> 0..Cardinality(R)]
    /\ graph \subseteq (Node \X Node)

Init ==
    /\ state = [n \in Node |-> IF n = initiator THEN "pending" ELSE "init"]
    /\ acked = [n \in Node |-> FALSE]
    /\ parent = [n \in Node |-> IF n = initiator THEN NoNode ELSE initiator]
    /\ echoCount = [n \in Node |-> IF n = initiator THEN Cardinality(R) ELSE 0]
    /\ graph = (Node \X Node) \ {<<x, x>>}

SendEcho(n, m) ==
    /\ state[n] = "pending"
    /\ <<n, m>> \in graph
    /\ state[m] = "init"
    /\ state' = [state EXCEPT ![m] = "pending"]
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ echoCount' = [echoCount EXCEPT ![m] = Cardinality(R)]
    /\ UNCHANGED <<acked, graph>>

ReceiveAck(n) ==
    /\ echoCount[n] > 0
    /\ echoCount' = [echoCount EXCEPT ![n] = @ - 1]
    /\ UNCHANGED <<state, acked, parent, graph>>

Done(n) ==
    /\ state[n] = "pending"
    /\ echoCount[n] = 0
    /\ state' = [state EXCEPT ![n] = "done"]
    /\ acked' = [acked EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<parent, echoCount, graph>>

AllDone == \A n \in Node : state[n] = "done"

Next ==
    \/ \E n \in Node, m \in Node : SendEcho(n, m)
    \/ \E n \in Node : ReceiveAck(n)
    \/ \E n \in Node : Done(n)
    \/ (AllDone /\ UNCHANGED vars)

TestSpec == Init /\ [][Next]_vars

AncestorProperties ==
    /\ (\A n \in Node : n # initiator => parent[n] # NoNode)
    /\ (\A n \in Node : (n # initiator /\ parent[n] # NoNode) => ancestor(initiator, n))
    /\ (\A n, m, k \in Node :
            (parent[n] = m /\ parent[m] = k) => parent[n] # k

Ancestor(n, m) == n = m \/ (parent[m] # NoNode /\ Ancestor(n, parent[m]))

====