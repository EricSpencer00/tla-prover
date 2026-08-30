---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES acked, parent, phase, echoNum, echoFrom, adj

vars == <<acked, parent, phase, echoNum, echoFrom, adj>>

TypeOK ==
    /\ acked \subseteq Node
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ phase \in [Node -> {"initing", "echoing", "done"}]
    /\ echoNum \in [Node -> Nat]
    /\ echoFrom \in [Node -> Node \cup {NoNode}]
    /\ adj \subseteq (Node \X Node)

Init ==
    /\ acked = {}
    /\ parent = [n \in Node |-> NoNode]
    /\ phase = [n \in Node |-> "initing"]
    /\ echoNum = [n \in Node |-> 0]
    /\ echoFrom = [n \in Node |-> NoNode]
    /\ adj = (Node \X Node) \ {<<n, n>> : n \in Node}

Begin(n) ==
    /\ phase[n] = "initing"
    /\ (n = initiator \/ n \in acked)
    /\ phase' = [phase EXCEPT ![n] = "echoing"]
    /\ UNCHANGED <<acked, parent, echoNum, echoFrom, adj>>

Echo(n, m) ==
    /\ phase[n] = "echoing"
    /\ <<n, m>> \in adj
    /\ n # m
    /\ parent[m] = NoNode
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ echoNum' = [echoNum EXCEPT ![m] = @ + 1]
    /\ echoFrom' = [echoFrom EXCEPT ![m] = n]
    /\ UNCHANGED <<acked, phase, adj>>

Ack(m) ==
    /\ parent[m] # NoNode
    /\ m \notin acked
    /\ acked' = acked \cup {m}
    /\ UNCHANGED <<parent, phase, echoNum, echoFrom, adj>>

Done(n) ==
    /\ phase[n] = "echoing"
    /\ n \in acked
    /\ \A m \in Node : (m # n) => (n \in acked \/ m \in acked \/ parent[m] # n)
    /\ phase' = [phase EXCEPT ![n] = "done"]
    /\ UNCHANGED <<acked, parent, echoNum, echoFrom, adj>>

Next ==
    \/ \E n \in Node : Begin(n)
    \/ \E n \in Node, m \in Node : Echo(n, m)
    \/ \E m \in Node : Ack(m)
    \/ \E n \in Node : Done(n)

Spec == Init /\ [][Next]_vars

AncestorProperties ==
    /\ (parent[initiator] = NoNode /\ /\ \A m \in Node \ {initiator} : parent[m] # NoNode)
    /\ \A m \in Node : (m # initiator /\ parent[m] # NoNode) => parent[parent[m]] # m

AncestorCycleFree ==
    \A n \in Node : (parent[n] # NoNode) ~> (parent[n] = NoNode)

TestSpec ==
    /\ Spec
    /\ \A n \in Node, m \in Node : (n # m) ~> (<<n, m>> \in adj)

====