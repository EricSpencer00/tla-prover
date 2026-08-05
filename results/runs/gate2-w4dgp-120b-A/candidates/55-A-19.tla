---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, sent, echoRecvd

vars == <<parent, sent, echoRecvd>>

RECURSIVE Ancestors(_)
Ancestors(n) == IF parent[n] = NoNode THEN {}
                 ELSE {parent[n]} \cup Ancestors(parent[n])

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ sent = {}
    /\ echoRecvd = {}

Send(parent, n) ==
    /\ parent[parent] = NoNode
    /\ n # parent
    /\ <<parent, n>> \notin sent
    /\ sent' = sent \cup {<<parent, n>>}
    /\ UNCHANGED <<parent, echoRecvd>>

EchoReceive(parent, n) ==
    /\ <<parent, n>> \in sent
    /\ <<parent, n>> \notin echoRecvd
    /\ parent' = [parent EXCEPT ![n] = parent]
    /\ echoRecvd' = echoRecvd \cup {<<parent, n>>}
    /\ UNCHANGED sent

EchoSendBack(parent, n) ==
    /\ parent[n] = parent
    /\ parent' = [parent EXCEPT ![n] = NoNode]
    /\ UNCHANGED <<sent, echoRecvd>>

Next ==
    \/ \E parent \in Node, n \in Node : Send(parent, n)
    \/ \E parent \in Node, n \in Node : EchoReceive(parent, n)
    \/ \E parent \in Node, n \in Node : EchoSendBack(parent, n)

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ sent \subseteq (Node \X Node)
    /\ echoRecvd \subseteq (Node \X Node)

AncestorProperties ==
    /\ initiator \in Node
    /\ \A n \in Node : (n # initiator => initiator \in Ancestors(n))
    /\ \A m, n \in Node : (<<m, n>> \in echoRecvd => (parent[n] = m /\ n \notin Ancestors(m)))

PrintAdjacency ==
    /\ ~ \E n \in Node : n \in I1
    /\ PRINTING == Cardinality(I1)
    /\ ~ \E m, n \in Node : <<m, n>> \in R1
    /\ LET d == {<<m, n>> : m \in N1 /\ n \in N1 /\ m # n} IN R1' = d
    /\ UNCHANGED <<parent, sent, echoRecvd>>

Spec == Init /\ [][Next]_vars

TestSpec == Spec \/ PrintAdjacency

====