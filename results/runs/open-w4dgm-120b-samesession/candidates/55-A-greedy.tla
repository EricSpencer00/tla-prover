---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

\* A fully-meshed three-node graph: every distinct pair of nodes is connected.
\* This concrete choice keeps the reachable state space tiny enough for exhaustive
\* model checking, while still exercising the full Echo protocol.
Neighbors(n) == {m \in Node : m # n}

VARIABLES parent, phase, echoCount, echoFrom, acked

vars == <<parent, phase, echoCount, echoFrom, acked>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ phase \in [Node -> {"idle", "echoing", "done"}]
    /\ echoCount \in [Node -> 0..Cardinality(Node)]
    /\ echoFrom \in [Node -> SUBSET Node]
    /\ acked \in [Node -> SUBSET Node]

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ phase = [n \in Node |-> "idle"]
    /\ echoCount = [n \in Node |-> 0]
    /\ echoFrom = [n \in Node |-> {}]
    /\ acked = [n \in Node |-> {}]

\* The initiator starts the spanning tree construction.
StartEcho ==
    /\ phase[initiator] = "idle"
    /\ phase' = [phase EXCEPT ![initiator] = "echoing"]
    /\ UNCHANGED <<parent, echoCount, echoFrom, acked>>

\* A node that is echoing forwards the echo to every neighbor except its parent.
SendEcho(n) ==
    /\ phase[n] = "echoing"
    /\ \E m \in Neighbors(n) \ {parent[n]} :
        /\ phase[m] = "idle"
        /\ parent' = [parent EXCEPT ![m] = n]
        /\ phase' = [phase EXCEPT ![m] = "echoing"]
    /\ UNCHANGED <<echoCount, echoFrom, acked>>

\* A node records an echo it receives from a neighbor.
ReceiveEcho(n) ==
    /\ phase[n] = "echoing"
    /\ \E m \in Neighbors(n) :
        /\ m # parent[n]
        /\ m \notin echoFrom[n]
        /\ echoFrom' = [echoFrom EXCEPT ![n] = @ \cup {m}]
        /\ echoCount' = [echoCount EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<parent, phase, acked>>

\* A node that has heard from all its neighbors (except its parent) is done.
DoneEcho(n) ==
    /\ phase[n] = "echoing"
    /\ echoFrom[n] = Neighbors(n) \ {parent[n]}
    /\ phase' = [phase EXCEPT ![n] = "done"]
    /\ UNCHANGED <<parent, echoCount, echoFrom, acked>>

\* A done node acknowledges its parent.
AckParent(n) ==
    /\ phase[n] = "done"
    /\ parent[n] # NoNode
    /\ n \notin acked[parent[n]]
    /\ acked' = [acked EXCEPT ![parent[n]] = @ \cup {n}]
    /\ UNCHANGED <<parent, phase, echoCount, echoFrom>>

\* The initiator is done once every other node has acknowledged it.
DoneRoot ==
    /\ phase[initiator] = "echoing"
    /\ \A n \in Node \ {initiator} : n \in acked[initiator]
    /\ phase' = [phase EXCEPT ![initiator] = "done"]
    /\ UNCHANGED <<parent, echoCount, echoFrom, acked>>

Next ==
    \/ StartEcho
    \/ \E n \in Node : SendEcho(n)
    \/ \E n \in Node : ReceiveEcho(n)
    \/ \E n \in Node : DoneEcho(n)
    \/ \E n \in Node : AckParent(n)
    \/ DoneRoot

Spec == Init /\ [][Next]_vars

\* Safety: the spanning tree is well-formed -- the initiator is an ancestor of
\* every other node and the ancestor relation is acyclic.
AncestorProperties ==
    /\ \A n \in Node : (n # initiator) => (initiator \in Ancestors(n))
    /\ \A n \in Node : ~ (n \in Ancestors(n))

\* Ancestors(n) is the set of nodes on the path from n to the initiator.
Ancestors(n) ==
    LET Rec(m) == IF m = NoNode THEN {} ELSE {m} \cup Rec(parent[m])
    IN Rec(n)

\* TestSpec is the entry point the .cfg file points to; it also prints the graph
\* adjacency relation at startup, which is a no-op for the model itself.
TestSpec == Spec /\ UNCHANGED vars /\ PrintNeighbors

PrintNeighbors ==
    /\ \A n \in Node : Print("Neighbors(" \o n \o ") = " \o ToString(Neighbors(n)))
    /\ UNCHANGED vars

====