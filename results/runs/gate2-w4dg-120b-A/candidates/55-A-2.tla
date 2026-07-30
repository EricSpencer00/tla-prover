---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets, TLC, Echo

CONSTANTS Node, initiator, R, NoNode

TypeOK ==
    /\ Node \subseteq STRING
    /\ Cardinality(Node) = 3
    /\ initiator \in Node
    /\ R \subseteq [Node \times Node]
    /\ \A e \in R : e[1] # e[2]
    /\ \A e \in R : <<e[1], e[2]>> \in R
    /\ NoNode \notin Node

Vars == EchoVars

Init ==
    /\ \E e \in [Node -> Node \cup {NoNode}] :
        /\ \A v \in Node : parent[v] = e[v]
        /\ parent[initiator] = NoNode
    /\ phase = [v \in Node |-> "idle"]
    /\ recv = [v \in Node |-> {}]
    /\ msgs = {}

Next ==
    \/ EchoInitiate
    \/ EchoSend
    \/ EchoRecv

TestSpec == Init /\ [][Next]_Vars

====