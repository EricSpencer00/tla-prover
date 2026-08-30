---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, echo, beacon, beaconNode, started

vars == <<parent, echo, beacon, beaconNode, started>>

None == "none"
Started == "started"

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ echo \in [Node -> {None, Started}]
    /\ beacon \in [Node -> {"?"} \cup R]
    /\ beaconNode \in {None} \cup Node
    /\ started \subseteq Node

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ echo = [n \in Node |-> None]
    /\ beacon = [n \in Node |-> "?"]
    /\ beaconNode = None
    /\ started = {}

Start(n) ==
    /\ n = initiator
    /\ echo[n] = None
    /\ echo' = [echo EXCEPT ![n] = Started]
    /\ started' = started \cup {n}
    /\ UNCHANGED <<parent, beacon, beaconNode>>

Echo(m, n) ==
    /\ parent[n] = NoNode
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ UNCHANGED <<echo, beacon, beaconNode, started>>

Deliver(n) ==
    /\ echo[n] = None
    /\ echo' = [echo EXCEPT ![n] = Started]
    /\ started' = started \cup {n}
    /\ UNCHANGED <<parent, beacon, beaconNode>>

Beacon(m, n) ==
    /\ m # n
    /\ beaconNode = None
    /\ Cardinality(started) >= 2
    /\ \E r \in R : beacon' = [beacon EXCEPT ![n] = r]
    /\ beaconNode' = n
    /\ UNCHANGED <<parent, echo, started>>

Next ==
    \/ \E n \in Node : Start(n) \/ Deliver(n)
    \/ \E m, n \in Node : Echo(m, n) \/ Beacon(m, n)

Spec == Init /\ [][Next]_vars

AncestorProperties ==
    /\ (initiator # NoNode => parent[initiator] = NoNode)
    /\ \A n \in Node : (parent[n] # NoNode => parent[parent[n]] = NoNode)

PrintAdjacency ==
    \/ beacon' = [n \in Node |-> "?"]
    /\ UNCHANGED <<parent, echo, beaconNode, started>>

TestSpec == Spec /\ PrintAdjacency

====