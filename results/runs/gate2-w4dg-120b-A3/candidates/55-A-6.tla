---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, active, arrived, msgCount

vars == <<parent, active, arrived, msgCount>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ active \in SUBSET Node
    /\ arrived \in SUBSET Node
    /\ msgCount \in 0..4

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ active = {initiator}
    /\ arrived = {}
    /\ msgCount = 0

Echo ==
    /\ \E n \in active :
         /\ parent[n] = NoNode
         /\ \E m \in Node \ {n} :
              /\ parent' = [parent EXCEPT ![n] = m]
              /\ active' = (active \cup {m}) \ {n}
         /\ msgCount' = (msgCount + 1) % 5
    /\ UNCHANGED arrived

Ack ==
    /\ \E n \in Node :
         /\ n \in active
         /\ active' = active \ {n}
         /\ arrived' = arrived \cup {n}
    /\ UNCHANGED <<parent, msgCount>>

Quiesce ==
    /\ active = {}
    /\ arrived = Node
    /\ UNCHANGED vars

Next == Echo \/ Ack \/ Quiesce

Spec == Init /\ [][Next]_vars

AncestorProperties ==
    /\ initiator \in arrived
    /\ \A n \in Node \ {initiator} : (parent[n] # NoNode) => (parent[n] \in arrived)
    /\ \A n \in arrived : (n # initiator) => (parent[n] # NoNode)
    /\ \A n \in arrived : (n # initiator) => (parent[n] \in arrived)

TestSpec ==
    /\ Spec
    /\ UNCHANGED vars

====