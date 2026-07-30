---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES parent, phase, children, active

vars == <<parent, phase, children, active>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ phase \in [Node -> {"idle", "working", "echoed"}]
    /\ children \subseteq [u : Node, v : Node]
    /\ active \in BOOLEAN

AncestorProperties ==
    /\ initiator \in {n \in Node : parent[n] # NoNode}
    /\ \A x \in Node : (parent[x] # NoNode) => (parent[parent[x]] = NoNode)

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ phase = [n \in Node |-> "idle"]
    /\ children = {}
    /\ active = FALSE

StartEcho(x) ==
    /\ phase[x] = "idle"
    /\ phase' = [phase EXCEPT ![x] = "working"]
    /\ active' = TRUE
    /\ UNCHANGED <<parent, children>>

SendEcho(x, y) ==
    /\ phase[x] = "working"
    /\ y # x
    /\ <<x, y>> \in R
    /\ parent[y] = NoNode
    /\ parent' = [parent EXCEPT ![y] = x]
    /\ phase' = [phase EXCEPT ![y] = "working"]
    /\ UNCHANGED <<children, active>>

CollectEcho(y) ==
    /\ phase[y] = "working"
    /\ \A z \in Node : (parent[z] = y) => phase[z] = "echoed"
    /\ phase' = [phase EXCEPT ![y] = "echoed"]
    /\ UNCHANGED <<parent, children, active>>

Echo(x, y) ==
    /\ phase[x] = "working"
    /\ parent[x] = y
    /\ children' = children \cup {[u |-> y, v |-> x]}
    /\ phase' = [phase EXCEPT ![x] = "echoed"]
    /\ UNCHANGED <<parent, active>>

AllEchoed ==
    /\ \A n \in Node : phase[n] = "echoed"
    /\ active' = FALSE
    /\ UNCHANGED <<parent, phase, children>>

Next ==
    \/ \E x \in Node : StartEcho(x)
    \/ \E x, y \in Node : SendEcho(x, y)
    \/ \E y \in Node : CollectEcho(y)
    \/ \E x, y \in Node : Echo(x, y)
    \/ AllEchoed

Spec == Init /\ [][Next]_vars

TestSpec ==
    /\ Spec
    /\ UNCHANGED vars
    /\ \A x, y \in Node : PrintLl("R(") /\ PrintS(x) /\ PrintS(",") /\ PrintS(y) /\ PrintLn(")")

====