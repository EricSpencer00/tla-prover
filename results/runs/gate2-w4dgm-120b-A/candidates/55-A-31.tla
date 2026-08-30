---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES echo, armed, link, responded, ancestor

vars == <<echo, armed, link, responded, ancestor>>

Init ==
    /\ echo = [x \in Node |-> "off"]
    /\ armed = [x \in Node |-> "inactive"]
    /\ link = [x \in Node |-> [y \in Node |-> TRUE]]
    /\ responded = [x \in Node |-> FALSE]
    /\ ancestor = [x \in Node |-> NoNode]

FireEcho(x) ==
    /\ x = initiator
    /\ echo[x] = "off"
    /\ echo' = [echo EXCEPT ![x] = "on"]
    /\ UNCHANGED <<armed, link, responded, ancestor>>

RespondEcho(x) ==
    /\ echo[x] = "off"
    /\ \E y \in Node :
        /\ y # x
        /\ echo[y] = "on"
        /\ link[y][x] = TRUE
        /\ echo' = [echo EXCEPT ![x] = "on"]
        /\ ancestor' = [ancestor EXCEPT ![x] = y]
    /\ UNCHANGED <<armed, link, responded>>

CommandArm(x) ==
    /\ echo[x] = "on"
    /\ echo' = [echo EXCEPT ![x] = "commanded"]
    /\ UNCHANGED <<armed, link, responded, ancestor>>

FireArm(x) ==
    /\ echo[x] = "commanded"
    /\ ~responded[x]
    /\ armed[x] = "inactive"
    /\ armed' = [armed EXCEPT ![x] = "active"]
    /\ responded' = [responded EXCEPT ![x] = TRUE]
    /\ UNCHANGED <<echo, link, ancestor>>

Quiesce ==
    /\ \A x \in Node : echo[x] \in {"on", "commanded"}
    /\ \A x \in Node : responded[x]
    /\ UNCHANGED vars

Next ==
    \/ \E x \in Node : FireEcho(x)
    \/ \E x \in Node : RespondEcho(x)
    \/ \E x \in Node : CommandArm(x)
    \/ \E x \in Node : FireArm(x)
    \/ Quiesce

InitSpec == Init
NextSpec == Next
Spec == InitSpec /\ [][NextSpec]_vars

TypeOK ==
    /\ echo \in [Node -> {"off", "on", "commanded"}]
    /\ armed \in [Node -> {"inactive", "active"}]
    /\ link \in [Node -> [Node -> BOOLEAN]]
    /\ responded \in [Node -> BOOLEAN]
    /\ ancestor \in [Node -> Node \cup {NoNode}]

AncestorProperties ==
    /\ \A x \in Node : (x # initiator) => (ancestor[x] # NoNode)
    /\ \A x \in Node : (x # initiator) => (ancestor[ancestor[x]] # NoNode)
    /\ \A x \in Node : (x # initiator) => (ancestor[ancestor[ancestor[x]]] = NoNode)

TestSpec == Spec

====