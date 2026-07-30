---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

TestSpec == Spec

VARIABLES parent, state, children, msgs

vars == <<parent, state, children, msgs>>

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ state = [n \in Node |-> "idle"]
    /\ children = {}
    /\ msgs = {}

EchoStep ==
    \/ \E n \in Node, m \in Node :
         /\ state[n] = "idle"
         /\ parent[m] = NoNode
         /\ n # m
         /\ \E c \in Node : n \in R[c]
         /\ parent' = [parent EXCEPT ![m] = n]
         /\ state' = [state EXCEPT ![m] = "propagating"]
    \/ \E n \in Node :
         /\ state[n] = "propagating"
         /\ children' = children \cup {n}
         /\ state' = [state EXCEPT ![n] = "echoed"]
    \/ \E n \in Node :
         /\ state[n] = "echoed"
         /\ \A m \in Node : parent[m] = n
         /\ state' = [state EXCEPT ![n] = "done"]
    \/ \E n \in Node :
         /\ state[n] = "done"
         /\ \A m \in Node : parent[m] = n
         /\ state' = [state EXCEPT ![n] = "idle"]
    /\ UNCHANGED <<parent, children, msgs>>

Idle == \A n \in Node : state[n] = "idle"

Next == EchoStep \/ (Idle /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ state \in [Node -> {"idle", "propagating", "echoed", "done"}]
    /\ children \subseteq Node
    /\ msgs \subseteq Node

AncestorProperties ==
    /\ (\A n \in Node : initiator \in R[n])
    /\ (\A n \in Node : parent[n] # NoNode => initiator \in R[parent[n]])

N1 == Node
I1 == initiator
R1 == R

====