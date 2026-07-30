---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES parent, status, flooded, inBox

vars == <<parent, status, flooded, inBox>>

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ status = [n \in Node |-> "idle"]
    /\ flooded = {}
    /\ inBox = {}

\* The Echo system has exactly these three actions.  The test variant is the
\* extra InitPrint action below, which is deliberately not part of the spec.
Send ==
    /\ \E s, d \in Node :
        /\ s # d
        /\ <<s, d>> \in R
        /\ status[s] = "idle"
        /\ parent[d] = NoNode
        /\ status' = [status EXCEPT ![s] = "sent"]
        /\ parent' = [parent EXCEPT ![d] = s]
    /\ inBox' = {}
    /\ flooded' = flooded

Echo ==
    /\ \E d \in Node :
        /\ status[d] = "sent"
        /\ status' = [status EXCEPT ![d] = "echoed"]
        /\ flooded' = flooded \cup {d}
        /\ inBox' = inBox
    /\ parent' = parent

Drop ==
    /\ \E m \in flooded :
        /\ m \notin inBox
        /\ inBox' = inBox \cup {m}
    /\ parent' = parent
    /\ status' = status
    /\ flooded' = flooded \ {m}

\* Test-only action: emits the full adjacency relation as observable
\* output and does nothing else.  The spec is still Init /\ [][Next]_vars.
InitPrint ==
    /\ Cardinality(flooded) = 0
    /\ Cardinality(inBox) = 0
    /\ status[initiator] = "idle"
    /\ Print("Adjacency relation is " * ToString(R))
    /\ UNCHANGED vars

Next == Send \/ Echo \/ Drop

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ status \in [Node -> {"idle", "sent", "echoed"}]
    /\ flooded \subseteq Node
    /\ inBox \subseteq Node

AncestorProperties ==
    /\ (parent[initiator] = NoNode /\ \A x \in Node \ {initiator} : parent[x] # NoNode)
    /\ \A y \in Node :
        /\ (parent[y] # NoNode) ~> (parent[parent[y]] = NoNode)

Spec == Init /\ [][Next]_vars

TestSpec == Spec /\ InitPrint

====