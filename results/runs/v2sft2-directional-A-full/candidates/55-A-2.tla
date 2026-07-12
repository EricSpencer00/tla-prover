---- MODULE MCEcho ----
EXTENDS TLC, Echo

CONSTANT Node = {"n1", "n2", "n3"}
CONSTANT initiator = "n1"
CONSTANT NoNode = "NoNode"
CONSTANT R = { <<u, v>> | u \in Node, v \in Node, u \# v }

TestSpec == Init /\ [][Next]_vars

INVARIANT TypeOK, AncestorProperties

====