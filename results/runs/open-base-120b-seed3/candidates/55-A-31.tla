---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for substitution *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

(* Distinct sentinel for the “no‑parent” value *)
NoNode == "NoNode"

(* Test specification that prints the adjacency relation at start‑up *)
TestSpec == PrintT(R1) /\ Spec

(* Invariants inherited from the Echo specification *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====