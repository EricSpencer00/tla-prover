---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete instantiation for model checking *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<a, b>> : a \in N1 /\ b \in N1 /\ a # b }
NoNode == "NoNode"

(* Initialization prints the adjacency relation for debugging *)
Init == Echo!Init /\ (Print(R) = R)

Next == Echo!Next

Spec == Init /\ [][Next]_vars

TestSpec == Spec

TypeOK == Echo!TypeOK

AncestorProperties == Echo!AncestorProperties
====