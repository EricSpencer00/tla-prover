---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete concrete definitions used by the .cfg substitution *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<a, b>> : a \in N1 /\ b \in N1 /\ a # b }
NoNode == "NoNode"

(* Basic sanity assumptions for the concrete instance *)
ASSUME NoNode \notin N1
ASSUME I1 \in N1

(* Specification alias expected by the configuration *)
TestSpec == Spec

(* Export the initialization and next-state relations from Echo *)
Init == Init
Next == Next

(* Invariants required by the configuration *)
TypeOK == TypeOK
AncestorProperties == AncestorProperties

====