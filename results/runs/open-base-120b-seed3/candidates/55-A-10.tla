---- MODULE MCEcho ----
EXTEND Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions used by the .cfg file to instantiate the constants *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
NoNode == "NoNode"
R1 == { <<x, y>> : x \in N1 /\ y \in N1 /\ x # y }

(* Specification that the model checker will check *)
TestSpec == Spec

(* Invariants inherited from the Echo specification *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties
====