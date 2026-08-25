---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete instances for model checking *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<<i, j>> : i \in N1 /\ j \in N1 /\ i # j}
NoNode == "NoNode"

(* Specification entry point for the model checker *)
TestSpec == Spec

====