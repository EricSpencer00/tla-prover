---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* ----- Concrete values used for cfg substitution ----- *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

(* ----- Specification (with a test print of the graph) ----- *)
TestSpec == Spec /\ PrintT(R) = R

====