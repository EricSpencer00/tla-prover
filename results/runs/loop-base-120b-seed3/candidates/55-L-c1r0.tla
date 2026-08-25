---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* ----- Concrete instantiation of the constants ----- *)
Node       == {"n1", "n2", "n3"}
initiator  == "n1"
NoNode     == "NoNode"
R          == { <<i, j>> : i \in Node /\ j \in Node /\ i # j }

(* ----- Operators used for cfg substitution ----- *)
N1 == Node
I1 == initiator
R1 == R

(* ----- Specification (with a test print of the graph) ----- *)
TestSpec == Spec /\ /\ PrintT(R) = R

(* ----- Invariants inherited from Echo ----- *)
TypeOK == TypeOK
AncestorProperties == AncestorProperties

====