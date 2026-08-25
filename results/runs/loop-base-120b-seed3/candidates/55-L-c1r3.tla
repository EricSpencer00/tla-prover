---- MODULE MCEcho ----
EXTENDS Echo, TLC

(* ----- Concrete values used for cfg substitution ----- *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

(* ----- Exported invariants required by the .cfg ----- *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

(* ----- Specification (with a test print of the graph) ----- *)
TestSpec == Spec /\ PrintT(R) = R

====