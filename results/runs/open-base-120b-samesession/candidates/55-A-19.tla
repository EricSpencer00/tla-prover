---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* concrete values used for constant substitution by the .cfg file *)
N1 == {"n1", "n2", "n3"}

I1 == "n1"

R1 == { <<a, b>> : a \in N1 /\ b \in N1 /\ a # b }

(* the sentinel value must be distinct from all nodes *)
ASSUME NoNode \notin Node

(* helper that prints the adjacency relation when the spec is initialized *)
PrintAdj == Print("Adjacency R = " \o ToString(R)) = TRUE

(* specification formula required by the .cfg file *)
TestSpec == Init /\ PrintAdj /\ [][Next]_vars

(* invariants required by the .cfg file *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====