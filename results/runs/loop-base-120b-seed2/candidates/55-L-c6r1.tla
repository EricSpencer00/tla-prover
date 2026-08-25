---- MODULE MCEcho ----
EXTENDS Echo, TLC

(* Concrete three‑node fully‑meshed graph *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

(* Specification used by the model checker; prints the adjacency relation at start *)
TestSpec == Echo!Init /\ Print("R1:", R1) /\ [][Echo!Next]_vars

(* Invariants required by the .cfg file *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====