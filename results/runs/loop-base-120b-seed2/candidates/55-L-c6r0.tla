---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete three‑node fully‑meshed graph *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

(* Print the adjacency relation at the start of each execution *)
Init == Echo!Init /\ Print(R1)

(* Specification used by the model checker *)
TestSpec == Init /\ [][Next]_vars

(* Invariants required by the .cfg file *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====