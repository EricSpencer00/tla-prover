---- MODULE MCEcho ----
EXTENDS Naturals, TLC, Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for the three‑node fully‑meshed graph *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<a, b>> : a \in N1 /\ b \in N1 /\ a # b }

(* Sentinel value distinct from all nodes *)
NoNode == "NoNode"

(* Model‑checking assumption that the sentinel is not a node *)
ASSUME NoNode \notin Node

(* State‑variable definitions, inheriting from Echo and adding a Print at startup *)
Init == Echo!Init /\ Print(R1)
Next == Echo!Next
vars == Echo!vars

(* Specification to be checked *)
TestSpec == Init /\ [][][Next]_(vars)

(* Invariants required by the .cfg file *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====