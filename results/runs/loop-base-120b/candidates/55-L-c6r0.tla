---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for the three‑node fully‑meshed graph *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<a, b>> : a \in N1 /\ b \in N1 /\ a # b }
NoNode == "NoNode"

(* Model‑checking assumption: the sentinel is not a real node *)
ASSUME NoNode \notin N1

(* Instantiate the generic Echo specification with the concrete constants *)
INSTANCE Echo WITH Node <- N1,
                 initiator <- I1,
                 R <- R1,
                 NoNode <- NoNode

(* Preserve the original initialization from Echo *)
Init == Echo!Init

(* Test action that prints the adjacency relation at startup *)
PrintR == /\ UNCHANGED <<>>
           /\ Print("R = ", R)

(* Extend the next‑state relation with the printing action *)
Next == Echo!Next \/ PrintR

(* The concrete specification to be checked *)
TestSpec == Init /\ [][Next]_(Echo!vars)

(* Invariants inherited from Echo *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties
====