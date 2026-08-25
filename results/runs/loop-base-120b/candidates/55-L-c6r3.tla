---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, Sequences, TLC, Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for the three‑node fully‑meshed graph *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == (N1 \X N1) \ { <<x, x>> : x \in N1 }

(* Model‑checking assumption: the sentinel is not a real node *)
ASSUME NoNode \notin N1

(* Bind the generic constants to concrete values *)
Node == N1
initiator == I1
R == R1
NoNode == "NoNode"

(* Preserve the original initialization from Echo *)
Init == Echo!Init

(* Test action that prints the adjacency relation at startup *)
PrintR ==
    /\ UNCHANGED Echo!vars
    /\ Print("R = ", R)

(* Extend the next‑state relation with the printing action *)
Next == Echo!Next \/ PrintR

(* The concrete specification to be checked *)
TestSpec == Init /\ [][Next]_(Echo!vars)

(* Invariants inherited from Echo *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties
====