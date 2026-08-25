---- MODULE MCEcho ----
EXTENDS Echo

CONSTANT Node, initiator, R, NoNode

(* Concrete three‑node fully‑meshed graph *)
ASSUME Node = {"n1", "n2", "n3"}
ASSUME initiator = "n1"
ASSUME NoNode = "NoNode"
ASSUME R = {
    << "n1", "n2" >>,
    << "n2", "n1" >>,
    << "n1", "n3" >>,
    << "n3", "n1" >>,
    << "n2", "n3" >>,
    << "n3", "n2" >>
}

(* Operators that the .cfg substitutes for the constants *)
N1 == Node
I1 == initiator
R1 == R

(* Re‑export invariants defined in Echo *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

(* Init prints the adjacency relation at start‑up *)
Init == Echo!Init /\ Print(R)
Next == Echo!Next

vars == Echo!vars

(* Specification used by the model checker *)
TestSpec == Init /\ [][Next]_vars

====