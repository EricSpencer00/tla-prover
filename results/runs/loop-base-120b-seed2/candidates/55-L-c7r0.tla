---- MODULE MCEcho ----
EXTENDS Echo

CONSTANT Node, initiator, R, NoNode

(* Concrete instantiation for a three‑node fully‑connected graph *)
ASSUME Node = {"n1", "n2", "n3"}
ASSUME NoNode = "NoNode"
ASSUME initiator = "n1"
ASSUME R = {
    << "n1", "n2" >>,
    << "n2", "n1" >>,
    << "n1", "n3" >>,
    << "n3", "n1" >>,
    << "n2", "n3" >>,
    << "n3", "n2" >>
}

(* Operators used for substitution in the .cfg file *)
N1 == Node
I1 == initiator
R1 == R

(* Specification *)
TestSpec == Spec

(* Invariants *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====