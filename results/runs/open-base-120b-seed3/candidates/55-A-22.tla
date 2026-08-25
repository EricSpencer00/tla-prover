---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions used by the .cfg substitution *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<< "n1", "n2" >>, << "n2", "n1" >>,
       << "n1", "n3" >>, << "n3", "n1" >>,
       << "n2", "n3" >>, << "n3", "n2" >>}

(* Specification derived from the Echo specification *)
TestSpec == Spec

(* Invariants imported from the Echo specification *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====