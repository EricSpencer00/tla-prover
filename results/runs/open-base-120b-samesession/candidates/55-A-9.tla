---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete instances for model checking *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { << "n1", "n2" >>,
        << "n1", "n3" >>,
        << "n2", "n1" >>,
        << "n2", "n3" >>,
        << "n3", "n1" >>,
        << "n3", "n2" >> }
NoNode == "NoNode"

(* Specification and safety invariants, delegated to the Echo module *)
TestSpec == Echo!Spec
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====