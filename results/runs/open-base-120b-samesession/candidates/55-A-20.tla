---- MODULE MCEcho ----
EXTENDS Echo, Naturals, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions used by the .cfg substitution *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

(* Sentinel value distinct from all nodes *)
NoNode == "NoNode"

(* Inherited definitions from the Echo specification *)
Init == Echo!Init
Next == Echo!Next

(* Specification to be checked by TLC *)
TestSpec == Echo!Spec

(* Invariants required by the configuration *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====