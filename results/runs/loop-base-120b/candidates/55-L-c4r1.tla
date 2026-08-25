---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete finite instances used by the .cfg substitutions *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

(* Distinct sentinel value for the “no‑parent” case *)
NoNode == "⊥"

(* Aliases to the definitions provided by the Echo specification *)
Init == Echo!Init
Next == Echo!Next
TestSpec == Echo!Spec

(* Invariants imported from the Echo specification *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====