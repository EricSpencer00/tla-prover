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

(* Aliases for invariants from Echo *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

(* Alias to the specification defined in Echo *)
TestSpec == Spec
====