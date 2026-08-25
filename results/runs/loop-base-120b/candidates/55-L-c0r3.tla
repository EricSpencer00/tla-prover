---- MODULE MCEcho ----
EXTENDS Echo

(* Constants required by the .cfg file *)
CONSTANTS Node, initiator, R, NoNode

(* Sentinel value for the “no parent” case – distinct from all nodes *)
NoNode == "none"

(* Concrete definitions used by the .cfg substitution *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

(* Invariants required by the .cfg file – aliased to those defined in Echo *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

(* Specification formula required by the .cfg *)
TestSpec == (Init /\ Print(R)) /\ [][Next]_vars

====