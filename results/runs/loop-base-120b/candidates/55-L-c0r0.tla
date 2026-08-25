---- MODULE MCEcho ----
EXTENDS Echo

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

(* Inherited initialization, augmented with a print of the graph *)
Init == Echo!Init /\ Print(R)

(* Inherited next-state relation *)
Next == Echo!Next

(* Specification formula required by the .cfg *)
TestSpec == Init /\ [][Next]_vars

(* Invariants required by the .cfg *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====