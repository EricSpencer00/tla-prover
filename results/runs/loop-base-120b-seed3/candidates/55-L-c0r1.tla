---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete instantiation of the abstract constants *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }
NoNode == "NoNode"

(* expose invariants from Echo *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

(* Test variant that prints the adjacency relation at startup *)
TestSpec == Init /\ Print(R) = R /\ [][Next]_vars

====