---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions used by the configuration file *)
N1 == {"A", "B", "C"}
I1 == "A"
R1 == {
        << "A", "B" >>,
        << "B", "A" >>,
        << "A", "C" >>,
        << "C", "A" >>,
        << "B", "C" >>,
        << "C", "B" >>
      }

(* Sentinel value distinct from all nodes *)
NoNode == "None"

(* Initial state augmented with a print of the adjacency relation *)
InitPrint == Print(R) /\ Init

(* Specification required by the .cfg *)
TestSpec == InitPrint /\ [][Next]_vars

====