---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for the three‑node fully‑meshed graph *)
N1 == {"A", "B", "C"}
I1 == "A"
R1 == {
        << "A", "B" >>, << "B", "A" >>,
        << "A", "C" >>, << "C", "A" >>,
        << "B", "C" >>, << "C", "B" >>
      }

(* Bind the abstract constants to the concrete values for model checking *)
ASSUME Node = N1
ASSUME initiator = I1
ASSUME R = R1
ASSUME NoNode = "None"
ASSUME NoNode \notin Node

(* Test variant: print the adjacency relation at start‑up *)
PrintGraph == Print("Adjacency R = " \o ToString(R))

(* Override the initial predicate to include the printing action *)
Init == Echo!Init /\ PrintGraph

(* Specification used by the model checker *)
TestSpec == Init /\ [][Echo!Next]_Echo!vars

====