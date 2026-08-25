---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* ----------------------------------------------------------------------
   Concrete definitions for the three‑node fully‑meshed graph
   ---------------------------------------------------------------------- *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { << "n1", "n2" >>,
        << "n2", "n1" >>,
        << "n1", "n3" >>,
        << "n3", "n1" >>,
        << "n2", "n3" >>,
        << "n3", "n2" >> }

(* a distinguished value that is not a node *)
NoNode == "NoNode"

(* ----------------------------------------------------------------------
   Bind the constants to the concrete values for model checking
   ---------------------------------------------------------------------- *)
ASSUME Node = N1
ASSUME initiator = I1
ASSUME R = R1

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
InitPrint == Init /\ Print(R)
TestSpec == InitPrint /\ [] [Next]_vars

====