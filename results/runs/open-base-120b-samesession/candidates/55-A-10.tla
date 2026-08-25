---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* ----------------------------------------------------------------------
   Concrete instantiation for exhaustive model checking
   ---------------------------------------------------------------------- *)
Node == {"n1", "n2", "n3"}
NoNode == "NoNode"
initiator == "n1"
R == {
        << "n1", "n2" >>,
        << "n2", "n1" >>,
        << "n1", "n3" >>,
        << "n3", "n1" >>,
        << "n2", "n3" >>,
        << "n3", "n2" >>
     }

(* ----------------------------------------------------------------------
   Operators required by the .cfg file (substituted for constants)
   ---------------------------------------------------------------------- *)
N1 == Node
I1 == initiator
R1 == R

(* ----------------------------------------------------------------------
   Test variant that prints the adjacency relation at startup
   ---------------------------------------------------------------------- *)
Init == Echo!Init /\ Print("R = " ^ ToString(R))

Next == Echo!Next

(* ----------------------------------------------------------------------
   Specification exposed to the model checker
   ---------------------------------------------------------------------- *)
TestSpec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Invariants inherited from the Echo specification
   ---------------------------------------------------------------------- *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====