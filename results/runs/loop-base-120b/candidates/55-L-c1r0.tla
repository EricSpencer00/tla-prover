---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* ----------------------------------------------------------------------
   Concrete (bounded) definitions that the .cfg file will substitute for the
   abstract constants.  These must be operators with the exact names
   required by the configuration.
   ---------------------------------------------------------------------- *)

N1 == {"A", "B", "C"}

I1 == "A"

R1 == {
        << "A", "B" >>, << "B", "A" >>,
        << "A", "C" >>, << "C", "A" >>,
        << "B", "C" >>, << "C", "B" >>
      }

NoNode == "None"

(* ----------------------------------------------------------------------
   The specification to be checked.
   ---------------------------------------------------------------------- *)

TestSpec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Invariants required by the .cfg file.
   ---------------------------------------------------------------------- *)

TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====