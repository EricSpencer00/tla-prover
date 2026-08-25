---- MODULE MCEcho ----
EXTENDS Echo

(* ----------------------------------------------------------------------
   Concrete (bounded) definitions that the .cfg file will substitute for the
   abstract constants.  These must be operators with the exact names
   required by the configuration.
   ---------------------------------------------------------------------- *)

(* Concrete set of nodes *)
N1 == {"A", "B", "C"}

(* Concrete initiator *)
I1 == "A"

(* Concrete edge relation (symmetric, irreflexive, fully connected) *)
R1 == {
        << "A", "B" >>, << "B", "A" >>,
        << "A", "C" >>, << "C", "A" >>,
        << "B", "C" >>, << "C", "B" >>
      }

(* ----------------------------------------------------------------------
   The specification to be checked.
   ---------------------------------------------------------------------- *)

TestSpec == Init /\ [][Next]_vars

====