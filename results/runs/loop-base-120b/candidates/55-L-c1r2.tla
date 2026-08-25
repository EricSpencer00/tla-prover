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
   Bind the abstract constants used by Echo to the concrete definitions
   above.  The configuration substitutes N1, I1, R1 for the abstract
   constants Node, initiator, and R, respectively.  We provide the required
   identifiers here.
   ---------------------------------------------------------------------- *)

Node == N1
initiator == I1
R == R1

(* Sentinel value representing “no parent”.  It must be distinct from any
   element of Node. *)
NoNode == "None"

(* ----------------------------------------------------------------------
   Export the invariants required by the .cfg file.  They are defined in
   the abstract Echo module; we simply expose them under the expected
   names.
   ---------------------------------------------------------------------- *)

TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

(* ----------------------------------------------------------------------
   The specification to be checked.
   ---------------------------------------------------------------------- *)

TestSpec == Init /\ [][Next]_vars

====