---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete finite set of nodes for model checking *)
N1 == {"n1", "n2", "n3"}

(* Deterministic choice of initiator *)
I1 == "n1"

(* Fully‑meshed undirected graph (symmetric, irreflexive) *)
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

(* ----------------------------------------------------------------------
   Initialization and next‑state relation for the test variant.
   The Init includes a Print statement that outputs the adjacency relation.
   ---------------------------------------------------------------------- *)
Init == Echo!Init /\ Print("Adjacency relation R = " \o ToString(R1))

Next == Echo!Next

(* Specification that uses the printed Init *)
Spec == Init /\ [][Next]_Echo!vars

(* Name required by the .cfg file *)
TestSpec == Spec

(* Invariants required by the .cfg file *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====