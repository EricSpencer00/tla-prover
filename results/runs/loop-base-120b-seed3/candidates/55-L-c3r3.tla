---- MODULE MCEcho ----
EXTENDS Echo

(*--------------------------------------------------------------*)
(* Concrete values for the model‑checking configuration          *)
(*--------------------------------------------------------------*)

(* Finite set of nodes *)
N1 == {"n1", "n2", "n3"}

(* Deterministic initiator *)
I1 == "n1"

(* Fully‑meshed, symmetric, irreflexive adjacency relation *)
R1 == {
    << "n1", "n2" >>,
    << "n2", "n1" >>,
    << "n1", "n3" >>,
    << "n3", "n1" >>,
    << "n2", "n3" >>,
    << "n3", "n2" >>
}

(* Sentinel value used as “no parent” – must be distinct from any node *)
NoNode == "none"

(*--------------------------------------------------------------*)
(* Exported constants expected by the .cfg file                   *)
(*--------------------------------------------------------------*)

Node == N1
initiator == I1
R == R1

(*--------------------------------------------------------------*)
(* Specification entry points required by the .cfg file          *)
(*--------------------------------------------------------------*)

TestSpec == Spec

INIT == Init
NEXT == Next

(*--------------------------------------------------------------*)
(* Additional properties (none required)                         *)
(*--------------------------------------------------------------*)

PROPERTIES == {}

====