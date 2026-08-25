---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(*--------------------------------------------------------------*)
(* Concrete concrete values for the model‑checking configuration *)
(*--------------------------------------------------------------*)

N1 == {"n1", "n2", "n3"}

I1 == "n1"

R1 == {
    << "n1", "n2" >>,
    << "n2", "n1" >>,
    << "n1", "n3" >>,
    << "n3", "n1" >>,
    << "n2", "n3" >>,
    << "n3", "n2" >>
}

(*--------------------------------------------------------------*)
(* Bind the declared constants to the concrete values above *)
(*--------------------------------------------------------------*)

Node == N1
initiator == I1
R == R1
NoNode == "NoNode"

(*--------------------------------------------------------------*)
(* Specification entry points required by the .cfg file           *)
(*--------------------------------------------------------------*)

TestSpec == Spec

INIT == Init
NEXT == Next

(*--------------------------------------------------------------*)
(* Invariants required by the .cfg file                         *)
(*--------------------------------------------------------------*)

TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

PROPERTIES == {}

=============================================================================