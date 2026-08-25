---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for model checking *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
    << "n1", "n2" >>, << "n2", "n1" >>,
    << "n1", "n3" >>, << "n3", "n1" >>,
    << "n2", "n3" >>, << "n3", "n2" >>
}

(* Specification under test *)
TestSpec == Spec

====