---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions used to instantiate the generic Echo specification *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<< "n1", "n2" >>, << "n2", "n1" >>,
       << "n1", "n3" >>, << "n3", "n1" >>,
       << "n2", "n3" >>, << "n3", "n2" >>}

(* Instantiate the generic Echo specification with the concrete constants *)
INSTANCE Echo WITH Node <- N1, initiator <- I1, R <- R1, NoNode <- NoNode

(* Specification to be checked by the model checker *)
TestSpec == Init /\ [][Next]_vars

====