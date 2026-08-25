---- MODULE MCEcho ----
EXTENDS Echo, TLC

(* Concrete definitions for the constants *)
N1 == {"n1", "n2", "n3"}

I1 == "n1"

R1 == { << "n1", "n2" >>,
        << "n2", "n1" >>,
        << "n1", "n3" >>,
        << "n3", "n1" >>,
        << "n2", "n3" >>,
        << "n3", "n2" >> }

(* Bind the declared constants to the concrete definitions for model checking *)
ASSUME Node = N1
ASSUME initiator = I1
ASSUME R = R1
ASSUME NoNode \notin Node

(* Specification used by the model checker *)
TestSpec == Spec

====