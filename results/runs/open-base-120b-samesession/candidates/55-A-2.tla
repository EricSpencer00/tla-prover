---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(*-----------------------------------------------------------------
  Concrete definitions used by the .cfg file to instantiate the
  abstract constants of the Echo specification.
-----------------------------------------------------------------*)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >> }

(*-----------------------------------------------------------------
  Specification to be checked.  Echo defines the behavior as Spec,
  so we expose it under the name required by the .cfg file.
-----------------------------------------------------------------*)
TestSpec == Spec

====