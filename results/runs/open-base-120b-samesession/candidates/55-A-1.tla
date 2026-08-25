---- MODULE MCEcho ----
EXTENDS TLC

(*-----------------------------------------------------------------
  Constants to be instantiated by the model checker.
-----------------------------------------------------------------*)
CONSTANT Node, initiator, R, NoNode

(*-----------------------------------------------------------------
  Concrete three‑node fully‑meshed graph for exhaustive checking.
-----------------------------------------------------------------*)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

(*-----------------------------------------------------------------
  Instantiation of the generic Echo specification with the concrete
  constants defined above.
-----------------------------------------------------------------*)
INSTANCE Echo AS E WITH
  Node      <- N1,
  initiator <- I1,
  R         <- R1,
  NoNode    <- NoNode

(*-----------------------------------------------------------------
  Required identifiers for the .cfg file.
-----------------------------------------------------------------*)
TestSpec == E!Spec
TypeOK == E!TypeOK
AncestorProperties == E!AncestorProperties

====