---- MODULE MCEcho ----
EXTENDS Naturals, TLC

CONSTANTS Node, initiator, R, NoNode

\* Concrete values for the model‑checking run
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

\* Sentinel value distinct from all nodes
NoNode == "NoNode"

\* Instantiate the generic Echo specification with the concrete constants
INSTANCE Echo AS E WITH
  Node      <- N1,
  initiator <- I1,
  R         <- R1,
  NoNode    <- NoNode

\* Test specification (the instantiated Echo spec)
TestSpec == E!Spec

\* Invariants inherited from Echo
TypeOK == E!TypeOK
AncestorProperties == E!AncestorProperties
=============================================================================