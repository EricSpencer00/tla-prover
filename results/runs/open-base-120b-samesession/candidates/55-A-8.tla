---- MODULE MCEcho ----
EXTENDS TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete finite definitions used by the .cfg substitutions *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

(* Instantiate the generic Echo specification with the concrete values *)
INSTANCE Echo AS EchoInst WITH
  Node      <- N1,
  initiator <- I1,
  R         <- R1,
  NoNode    <- NoNode

(* Test variant that prints the adjacency relation at startup *)
InitPrint == EchoInst!Init /\ Print(EchoInst!R)

TestSpec == InitPrint /\ [][EchoInst!Next]_(EchoInst!vars)

TypeOK == EchoInst!TypeOK
AncestorProperties == EchoInst!AncestorProperties
====