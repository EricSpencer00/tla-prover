---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions used by the .cfg substitutions *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

(* Instantiate the generic Echo specification *)
INSTANCE Echo AS EchoInst

(* Print the adjacency relation at startup (TLC Print returns TRUE) *)
PrintGraph == Print("Adjacency relation R = " \o ToString(R))

(* Init and Next actions for the test variant *)
INIT == EchoInst!Init /\ PrintGraph
NEXT == EchoInst!Next

(* Specification used by the model checker *)
TestSpec == (EchoInst!Init /\ PrintGraph) /\ [][EchoInst!Next]_(EchoInst!vars)

(* Invariants inherited from Echo *)
TypeOK == EchoInst!TypeOK
AncestorProperties == EchoInst!AncestorProperties

(* Optional properties placeholder *)
PROPERTIES == TRUE
====