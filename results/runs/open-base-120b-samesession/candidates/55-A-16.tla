---- MODULE MCEcho ----
EXTENDS Naturals, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for substitution by the .cfg file *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
    <<"n1","n2">>, <<"n2","n1">>,
    <<"n1","n3">>, <<"n3","n1">>,
    <<"n2","n3">>, <<"n3","n2">>
}

(* Instantiate the generic Echo specification with the concrete values *)
INSTANCE Echo AS EchoInst WITH
    Node     <- N1,
    initiator<- I1,
    R        <- R1,
    NoNode   <- NoNode

(* Test variant that prints the adjacency relation at startup *)
PrintGraph == Print("Adjacency relation: " \o ToString(R1))

(* Specification exposed to the model checker *)
TestSpec == PrintGraph /\ EchoInst!Spec

(* Invariants required by the .cfg file *)
TypeOK == EchoInst!TypeOK
AncestorProperties == EchoInst!AncestorProperties

====