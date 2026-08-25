---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

(* concrete definitions for the three‑node fully‑meshed graph *)
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

NoNode == "NoNode"

(* instantiate the generic Echo specification with the concrete constants *)
INSTANCE Echo WITH
    Node     <- N1,
    initiator<- I1,
    R        <- R1,
    NoNode   <- NoNode

(* test variant that prints the adjacency relation at startup *)
PrintAdjacency == Print(R1)

TestInit == Echo!Init /\ PrintAdjacency
TestNext == Echo!Next

TestSpec == TestInit /\ [][TestNext]_(Echo!vars)

(* invariants inherited from Echo *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties
====