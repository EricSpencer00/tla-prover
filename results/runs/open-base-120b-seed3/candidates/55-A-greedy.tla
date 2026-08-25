---- MODULE MCEcho ----
EXTENDS Echo, FiniteSets, Sequences, Naturals

CONSTANTS Node, initiator, R, NoNode

\* Concrete definitions used by the .cfg substitution
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<< "n1", "n2" >>, << "n2", "n1" >>,
       << "n1", "n3" >>, << "n3", "n1" >>,
       << "n2", "n3" >>, << "n3", "n2" >>}

\* Sentinel value distinct from all nodes
NoNode == "NoNode"

\* Test variant that prints the adjacency relation at start
TestSpec == Spec /\ Print(R)

\* Invariants exported for the .cfg file
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====