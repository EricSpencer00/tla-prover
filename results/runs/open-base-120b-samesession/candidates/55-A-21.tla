---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Node, initiator, R, NoNode

\* Concrete definitions for the three‑node fully‑meshed graph
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<< "n1", "n2" >>, << "n2", "n1" >>,
       << "n1", "n3" >>, << "n3", "n1" >>,
       << "n2", "n3" >>, << "n3", "n2" >>}
NoNode == "NoNode"

\* Instantiate the generic Echo specification with the concrete constants
INSTANCE Echo WITH Node <- N1, initiator <- I1, R <- R1, NoNode <- NoNode

\* Test variant: print the adjacency relation when the initial state is created
InitPrint == Echo!Init /\ Print(R1)

Next == Echo!Next

\* Specification used by the model checker
TestSpec == InitPrint /\ [][Next]_Echo!vars

\* Invariants required by the .cfg file
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties
============================================