---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
INSTANCE Echo

CONSTANTS Node, initiator, R, NoNode

\* Concrete substitution operators used by the .cfg file
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

\* Ensure the sentinel constant is distinct from all nodes
ASSUME NoNode \notin N1

\* Test variant that prints the adjacency relation at initialization
TestInit == Echo!Init /\ Print(R)

\* Specification formula required by the .cfg file
TestSpec == TestInit /\ [] [Echo!Next]_{Echo!vars}

\* Invariants required by the .cfg file
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====