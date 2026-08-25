---- MODULE MCEcho ----
EXTENDS TLC

CONSTANTS Node, initiator, R, NoNode

\* Concrete definitions used by the .cfg substitution
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<< "n1", "n2" >>,
       << "n2", "n1" >>,
       << "n1", "n3" >>,
       << "n3", "n1" >>,
       << "n2", "n3" >>,
       << "n3", "n2" >>}

\* Instantiate the generic Echo specification with the concrete values
INSTANCE Echo WITH
    Node    <- N1,
    initiator <- I1,
    R       <- R1,
    NoNode  <- NoNode

\* Initial state (prints the graph for the test variant)
Init == Echo!Init /\ Print(R1)

Next == Echo!Next
vars == Echo!vars

\* Specification exported under the required name
TestSpec == Init /\ [][Next]_vars

\* Invariants required by the .cfg
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====