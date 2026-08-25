---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

\* Concrete concrete definitions for the model‑checking instance
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { << "n1", "n2" >>,
        << "n1", "n3" >>,
        << "n2", "n1" >>,
        << "n2", "n3" >>,
        << "n3", "n1" >>,
        << "n3", "n2" >> }

\* The sentinel for “no parent’’ must be distinct from all nodes
ASSUME NoNode \notin Node

\* Variant that prints the adjacency relation at start‑up
InitPrint == Init /\ Print(R)

\* Specification to be checked
TestSpec == InitPrint /\ [][Next]_vars

====