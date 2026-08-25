---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

\* Concrete definitions that will be used to instantiate the constants
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1, j \in N1, i # j }
NoNodeVal == "NoNode"

\* Bind the declared constants to the concrete values for model checking
ASSUME Node = N1
ASSUME initiator = I1
ASSUME R = R1
ASSUME NoNode = NoNodeVal

\* Export the full specification (as required by the .cfg file)
TestSpec == Spec

\* Export the basic components of the specification (optional but useful)
Init == Echo!Init
Next == Echo!Next

\* Invariants required by the .cfg file
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====