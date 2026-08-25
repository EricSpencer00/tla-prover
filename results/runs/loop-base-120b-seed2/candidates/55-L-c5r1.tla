---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

\* Concrete definitions for the model‑checking instance
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

\* Expose the invariants from the Echo specification so that the .cfg can find them
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

\* The specification to be checked
TestSpec == Spec

====