---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

\* Concrete concrete definitions for the model‑checking instance
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

\* The specification to be checked
TestSpec == Spec

\* The invariants are inherited from the Echo specification
\* (they are therefore available as TypeOK and AncestorProperties)

====