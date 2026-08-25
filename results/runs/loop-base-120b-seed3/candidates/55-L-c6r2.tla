---- MODULE MCEcho ----
EXTENDS Echo, TLC, Sequences, Naturals

\* Concrete definitions that will be substituted for the constants
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<x, y>> : x \in N1 /\ y \in N1 /\ x # y }

\* NoNode must be distinct from all nodes
ASSUME NoNode \notin N1

\* Specification used by the model checker
TestSpec == Init /\ [][Next]_vars

====