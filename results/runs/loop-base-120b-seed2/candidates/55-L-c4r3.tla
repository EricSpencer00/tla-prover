---- MODULE MCEcho ----
EXTENDS Echo, FiniteSets, TLC
CONSTANTS Node, initiator, R

(*--------------------------------------------------------------------
  Concrete definitions for the three‑node fully‑meshed graph.
--------------------------------------------------------------------*)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<<i, j>> : i \in N1 /\ j \in N1 /\ i # j}

(*--------------------------------------------------------------------
  Specification exported for the model checker.
--------------------------------------------------------------------*)
TestSpec == Spec
====