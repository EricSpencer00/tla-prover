---- MODULE MCEcho ----
EXTENDS Echo, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants required by the Echo specification.  Their concrete
  values are supplied via the operators N1, I1, R1 and NoNode,
  which the .cfg file maps to the constants Node, initiator, R and
  NoNode respectively.
--------------------------------------------------------------------*)
CONSTANTS Node, initiator, R, NoNode

(*--------------------------------------------------------------------
  Concrete definitions for the three‑node fully‑meshed graph.
--------------------------------------------------------------------*)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<<i, j>> : i \in N1 /\ j \in N1 /\ i # j}
NoNode == "null"

(*--------------------------------------------------------------------
  Specification exported for the model checker.
--------------------------------------------------------------------*)
TestSpec == Spec

(*--------------------------------------------------------------------
  Invariants required by the .cfg file.
--------------------------------------------------------------------*)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====