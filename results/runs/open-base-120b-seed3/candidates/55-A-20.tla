---- MODULE MCEcho ----
EXTENDS Echo

\*-----------------------------------------------------------------
\* Constants required by the configuration
\*-----------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\*-----------------------------------------------------------------
\* Concrete finite definitions that the .cfg file will substitute
\*   Node      <- N1
\*   initiator <- I1
\*   R         <- R1
\*-----------------------------------------------------------------
N1 == {"n1", "n2", "n3"}

I1 == "n1"

R1 == { <<x, y>> : x \in N1 /\ y \in N1 /\ x # y }

\* Sentinel value distinct from all nodes
NoNode == "NoNode"

\*-----------------------------------------------------------------
\* Specification (the top-level temporal formula)
\*-----------------------------------------------------------------
TestSpec == Spec

\*-----------------------------------------------------------------
\* Invariants required by the .cfg file
\*-----------------------------------------------------------------
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====