---- MODULE MCEcho ----
EXTENDS Echo, TLC

\* ----------------------------------------------------------------------
\* Constant declarations (required by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* Concrete definitions that the .cfg substitutes for the constants
\* ----------------------------------------------------------------------
N1 == {"n1", "n2", "n3"}

I1 == "n1"

R1 == { << "n1", "n2" >>, << "n1", "n3" >>,
        << "n2", "n1" >>, << "n2", "n3" >>,
        << "n3", "n1" >>, << "n3", "n2" >> }

\* A sentinel value distinct from all nodes
NoNode == "NoNode"

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg file (exposed from Echo)
\* ----------------------------------------------------------------------
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

\* ----------------------------------------------------------------------
\* Specification required by the .cfg file
\* ----------------------------------------------------------------------
TestSpec == Spec
====