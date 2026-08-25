---- MODULE MCEcho ----
EXTENDS Echo, TLC

\* ----------------------------------------------------------------------
\* Constants that will be instantiated by the .cfg file
\* ----------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* Concrete definitions that the .cfg substitutes for the above constants
\* ----------------------------------------------------------------------
N1 == {"n1", "n2", "n3"}

I1 == "n1"

R1 == { << "n1", "n2" >>, << "n1", "n3" >>,
        << "n2", "n1" >>, << "n2", "n3" >>,
        << "n3", "n1" >>, << "n3", "n2" >> }

NoNode == "None"

\* ----------------------------------------------------------------------
\* Specification, invariants and properties required by the .cfg file
\* ----------------------------------------------------------------------
TestSpec == Spec

TypeOK == Echo!TypeOK

AncestorProperties == Echo!AncestorProperties
=============================================================================