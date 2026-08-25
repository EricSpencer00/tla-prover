---- MODULE MCEcho ----
EXTENDS Echo

\* ----------------------------------------------------------------------
\* Concrete constants for the three‑node fully‑meshed graph
\* ----------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

Node == {"n1", "n2", "n3"}
initiator == "n1"
NoNode == "NoNode"

R == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
     }

\* ----------------------------------------------------------------------
\* Operators used by the .cfg substitution
\* ----------------------------------------------------------------------
N1 == Node
I1 == initiator
R1 == R

\* ----------------------------------------------------------------------
\* Specification and invariants required by the configuration
\* ----------------------------------------------------------------------
TestSpec == Spec

TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

\* (Optional aliases – not required by the .cfg but useful for completeness)
Init == Echo!Init
Next == Echo!Next

====