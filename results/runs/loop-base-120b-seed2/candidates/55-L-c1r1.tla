---- MODULE MCEcho ----
EXTENDS Echo

\* ----------------------------------------------------------------------
\* Concrete constants for the three‑node fully‑meshed graph
\* ----------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* Assign concrete values to the constants inherited from Echo
ASSUME Node = {"n1", "n2", "n3"}
ASSUME initiator = "n1"
ASSUME NoNode = "NoNode"
ASSUME R = {
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
\* Specification required by the configuration
\* ----------------------------------------------------------------------
TestSpec == Spec

====