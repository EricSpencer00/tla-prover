---- MODULE MCEcho ----
EXTENDS Echo, FiniteSets

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* Concrete definitions used for substitution in the .cfg file
\* ----------------------------------------------------------------------
N1 == {"A", "B", "C"}                \* the three nodes
I1 == "A"                            \* deterministic initiator
R1 == {
        << "A", "B" >>, << "B", "A" >>,
        << "A", "C" >>, << "C", "A" >>,
        << "B", "C" >>, << "C", "B" >>
      }                               \* fully‑meshed undirected graph

\* ----------------------------------------------------------------------
\* Aliases to the definitions coming from the Echo specification
\* ----------------------------------------------------------------------
Init == Echo!Init
Next == Echo!Next
TestSpec == Echo!Spec

\* ----------------------------------------------------------------------
\* Invariants required by the configuration
\* ----------------------------------------------------------------------
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====