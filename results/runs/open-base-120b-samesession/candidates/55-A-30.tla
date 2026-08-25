---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, Sequences, Echo

\*-------------------------------------------------
\* Concrete constants for the three‑node fully‑meshed graph
\*-------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* Operators that the .cfg file will substitute for the constants
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

\* Bind the constants to the concrete values for model checking
ASSUME Node = N1
ASSUME initiator = I1
ASSUME R = R1
ASSUME NoNode \notin Node

\*-------------------------------------------------
\* Specification entry point required by the .cfg file
\*-------------------------------------------------
TestSpec == Echo!Spec

\*-------------------------------------------------
\* Invariants required by the .cfg file
\*-------------------------------------------------
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====