---- MODULE MCEcho ----
EXTENDS Naturals, Sequences

\* ----------------------------------------------------------------------
\* Constants required by the Echo specification
\* ----------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* Concrete values that the .cfg file will substitute for the constants
\* ----------------------------------------------------------------------
N1 == {"n1", "n2", "n3"}
I1 == "n1"
NoNode == "NoNode"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "c3", "c2" >>
      }

\* ----------------------------------------------------------------------
\* Instantiate the generic Echo specification with the concrete values
\* ----------------------------------------------------------------------
INSTANCE Echo WITH
    Node      <- N1,
    initiator <- I1,
    R         <- R1,
    NoNode    <- NoNode

\* ----------------------------------------------------------------------
\* Specification required by the .cfg file
\* ----------------------------------------------------------------------
TestSpec == Spec

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg file (already defined in Echo)
\* ----------------------------------------------------------------------
\* TypeOK    == Echo!TypeOK
\* AncestorProperties == Echo!AncestorProperties

====