---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

\*--------------------------------------------------------------
\* Concrete instantiation for model checking
\*--------------------------------------------------------------

N1 == {"n1", "n2", "n3"}

I1 == "n1"

R1 == {
        << "n1", "n2" >>,
        << "n2", "n1" >>,
        << "n1", "n3" >>,
        << "n3", "n1" >>,
        << "n2", "n3" >>,
        << "n3", "n2" >>
      }

\* NoNode must be distinct from every node in the graph
ASSUME NoNode \notin N1

\*--------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------

TestSpec == Init /\ [][Next]_vars

\*--------------------------------------------------------------
\* Invariants (defined in the extended Echo module)
\*--------------------------------------------------------------

\* TypeOK      \* defined in Echo
\* AncestorProperties \* defined in Echo

====