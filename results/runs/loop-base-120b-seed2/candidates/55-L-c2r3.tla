---- MODULE MCEcho ----
EXTENDS Echo

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
NoNode == "NoNode"
ASSUME NoNode \notin N1

\*--------------------------------------------------------------
\* Bind the abstract constants to the concrete definitions
\*--------------------------------------------------------------

Node == N1
initiator == I1
R == R1

\*--------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------

TestSpec == Init /\ [][Next]_vars

====