---- MODULE MCEcho ----
EXTENDS Echo, TLC

\*-----------------------------------------------------------------
\*  Constants (to be instantiated by the .cfg file)
\*-----------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\*-----------------------------------------------------------------
\*  Concrete definitions used by the configuration (substituted for
\*  the abstract constants above)
\*-----------------------------------------------------------------
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { << "n1", "n2" >>,
        << "n2", "n1" >>,
        << "n1", "n3" >>,
        << "n3", "n1" >>,
        << "n2", "n3" >>,
        << "n3", "n2" >> }

\*  Sentinel value distinct from all nodes
NoNode == "NoNode"

\*  Ensure the sentinel is not a node
ASSUME NoNode \notin N1

\*-----------------------------------------------------------------
\*  Test variant: print the adjacency relation at start‑up
\*-----------------------------------------------------------------
PrintAdj == Print("\nAdjacency R = " \o ToString(R))

\*  The underlying Echo specification
Init == Echo.Init /\ PrintAdj
Next == Echo.Next

\*  The specification required by the .cfg file
TestSpec == Init /\ [][Next]_<<>>  \* the variable set is internal to Echo

\*  Invariants required by the .cfg file
TypeOK == Echo.TypeOK
AncestorProperties == Echo.AncestorProperties

=============================================================================