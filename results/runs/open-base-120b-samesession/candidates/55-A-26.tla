---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

\* Concrete instantiations for the three‑node fully‑meshed graph
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

\* Sentinel value distinct from all nodes
ASSUME NoNode \notin N1

\* Initial state: inherit Echo's Init and print the adjacency relation
Init == Echo!Init /\ Print(R)

\* Step relation: unchanged from Echo
Next == Echo!Next

\* Full specification (used by the .cfg file)
Spec == Init /\ [][Next]_(Echo!vars)

TestSpec == Spec

====