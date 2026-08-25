---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

\* Concrete definitions that the .cfg file will substitute for the constants
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

\* Sentinel value distinct from all nodes
NoNode == "NoNode"

\* Instantiate the generic Echo specification with the (as‑yet‑unbound) constants.
\* The .cfg file will bind Node, initiator, and R to N1, I1, and R1 respectively.
INSTANCE Echo AS E WITH
    Node      <- Node,
    initiator <- initiator,
    R         <- R,
    NoNode    <- NoNode

\* Test variant: print the adjacency relation at start‑up.
Init == E!Init /\ Print(R)
Next == E!Next

\* The specification required by the .cfg file.
TestSpec == Init /\ [][Next]_E!vars

\* Invariants required by the .cfg file.
TypeOK == E!TypeOK
AncestorProperties == E!AncestorProperties

====