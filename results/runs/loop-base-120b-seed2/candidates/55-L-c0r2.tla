---- MODULE MCEcho ----
EXTENDS TLC

CONSTANTS Node, initiator, R

\* Concrete definitions that the .cfg file will substitute for the constants
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

\* Sentinel value distinct from all nodes
NoNodeVal == "NoNode"

\* Instantiate the generic Echo specification with the (as‑yet‑unbound) constants.
INSTANCE Echo WITH
    Node      <- Node,
    initiator <- initiator,
    R         <- R,
    NoNode    <- NoNodeVal

\* The specification required by the .cfg file.
TestSpec == Echo!Init /\ [][Echo!Next]_Echo!vars

\* Invariants required by the .cfg file.
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties
====