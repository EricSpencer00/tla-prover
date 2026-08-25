---- MODULE MCEcho ----
EXTENDS Echo, TLC

\*-----------------------------------------------------------------
\* Concrete constants for the three‑node fully connected graph
\*-----------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

Node == {"N1", "N2", "N3"}

initiator == "N1"

NoNode == "NoNode"

R == {
        << "N1", "N2" >>, << "N2", "N1" >>,
        << "N1", "N3" >>, << "N3", "N1" >>,
        << "N2", "N3" >>, << "N3", "N2" >>
     }

\*-----------------------------------------------------------------
\* Operators required by the .cfg file (substituted for the constants)
\*-----------------------------------------------------------------
N1 == Node
I1 == initiator
R1 == R

\*-----------------------------------------------------------------
\* Specification derived from the Echo module
\*-----------------------------------------------------------------
TestSpec == Spec

\*-----------------------------------------------------------------
\* Invariants required by the .cfg file
\*-----------------------------------------------------------------
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

\*-----------------------------------------------------------------
\* Optional test variant that prints the adjacency relation at start‑up
\* (executed once by TLC when the initial state is generated)
\*-----------------------------------------------------------------
InitPrint ==
    /\ TRUE
    /\ Print("Adjacency relation R = " \o ToString(R))

====