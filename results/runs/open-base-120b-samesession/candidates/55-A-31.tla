---- MODULE MCEcho ----
EXTENDS Echo, Naturals, Sequences

\*----------------------------------------------------------------------
\* Concrete constants for the three‑node fully‑meshed graph
\*----------------------------------------------------------------------

CONSTANTS Node, initiator, R, NoNode

Node      == {"n1", "n2", "n3"}
initiator == "n1"
NoNode    == "NoNode"

\* Undirected, irreflexive, symmetric adjacency relation
R == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
     }

\*----------------------------------------------------------------------
\* Operators required for the .cfg substitution
\*----------------------------------------------------------------------

N1 == Node
I1 == initiator
R1 == R

\*----------------------------------------------------------------------
\* Test specification: prints the adjacency relation once at start‑up
\*----------------------------------------------------------------------

InitPrint == Init /\ Print(R)

\* The set of all state variables is assumed to be named `vars` in the
\* extended Echo module.  If Echo uses a different tuple name, replace
\* `vars` accordingly.
TestSpec == InitPrint /\ [] [Next]_vars

=============================================================================