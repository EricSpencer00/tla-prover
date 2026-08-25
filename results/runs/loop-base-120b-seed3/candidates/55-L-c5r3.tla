---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

\* Concrete definitions that the .cfg file will substitute for the constants
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<<"n1","n2">>, <<"n2","n1">>,
       <<"n1","n3">>, <<"n3","n1">>,
       <<"n2","n3">>, <<"n3","n2">>}
NoNode == "NoNode"

\* Instantiate the generic Echo specification with the concrete values above
INSTANCE Echo WITH
    Node      <- N1,
    initiator <- I1,
    R         <- R1,
    NoNode    <- NoNode

\* Expose the invariants required by the .cfg file
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

\* Specification required by the .cfg file.  The Print operator causes the
\* adjacency relation to be written to the TLC console at the start of
\* each run.
TestSpec == Spec /\ Print(R, "R")
====