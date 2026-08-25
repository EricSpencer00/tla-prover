---- MODULE MCEcho ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, initiator, R, NoNode

\* Concrete bounded versions for the model checker (used via the .cfg substitutions)
N1 == {"A", "B", "C"}
I1 == "A"
R1 == {<<"A","B">>, <<"B","A">>,
       <<"A","C">>, <<"C","A">>,
       <<"B","C">>, <<"C","B">>}

\* The sentinel value for “no parent” must be distinct from all nodes
ASSUME NoNode \notin Node

\* Instantiate the generic Echo algorithm with the concrete constants
INSTANCE Echo WITH
    Node      <- Node,
    initiator <- initiator,
    R         <- R,
    NoNode    <- NoNode

\* Test variant: prints the adjacency relation at startup
TestSpec == (Print(R) = R) /\ Spec

====