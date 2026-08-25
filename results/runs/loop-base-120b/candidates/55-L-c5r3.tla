---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, initiator, R, NoNode

\* Concrete three‑node fully‑connected graph
N1 == {"n1", "n2", "n3"}

\* Deterministically chosen initiator
I1 == "n1"

\* Undirected, irreflexive adjacency relation (fully meshed)
R1 == (N1 \X N1) \ { <<n,n>> : n \in N1 }

\* Sentinel value for “no parent”, distinct from all nodes
ASSUME NoNode \notin N1

\* Instantiate the generic Echo specification with the concrete constants
INSTANCE Echo WITH
    Node      <- N1,
    initiator <- I1,
    R         <- R1,
    NoNode    <- NoNode

\* The specification to be checked
TestSpec == Echo!Spec
====