---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

\* Concrete three-node fully‑connected graph
N1 == {"n1", "n2", "n3"}

\* Deterministically chosen initiator
I1 == "n1"

\* Undirected, irreflexive adjacency relation (fully meshed)
R1 == { <<a, b>> : a \in N1 /\ b \in N1 /\ a # b }

\* Sentinel value for “no parent”, distinct from all nodes
NoNode == "None"

\* Ensure the sentinel is not a node of the graph
ASSUME NoNode \notin N1

\* Instantiate the generic Echo specification with the concrete constants
INSTANCE Echo WITH
    Node <- N1,
    initiator <- I1,
    R <- R1,
    NoNode <- NoNode

\* The specification to be checked
TestSpec == Echo!Spec

\* Safety invariants inherited from Echo
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====