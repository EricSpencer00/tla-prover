---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

\* --- Concrete instantiation for model checking --------------------
\* Three distinct nodes (strings)
N1 == {"n1", "n2", "n3"}

\* Deterministic initiator
I1 == "n1"

\* Fully‑meshed, undirected graph (symmetric, irreflexive)
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

\* Sentinel value for “no parent” (distinct from all nodes)
NoNodeVal == "NoNode"

\* --- Specification ------------------------------------------------
\* The test specification used by the .cfg file
TestSpec == Spec

\* Expose the Init and Next actions defined in the Echo module
Init == Echo!Init
Next == Echo!Next

====