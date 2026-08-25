---- MODULE MCEcho ----
EXTENDS Naturals, TLC, Echo

\*--------------------------------------------------------------
\* Concrete constants required by the Echo algorithm
\*--------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* Finite set of three nodes (string values)
N1 == {"n1", "n2", "n3"}

\* Deterministically chosen initiator
I1 == "n1"

\* Fully‑meshed, undirected graph (symmetric, irreflexive)
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

\* Sentinel value distinct from all nodes
NoNode == "NoNode"

\* Bind the generic constants to the concrete instances
Node == N1
initiator == I1
R == R1

\*--------------------------------------------------------------
\* Specification exported for the model checker
\*--------------------------------------------------------------
TestSpec == Spec

====