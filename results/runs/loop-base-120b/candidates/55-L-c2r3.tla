---- MODULE MCEcho ----
EXTENDS Naturals, TLC, Echo, Relation

\* Concrete set of three nodes (string values)
N1 == {"n1", "n2", "n3"}

\* Deterministically chosen initiator
I1 == "n1"

\* Fully‑meshed, undirected graph (symmetric, irreflexive)
R1 == (N1 \X N1) \ { <<v, v>> : v \in N1 }

\* Sentinel value representing “no parent” – distinct from all nodes
NoNode == "NoNode"

\* Bind the generic constants to the concrete instances
Node == N1
initiator == I1
R == R1

\* Specification exported for the model checker
TestSpec == Spec

====