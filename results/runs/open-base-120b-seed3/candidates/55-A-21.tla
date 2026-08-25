---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, Sequences, Echo

CONSTANTS Node, initiator, R, NoNode

\* Concrete three‑node fully‑meshed graph (used via the cfg substitution operators)
N1 == {"n1", "n2", "n3"}

I1 == "n1"

R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

\* Sentinel value distinct from all nodes
ASSUME NoNode \notin N1

\* Specification to be checked by the model checker
TestSpec == Spec

\* The invariants are inherited from the Echo module; they are therefore
\* available under the required names without further definition.
====