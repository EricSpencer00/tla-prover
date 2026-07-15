---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed (irreflexive, symmetric, connected).
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE ]

\* Let R be this fully meshed graph.
R == R1

\* The original specification (from Echo) expects an initial state predicate.
\* We define it minimally by requiring the initiator to be one of the nodes.
Init == I1 \in N1

\* The overall specification combines the initial predicate with the rest of Echo.
Spec == Init /\ Echo

\* Print R to stdout at startup.
TestSpec == PrintT(R) \/ Spec
====