---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets
\* picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed.  The definition below
\* creates a relation that is true for every pair of distinct
\* nodes and false for self‑loops.
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE ]

\* To obtain a relation that satisfies the assumptions in
\* the imported Echo module (connected, symmetric, irreflexive),
\* we simply choose such a relation.  With the concrete N1 above,
\* the only relation that meets all three conditions is R1, so we
\* bind R to that concrete relation.
R == R1

\* Print the chosen relation at startup and then behave as the
\* original specification.
TestSpec == PrintT(R) \/ Spec
=====================================================