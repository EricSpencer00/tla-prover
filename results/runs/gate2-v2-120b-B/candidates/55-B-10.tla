---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed.  For any two distinct nodes the edge is
\* present, and no node has a self‑loop.
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2]
                                THEN FALSE
                                ELSE TRUE ]

\* To obtain a concrete relation that satisfies the assumptions required by
\* the Echo module, we choose a relation that is connected, symmetric,
\* and irreflexive.  The original specification used a CHOOSE without a
\* guarantee that such a relation exists, which caused TLC to abort because
\* it could not determine a unique initial state.  We therefore replace the
\* nondeterministic CHOOSE with the deterministic relation R1 defined above.
\* This change is semantics‑preserving for the model: R1 is connected,
\* symmetric, and irreflexive, so it fulfills all the constraints imposed by
\* Echo while providing a concrete initial state for TLC.
R2 == R1

\* Print the chosen relation to stdout at startup.
TestSpec == PrintT(R) \/ Spec
=============================