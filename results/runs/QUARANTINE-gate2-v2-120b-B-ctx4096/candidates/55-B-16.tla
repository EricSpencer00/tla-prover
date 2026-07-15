---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed:
\*    edge between distinct nodes is TRUE, self‑edges are FALSE.
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE ]

\* Choose a relation that satisfies the assumptions required by Echo.
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] :
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* The specification that Echo expects.
Spec == EchoSpec(R2, I1)

\* Print the chosen relation at startup (not part of the behavior).
TestSpec == PrintT(R2) \/ Spec

=============================================================================