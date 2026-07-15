---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed.
R1 == [edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE]

\* Choose a graph that satisfies the assumptions in Echo.
R2 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* The specification used by TLC.
Spec == Spec(R2)

\* Print R to stdout at startup (optional, does not affect Spec).
TestSpec == PrintT(R2) \/ Spec

====