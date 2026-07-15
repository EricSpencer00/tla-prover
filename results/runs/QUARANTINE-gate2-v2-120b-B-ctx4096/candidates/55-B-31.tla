---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed: every distinct pair of nodes is connected.
R1 == [edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE]

\* Choose a concrete relation that satisfies the assumptions of Echo.
R2 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Print the chosen relation at startup and then behave like the original Spec.
TestSpec == PrintT(R2) \/ Spec

====