---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed.
R1 == [edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE]

\* Choose a relation that satisfies the assumptions required by Echo.
R2 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Define the relation used by Echo.
R == R2

\* Print R to stdout at startup.
TestSpec == PrintT(R) \/ Spec

\* The initial state predicate required by TLC.
Init == TestSpec

====