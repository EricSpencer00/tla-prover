---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed: all distinct pairs are connected.
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE ]

\* To get a graph that satisfies the assumptions in Echo, we simply
\* define R to be a relation that is connected, symmetric, and irreflexive.
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] :
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Print R to stdout at startup.
TestSpec == PrintT(R2) \/ Spec

\* The initial state predicate required by TLC.
\* It matches the initial predicate of the imported Echo specification.
Init == Spec!Init

=============================================================================