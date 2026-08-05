---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes, each starting a flood.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed, so each edge is
\* bidirectional and none is reflexive:
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE ]

\* To get a graph that satisfies the assumptions in Echo,
\* we define R as the CHOOSE of any symmetric,
\* irreflexive, connected relation on N1 -- it works out to be R1.
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] :
        /\ IsConnected(r, N1) /\ IsSymmetric(r, N1) /\ IsIrreflexive(r, N1)

\* Print the relation to stdout at startup and start the flood.
TestSpec == PrintT(R2) /\ Spec
====