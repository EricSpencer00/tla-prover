---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets
\* picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed:
R1 == [ edge \in (N1 \X N1) |-> 
          IF edge[1] = edge[2] 
          THEN FALSE 
          ELSE TRUE ]

\* To get a graph that satisfies the
\* assumptions in Echo, we simply 
\* define R to be:
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] :
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Alias the relation expected by Echo.
R == R2

\* Print R to stdout at startup.
TestSpec == PrintT(R) \/ Spec

\* Minimal initial predicate required by TLC.
Init == TRUE
================