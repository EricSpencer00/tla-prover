---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets
\* picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* A fully meshed irreflexive symmetric relation on N1.
R1 == [ edge \in (N1 \X N1) |-> 
          IF edge[1] = edge[2] 
          THEN FALSE 
          ELSE TRUE ]

\* An alternate definition that satisfies the Echo assumptions.
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] : 
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Print R1 (or R2) at startup and then run the base specification.
TestSpec == PrintT(R1) \/ Spec

=============================================================================