---- MODULE MCEcho ----
EXTENDS Echo, FiniteSets, Naturals

\*----------------------------------------------------------------------
\* A tiny graph with three nodes.
\*----------------------------------------------------------------------
N1 == {"a", "b", "c"}

\*----------------------------------------------------------------------
\* The initiator node (any node from N1).
\*----------------------------------------------------------------------
I1 == CHOOSE n \in N1 : TRUE

\*----------------------------------------------------------------------
\* Fully meshed graph (no self‑loops, all other edges present).
\*----------------------------------------------------------------------
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE ]

\*----------------------------------------------------------------------
\* Choose a relation that satisfies the Echo module's assumptions.
\*----------------------------------------------------------------------
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] :
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\*----------------------------------------------------------------------
\* R is defined to be R2 (the chosen relation).  This definition is
\* used by the imported Echo module.
\*----------------------------------------------------------------------
R == R2

\*----------------------------------------------------------------------
\* Print R to stdout at startup, then behave like the Echo specification.
\*----------------------------------------------------------------------
TestSpec == PrintT(R) \/ Spec

=========================