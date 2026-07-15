---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* Pick an initiator arbitrarily from N1.
I1 == CHOOSE n \in N1 : TRUE

\* Fully meshed (undirected) graph: edge (x,y) is TRUE iff x \neq y.
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] 
                                THEN FALSE
                                ELSE TRUE ]

\* Choose a relation that satisfies the assumptions required by Echo.
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] : 
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Print the chosen relation and then behave like the underlying Echo spec.
TestSpec == PrintT(R) \/ Spec
=============================================================================