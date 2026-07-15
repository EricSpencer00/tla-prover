---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed:
\*   edges between distinct nodes are TRUE,
\*   self‑edges are FALSE.
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE ]

\* Choose a relation that satisfies the assumptions required by Echo.
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] :
          /\ IsConnected(r, N1)
          /\ IsSymmetric(r, N1)
          /\ IsIrreflexive(r, N1)

\* Export the relation that Echo expects to be named R,
\* and make the initial state predicate explicit for TLC.
R == R2

Init == R = R2

\* The rest of the behavior is taken from Echo.
Next == Echo!Next

Spec == Init /\ [][Next]_<<R>>

\* Print R to stdout at startup (does not affect the model).
TestSpec == PrintT(R) \/ Spec

=============================================================================