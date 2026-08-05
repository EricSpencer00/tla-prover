---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a","b","c"}

\* The initiator is nondeterministically chosen from N1.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed except for self-loops.
\*      <<"a","a">> :> FALSE, <<"b","b">> :> FALSE, <<"c","c">> :> FALSE,
\*      all other pairs are TRUE.  More concisely:
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE ]

\* To get a graph that satisfies the assumptions in Echo, we simply
\* choose any relation in the full relation space that is connected,
\* symmetric, and irreflexive:
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] :
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Print R to stdout at startup.
TestSpec == PrintT(R) \/ Spec
====