---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed: << <<"a", "a">> :> FALSE,
\* <<"a", "b">> :> TRUE, <<"a", "c">> :> TRUE, etc.  More concisely:
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE ]

\* But we must pick an r that is a proper undirected graph (connected,
\* symmetric, irreflexive), so we CHOOSE it from just those relations:
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] :
          /\ IsConnected(r, N1) /\ IsSymmetric(r, N1) /\ IsIrreflexive(r, N1)

\* Print R to stdout at startup and run the spec.
TestSpec == PrintT(R) \/ Spec

\* TLC needs an explicit Init (our Spec already has one).
Init == Init
====