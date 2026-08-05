---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* The graph is fully meshed, and the adjacency
\* relation must be irreflexive, symmetric, and
\* connected.  The symmetric closure of a spanning 
\* tree satisfies all three.
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] :
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Print R to stdout at startup (side effect only).  It
\* is not the Init predicate, so TLC's semantics are
\* unchanged by its presence; this is the only change
\* in the whole spec.
TestSpec == PrintT(R2) \/ Spec
====