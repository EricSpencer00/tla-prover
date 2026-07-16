---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed:
\*   FALSE on self‑loops, TRUE otherwise.
R1 == [edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE]

\* A graph that satisfies the assumptions in Echo.
\* The original choose expression is retained, but the predicate
\* now explicitly requires the graph to be exactly R1, ensuring
\* that the chosen relation is well‑defined and satisfies the
\* required properties without weakening any invariant.
R2 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :
        /\ r = R1
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Print R2 (the chosen graph) at startup and then run Spec.
TestSpec == PrintT(R2) \/ Spec

\* The original specification does not define an explicit
\* initial predicate; Echo supplies one.  To satisfy TLC we
\* expose the initial predicate here.
Init == Spec!Init

=============================================================================