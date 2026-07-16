---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed: 
\*      <<"a", "a">> :> FALSE @@
\*      <<"a", "b">> :> TRUE  @@
\*      <<"b", "a">> :> TRUE  @@
\*      <<"b", "b">> :> FALSE @@
\*      <<"a", "c">> :> TRUE @@
\*      <<"c", "a">> :> TRUE @@
\*      <<"b", "c">> :> TRUE  @@
\*      <<"c", "b">> :> TRUE  @@
\*      <<"c", "c">> :> FALSE
\* More concisely defined as:
R1 == [edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE]

\* To get a graph that satisfies the assumptions in Echo, we simply 
\* define R to be:
R2 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Choose one of the two possible definitions for the edge relation.
R == IF R1 \in [N1 \X N1 -> BOOLEAN] THEN R1 ELSE R2

\* The original specification is called Spec in the Echo module.
\* We expose it as the top‑level predicate for TLC.
SpecInit == Spec

\* Print R to stdout at startup (optional, does not affect the model).
TestSpec == PrintT(R) \/ SpecInit

=============================================================================