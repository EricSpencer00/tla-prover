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
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] 
                                THEN FALSE
                                ELSE TRUE ]

\* To get a graph that satisfies the assumptions in Echo, we simply 
\* define R to be:
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] : 
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* The original specification used a helper constant TestSpec that only
\* printed the chosen graph.  TLC requires an explicit initial state
\* predicate, so we expose the chosen graph as a constant (R) and let
\* the imported Echo module provide its Init predicate.  This change
\* preserves the intended behaviour while satisfying the tool's
\* requirements.
CONSTANT R

\* Bind the constant R to the graph we constructed above.
R == R2

\* The specification exported for TLC is the one defined in Echo,
\* with the added constant binding above.
Spec == Init /\ [][Next]_vars

====