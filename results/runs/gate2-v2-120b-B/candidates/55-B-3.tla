---- MODULE MCEcho ----------
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets
\* picked as the initiator.
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

\* To get a graph that satisfies the
\* assumptions in Echo, we simply 
\* define R to be:
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] : 
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

VARIABLE R

\* The original specification expected `R` to be defined in the
\* imported module `Echo`.  Here we bind `R` to the concrete
\* relation `R2` that we constructed above, preserving the intended
\* semantics.
Init == R = R2

\* The rest of the behavior is delegated to the original `Spec`
\* from module `Echo`, but with `R` fixed by the above initialization.
Next == Spec

Spec == Init /\ [][Next]_<<R>>

\* Print R to stdout at startup (optional, does not affect semantics).
TestSpec == PrintT(R) \/ Spec        

====