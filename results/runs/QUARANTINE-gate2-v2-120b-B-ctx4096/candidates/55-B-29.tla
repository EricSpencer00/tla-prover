---- MODULE MCEcho ----
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

\* Print R to stdout at startup.
TestSpec == PrintT(R) \/ Spec

\* ---------------------------
\* The original specification \"Echo\" expects an
\* initial state predicate named Init. The original
\* MCEcho module only defined a constant I1 but never
\* bound it to the Init predicate of Echo.  This caused
\* TLC to report that the configuration file did not
\* specify the initial state predicate.
\*
\* We fix the problem by defining Init as the conjunction
\* of Echo's Init predicate and the concrete choice of the
\* initiator I1.  This preserves the original intent of the
\* model (the initiator can be any node in N1) while providing
\* the required initial state for TLC.
\* ---------------------------
Init == Echo!Init /\ I = I1

\* The rest of the behavior is exactly the specification
\* from Echo, with the concrete graph R2.
Spec == /\ Init
        /\ [][Echo!Next]_<<I, R>>

====