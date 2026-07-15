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

\* The original specification refers to a constant R that is
\* defined in the imported module Echo.  We need to bind that
\* constant to the concrete relation we constructed above.  The
\* simplest way to do this while preserving all original behaviour
\* is to use a CONSTANT ASSIGNMENT in the .cfg file.  Because we are
\* required to produce a self‑contained module, we expose a variable
\* that mirrors the constant and initialise it in the Init predicate.
VARIABLE R

\* Init now assigns the variable R the concrete relation R2.
Init == /\ R = R2

\* The rest of the behaviour is inherited from Echo via the Spec
\* definition (which refers to Init and Next).  We keep that definition
\* unchanged and simply conjoin it with our Init.
Spec == Init /\ Next

\* Print R to stdout at startup.
TestSpec == PrintT(R) \/ Spec

====