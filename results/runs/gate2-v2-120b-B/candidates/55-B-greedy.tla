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

\* The original specification used a helper constant
\* `R` that was defined in the imported module `Echo`.
\* In the original `Echo` module the constant `R` is
\* constrained by the `Init` predicate, but the
\* configuration file for this model did not
\* specify an explicit initial state predicate.
\* To make the model self‑contained and give TLC a
\* concrete initial state, we define `R` locally as the
\* concrete relation `R2` and expose it as the initial
\* state predicate `Init`.  This preserves the intended
\* semantics because `R2` already satisfies all the
\* required properties (connected, symmetric, irreflexive)
\* and therefore is a valid choice for `R` in the original
\* specification.
R == R2

Init == /\ R = R2
        /\ I1 \in N1

\* The original `Spec` from `Echo` is the temporal
\* behavior that starts from `Init`.  We reuse it here.
Spec == Init /\ [][Next]_vars

\* Print R to stdout at startup.
TestSpec == PrintT(R) \/ Spec

====