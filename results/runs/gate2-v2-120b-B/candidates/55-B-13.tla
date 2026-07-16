---- MODULE MCEcho ----
EXTENDS Echo, FiniteSets, Relation

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

\* The specification of Echo expects an initial state predicate.
\* We reuse the generic initialization from Echo, supplying the
\* concrete graph R2 and the initiator I1.
Init == InitEcho(R2, I1)

\* The behavior of Echo lifted to our concrete graph.
Next == NextEcho(R2, I1)

\* Full specification (initial predicate and next-state relation).
Spec == Init /\ [][Next]_<<I1, R2>>

\* Print R to stdout at startup without affecting the spec.
TestSpec == PrintT(R2) \/ Spec

\* The invariant required by Echo (the one that
\* checks that all nodes eventually learn the message).
Inv == EchoInv(R2, I1)

====