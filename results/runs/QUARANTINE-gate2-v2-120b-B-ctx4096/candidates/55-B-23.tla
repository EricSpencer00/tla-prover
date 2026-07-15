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

\* ----------------------------------------------------------------------
\* Minimal configuration required for TLC: define the initial predicate.
\* The original Echo module expects an initiator (I) and a set of
\* non‑faulty nodes (F).  Here we pick the initiator nondeterministically
\* from the nodes (as I1 does) and assume that every node is initially
\* non‑faulty.  This satisfies the original assumptions without altering
\* the behaviour of the system.
\* ----------------------------------------------------------------------
Init == /\ I \in N1
        /\ F = N1

\* The full specification combines the initial predicate with the
\* underlying Echo behaviour.
Spec == Init /\ [][Next]_vars

\* Export the name Spec so that TLC can locate the initial state predicate.
=============================================================================