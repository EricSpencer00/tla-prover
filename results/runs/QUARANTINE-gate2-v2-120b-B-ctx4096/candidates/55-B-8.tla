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

\* The original \"TestSpec\" definition attempted to
\* combine a side‑effect (PrintT) with the spec using logical
\* disjunction.  This caused the configuration file to lack an
\* explicit initial state predicate, leading TLC to abort.
\* We replace it with an explicit definition of the initial state
\* that preserves the intended behavior: the system starts in the
\* state described by Spec, and the relation R is printed once at
\* startup (the print is retained as a harmless side‑effect).
Init == Spec /\ PrintT(R)

\* The rest of the specification (variables, next‑state relation, etc.)
\* are inherited from Echo via the imported module.
SpecInit == Init

====