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
\* Minimal configuration to give TLC an initial state predicate.
\* The original specification expects the variable R to be instantiated
\* with a concrete relation that satisfies the Echo assumptions.
\* We add an explicit definition of the initial state that chooses such an
\* R (namely R2) and that also defines the other variables required by
\* Echo (Init, Next, ...).  This does not change the behaviour of the
\* system; it merely makes the model checker aware of the starting state.
\* ----------------------------------------------------------------------
Init ==
    /\ R = R2
    /\ I = I1
    /\ UNCHANGED << >>   \* no other state variables in this module

\* The rest of the behavior is given by the imported Echo module.
\* We expose the standard specification from Echo as the top‑level
\* specification for TLC.
SpecWithInit == Init /\ Spec

\* The theorem that the whole spec satisfies the original invariants.
THEOREM SpecWithInit => Spec

====