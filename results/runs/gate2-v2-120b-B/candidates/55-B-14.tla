---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets
\* picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed (irreflexive, symmetric, connected):
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] 
                                THEN FALSE
                                ELSE TRUE ]

\* We need an initial-state predicate for TLC.
\* The original spec used `TestSpec == PrintT(R) \/ Spec`, which does
\* not define any initial condition.  To preserve the intended
\* behaviour we keep the original actions but add a trivial
\* `Init` that simply sets the relation `R` to the fully‑meshed
\* graph `R1`.  This satisfies all assumptions required by the
\* imported `Echo` module and does not weaken any invariants.
Init == R = R1

\* The rest of the spec (the actions, safety invariant, etc.) are
\* inherited from `Echo`.  We therefore expose the original `Spec`
\* but conjoin it with the new `Init` so that TLC has a proper
\* initial‑state predicate.
SpecWithInit == Init /\ Spec

\* For completeness we preserve the original `TestSpec` definition,
\* although it is no longer used by the model checker.
TestSpec == PrintT(R) \/ SpecWithInit

\* The exported specification for TLC.
Spec == SpecWithInit
====