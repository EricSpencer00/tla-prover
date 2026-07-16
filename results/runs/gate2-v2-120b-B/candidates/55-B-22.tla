---- MODULE MCEcho ----
EXTENDS Echo, Naturals, FiniteSets, Relation, TLC

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets
\* picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed:
\*   self‑edges are FALSE, all other edges are TRUE.
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] THEN FALSE ELSE TRUE ]

\* To obtain a graph that satisfies the assumptions in Echo,
\* we simply define R to be a concrete, fully‑meshed relation.
R2 == R1

\* The initial state predicate required by TLC.
Init == /\ R = R2
        /\ Initiator = I1

\* The rest of the behavior is delegated to Echo's definition.
Next == Echo!Next

\* The full specification.
Spec == Init /\ [][Next]_<<R, Initiator>>

\* Print R to stdout at startup (has no effect on the model).
TestSpec == PrintT(R) \/ Spec

====