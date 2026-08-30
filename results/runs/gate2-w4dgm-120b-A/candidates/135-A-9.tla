---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

\* Model-checkable (finite) version of the reachability definition's path
\* quantifier: sequences of nodes of bounded length instead of an unrestricted
\* set of paths, which would be infinite and uncheckable.
LimitedSeq(S, k) == {s \in Seq(S) : Len(s) <= k}

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "idle"

\* The sequential reachability process: pick a frontier node, materialize its
\* successors into the marked set, and move that node out of the frontier.
Step(n) ==
    /\ pc = "idle"
    /\ n \in frontier
    /\ marked' = marked \cup Succ[n]
    /\ frontier' = (frontier \ {n}) \cup Succ[n]
    /\ pc' = "running"

Settle ==
    /\ pc = "running"
    /\ pc' = "idle"
    /\ UNCHANGED <<marked, frontier>>

Terminate ==
    /\ frontier = {}
    /\ pc # "done"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes : Step(n)
    \/ Settle
    \/ Terminate
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Settle) /\ WF_vars(Terminate)

\* Reachability invariants: successor closure, reachability decomposition, and
\* reachable set equality, together with the type invariant.
Inv1 == \A n \in marked : Succ[n] \subseteq marked
Inv2 == \A n \in frontier : (Succ[n] \cup {n}) \cap marked = {}
Inv3 == marked = {n \in Nodes : \E p \in LimitedSeq(Nodes, Cardinality(Nodes)) : p[1] = Root /\ p[Len(p)] = n}

\* Partial correctness captured as a state invariant (property in the .cfg).
PartialCorrectness == marked = {n \in Nodes : \E p \in LimitedSeq(Nodes, Cardinality(Nodes)) : p[1] = Root /\ p[Len(p)] = n}

Termination == <> (pc = "done")

====