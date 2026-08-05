---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\* Model-checking the sequential Misra reachability algorithm against a concrete,
\* finite graph. Nodes and edges are fixed in the CONSTANTS section of the .cfg,
\* and Succ is overridden by ConnectedToSomeButNotAll (the finite adjacency set the
\* algorithm actually uses). Sequence quantification is made finite by the
\* LimitedSeq override (bounded by the number of nodes). The .cfg also swaps in
\* the finite ConnectedToSomeButNotAll definition for Succ, so the model stays
\* checkable.
CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == << marked, frontier, pc >>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "ongoing"

Grow ==
  /\ frontier # {}
  /\ \E v \in frontier :
       /\ marked' = marked \cup {v}
       /\ frontier' = frontier \cup Succ[v]
  /\ pc' = "ongoing"

Done ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED << marked, frontier >>

Next == Grow \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Done)

Inv1 ==
  \A x \in frontier : x \notin marked

Inv2 ==
  \A x \in marked : x \in ReachableNodes(\A y \in Nodes : TRUE)

Inv3 ==
  \A x \in Nodes : x \in reachable(\A y \in Nodes : TRUE) => x \in marked

PartialCorrectness ==
  reached() => marked = Nodes

reached() == \A x \in Nodes : \E p \in LimitedSeq(Nodes) : p[1] = Root /\ p[Len(p)] = x /\ \A i \in 1 .. Len(p) - 1 : ConnectedToSomeButNotAll[p[i]](p[i + 1])

ReachableNodes(S) ==
  {x \in Nodes : \E p \in LimitedSeq(Nodes) : p[1] \in S /\ p[Len(p)] = x /\ \A i \in 1 .. Len(p) - 1 : ConnectedToSomeButNotAll[p[i]](p[i + 1])}

connected(x, y) == \E p \in LimitedSeq(Nodes) : p[1] = x /\ p[Len(p)] = y /\ \A i \in 1 .. Len(p) - 1 : ConnectedToSomeButNotAll[p[i]](p[i + 1])

Termination == <>(pc = "done")
====