---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* Reachability via Misra's variant of breadth-first search, where the marked
\* set and the frontier are allowed to overlap.
CONSTANTS Nodes, Root, Succ
\* ConnectedToSomeButNotAll is the operator the .cfg substitutes for Succ.
ConnectedToSomeButNotAll == {y \in Nodes : \E x \in Nodes : y \in Succ[x]}
LimitedSeq == {s \in Sequences : Len(s) <= 3}

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The single loop action, with its two cases from the frontier.
Explore ==
  /\ frontier # {}
  /\ pc = "running"
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Explore)

\* Invariant (1): every successor of a marked node is already marked or in the frontier.
Inv1 == \A x \in Nodes : x \in marked => ConnectedToSomeButNotAll[x] \subseteq (marked \cup frontier)

\* Invariant (2): the reachable-from-marked-or-frontier set equals the reachable-from-union set.
Inv2 == {y \in Nodes : \E x \in (marked \cup frontier) : y \in ConnectedToSomeButNotAll[x]}
          = {y \in Nodes : \E x \in (marked \cup frontier) : y \in ConnectedToSomeButNotAll[x]}

\* Invariant (3): the root's reachable set is the marked set plus the frontier's reach.
Inv3 == {y \in Nodes : \E x \in marked : y \in ConnectedToSomeButNotAll[x]}
          \cup {y \in Nodes : \E x \in frontier : y \in ConnectedToSomeButNotAll[x]}
          = {y \in Nodes : \E x \in Nodes : y \in ConnectedToSomeButNotAll[x]}

\* Partial correctness: termination means marked is exactly the reachable set.
PartialCorrectness ==
  (pc = "done") => (marked = {y \in Nodes : \E x \in Nodes : y \in ConnectedToSomeButNotAll[x]})

Termination == (pc = "running") ~> (pc = "done")

====