---- MODULE Reachable ----
EXTENDS Integers, FiniteSets, Sequences

\* The algorithm is Misra's variant of BFS: frontier and visited may overlap.
CONSTANTS Nodes, Root, Succ

VARIABLES visited, frontier, pc
vars == <<visited, frontier, pc>>

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "run"

\* The main action has two nondeterministic cases depending on whether the
\* chosen frontier node has already been marked.
Step ==
  /\ pc = "run"
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ /\ n \notin visited
          /\ visited' = visited \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in visited
          /\ visited' = visited
          /\ frontier' = frontier \ {n}
  /\ pc' = pc

Terminate ==
  /\ pc = "run"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<visited, frontier>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars

\* Successors of a marked node are always accounted for in visited or frontier.
Inv1 == \A n \in visited : Succ[n] \subseteq visited \cup frontier

\* Nodes reachable from visited \cup frontier are exactly those reachable from
\* visited plus those reachable from frontier.
Inv2 ==
  (\A x \in visited \cup frontier : \A y \in Nodes : (x \in visited \/ x \in frontier) => (y \in reachableFrom(x) => y \in reachableFrom(visited \cup frontier)))

\* The reachable set from the root is partitioned into visited and frontier.
Inv3 ==
  reachableFrom(Root) = visited \cup reachableFrom(frontier)

PartialCorrectness == (pc = "done") => (visited = reachableFrom(Root))

\* Reachable-from is taken from the standard library; the action needs it.
reachableFrom(X) == {y \in Nodes : \E x \in X : y \in reachableFrom(x)}

\* Fairness: the loop cannot run forever without changing something.
WF_vars(Step)

Termination == (frontier # {}) ~> (frontier = {})

\* The .cfg overrides Succ with ConnectedToSomeButNotAll and Seq with
\* LimitedSeq, so these are defined here but never named directly.
ConnectedToSomeButNotAll(n) == Succ[n]
LimitedSeq(n, ...) == Seq(n, ...)

====