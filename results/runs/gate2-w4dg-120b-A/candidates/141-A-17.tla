---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

\* Reachable(n) computes the set of nodes reachable from n by following Succ.
RECURSIVE Reachable(_)
Reachable(n) ==
  LET rg == {n} \cup (IF n \in Nodes THEN Reachable(Succ[n]) ELSE {})
  IN rg

VARIABLES visited, frontier, pc
vars == << visited, frontier, pc >>

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "loop"

\* The main action is chosen nondeterministically from the frontier, with two
\* cases: an unmarked node is marked and its successors are added to the
\* frontier (the node stays in the frontier); an already-marked node is removed.
Explore(n) ==
  /\ n \in frontier
  /\ IF n \notin visited
       THEN /\ visited' = visited \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ visited' = visited
            /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Terminate ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED << visited, frontier >>

Next ==
  \/ \E n \in Seq : Explore(n)
  \/ Terminate

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"loop", "done"}

\* Every successor of a visited node is either visited or still in the frontier.
Inv1 ==
  \A n \in visited : Succ[n] \subseteq (visited \cup frontier)

\* The union of what has been visited and what is reachable from the frontier
\* equals what is reachable from the visited/frontier union.
Inv2 ==
  visited \cup Reachable(frontier) = Reachable(visited \cup frontier)

\* What is reachable from the root is exactly the visited set plus what is
\* reachable from the frontier.
Inv3 ==
  Reachable(Root) = visited \cup Reachable(frontier)

PartialCorrectness ==
  /\ pc = "done"
  /\ visited = Reachable(Root)

Termination ==
  \A n \in Seq : TRUE
  /\ \A n \in Nodes : TRUE
  /\ \A n \in frontier : TRUE
  /\ \A n \in visited : TRUE
  /\ \A f \in Reachable(frontier) : TRUE
  /\ \A g \in Succ[n] : TRUE
  /\ \A h \in Seq : TRUE
  /\ WF_vars([\E n \in Seq : Explore(n)])
  /\ pc = "done"
====