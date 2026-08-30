---- MODULE Reachable ----
EXTENDS Naturals, Sequences

\* Misra's BFS variant keeps the visited and frontier sets overlapping, which
\* is what enables the relaxed parallelization discussed in the companion
\* module; the invariant suite is exactly what pins the result down to
\* reachability despite that overlap.

CONSTANT Nodes, Root, Succ

VARIABLES visited, frontier, pc

vars == << visited, frontier, pc >>

Init ==
    /\ visited = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Nondeterministic choice of the frontier member to act on; overlapping
\* visited/frontier is handled by the two cases below.
Explore(n) ==
    /\ n \in frontier
    /\ visited' = IF n \in visited THEN visited ELSE visited \cup {n}
    /\ frontier' = IF n \in visited
         THEN frontier \ {n}
         ELSE frontier \cup Succ[n]
    /\ pc' = IF (frontier \cup Succ[n]) \ {n} = {} THEN "done" ELSE "running"

Next == \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

TypeOK == /\ visited \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"running", "done"}

\* Every successor of a visited node is already accounted for: in the visited
\* set or still waiting in the frontier.
Inv1 == \A n \in visited : Succ[n] \subseteq (visited \cup frontier)

\* The marked set plus the frontier's future both cover exactly the nodes
\* reachable from the current combined pool -- no reachable node is lost.
Inv2 == (visited \cup frontier) \cup ReachableFrom(frontier) = ReachableFrom(visited \cup frontier)

\* Once the algorithm has terminated, its visited set is exactly the reachable
\* set -- nothing more, nothing less.
Inv3 == pc = "done" => visited = ReachableFrom({Root})

PartialCorrectness == visited = ReachableFrom({Root})

\* Termination only holds in the finite case; the fairness of Next is what
\* forces the frontier to actually drain rather than churn forever.
Termination == \A n \in Nodes : WeakFairness(vars, Explore(n))

\* By construction the model checks this against ReachableFrom({Root}) and
\* Fail: it is not a definition to be overridden, only a placeholder for the
\* cfg's substitution of a finite bounded version of Succ.
ConnectedToSomeButNotAll == FALSE

\* Hand-rolled finite version of Seq for cfg substitution -- the operator name
\* on the left must NOT be declared here, only the right side.
LimitedSeq == (n \in Nat) |-> IF n \in Nat THEN n ELSE 0

====