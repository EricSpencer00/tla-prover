---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

\* Model-checking configuration for the Misra reachability algorithm.  It
\* provides concrete definitions for the graph and a bounded sequence
\* operator, so the default infinite domain from Sequences is replaced by
\* the finite operator defined here.
CONSTANTS
  Nodes, Root, Succ

VARIABLES
  marked, frontier, pc

vars == << marked, frontier, pc >>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "active"

\* Inherited from the algorithm: explore the frontier.
Step(x) ==
  /\ pc = "active"
  /\ x \in frontier
  /\ frontier' = (frontier \ {x}) \cup (Succ[x] \ marked)
  /\ marked' = marked \cup Succ[x]
  /\ UNCHANGED pc

Complete ==
  /\ pc = "active"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED << marked, frontier >>

Next == (\E x \in Nodes : Step(x)) \/ Complete

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"active", "done"}

\* The successors of the frontier are already marked.
Inv1 ==
  \A x \in frontier : Succ[x] \subseteq marked

\* The marked set is exactly the frontier plus the successors of the frontier.
Inv2 ==
  marked = frontier \cup (\E x \in frontier : Succ[x])

\* Anything reachable from the frontier is already marked.
Inv3 ==
  \A x \in frontier : \A y \in Succ[x] : y \in marked

PartialCorrectness ==
  \A x \in Nodes : frontier = {} => marked = x

\* Termination: the algorithm always completes.
Termination ==
  <>(pc = "done")

\* The graph is fully connected but non-deterministic: each node has exactly
\* two successors, chosen so that every node participates in reachability.
ConnectedToSomeButNotAll ==
  \A x \in Nodes : Cardinality(Succ[x]) = 2

\* The reachability definition from the algorithm uses existential
\* quantification over sequences (paths).  The default Seq operator from the
\* Sequences module is infinite; replace it with a bounded, checkable version.
LimitedSeq ==
  { s \in Seq(Nodes) : Len(s) =< Cardinality(Nodes) }

====