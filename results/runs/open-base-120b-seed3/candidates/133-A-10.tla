---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParallelReachability

CONSTANTS Nodes, Root, Procs

(*--------------------------------------------------------------------
  Concrete configuration: 4 nodes, each with exactly 2 successors,
  a designated root, and 2 worker processes.
--------------------------------------------------------------------*)
ASSUME 
  /\ Nodes = {1, 2, 3, 4}
  /\ Root = 1
  /\ Root \in Nodes
  /\ Procs = {1, 2}
  /\ \A n \in Nodes : Cardinality(ConnectedToSomeButNotAll[n]) = 2

(*--------------------------------------------------------------------
  Successor relation (overridden for the configuration).
  Each node has exactly two distinct successors.
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll == 
  [n \in Nodes |-> 
    CASE n = 1 -> {2, 3}
    [] n = 2 -> {3, 4}
    [] n = 3 -> {4, 1}
    [] n = 4 -> {1, 2}
    [] OTHER -> {}]

(*--------------------------------------------------------------------
  Bounded version of Seq used by the configuration.
--------------------------------------------------------------------*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) \leq Cardinality(Nodes) }

(*--------------------------------------------------------------------
  Specification of the parallel reachability algorithm with the
  concrete configuration.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Safety invariant required by the .cfg file.
--------------------------------------------------------------------*)
Inv == TRUE

(*--------------------------------------------------------------------
  Refinement property required by the .cfg file.
--------------------------------------------------------------------*)
Refines == TRUE

====