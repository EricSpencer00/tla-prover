---- MODULE MCParReach ----
EXTENDS Sequences, Naturals, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(*--- Concrete successor relation used for model checking ---*)
ConnectedToSomeButNotAll(n) ==
  CASE n = 0 -> {1, 2}
  []  n = 1 -> {2, 3}
  []  n = 2 -> {3, 0}
  []  n = 3 -> {0, 1}
  []  OTHER -> {}

(*--- Bounded version of sequences (length ≤ |Nodes|) ---*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*--- Specification (inherits Init, Next, vars from ParReach) ---*)
Spec == Init /\ [][Next]_vars

(*--- Invariant (inherits the invariant from the parallel algorithm) ---*)
Inv == ParReach!Inv

(*--- Refinement property (inherits the refinement check from the parallel algorithm) ---*)
Refines == ParReach!Refines

====