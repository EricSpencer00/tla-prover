---- MODULE MCParReach ----
EXTENDS Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(*-----------------------------------------------------------------
  Concrete successor relation used for model checking.
  The .cfg substitutes Succ with this operator.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
       [] n = 2 -> {3, 4}
       [] n = 3 -> {4, 1}
       [] n = 4 -> {1, 2}
       [] OTHER -> {}

(*-----------------------------------------------------------------
  Bounded version of Seq for finite-state checking.
  The .cfg substitutes Seq with this operator.
-----------------------------------------------------------------*)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  Specification of the parallel reachability algorithm.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Inductive invariant (type correctness + control‑flow properties).
-----------------------------------------------------------------*)
Inv == ParReach!Inv

(*-----------------------------------------------------------------
  Refinement property: parallel algorithm implements the sequential
  Misra algorithm.
-----------------------------------------------------------------*)
Refines == ParReach!Refines

====